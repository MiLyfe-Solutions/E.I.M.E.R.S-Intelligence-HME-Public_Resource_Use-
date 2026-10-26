import V185TrunkScan23Chunk0890

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5273687 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 1, 5]
def baseStart_5273687 : Nat := 118140960795 + 5273687 * 2 ^ 59
def prefixEnd_5273687 : Nat := 4983230072969 + 3 ^ 40 * 5273687 * 2
def baseEnd_5273687 : Nat := 902645417455871136353087

theorem tailTrace_5273687 : CollatzResearch.WordTrace tailWord_5273687 prefixEnd_5273687 902645417455871136353087 := by
  unfold tailWord_5273687
  simp only [CollatzResearch.WordTrace]
  refine ⟨192347166845340147878387315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128231444563560098585591543 192347166845340147878387315)
  ·
    refine ⟨288520750268010221817580973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192347166845340147878387315 288520750268010221817580973)
    ·
      refine ⟨108195281350503833181592865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288520750268010221817580973 108195281350503833181592865)
      ·
        refine ⟨81146461012877874886194649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108195281350503833181592865 81146461012877874886194649)
        ·
          refine ⟨60859845759658406164645987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81146461012877874886194649 60859845759658406164645987)
          ·
            refine ⟨91289768639487609246968981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60859845759658406164645987 91289768639487609246968981)
            ·
              refine ⟨4279207904975981683451671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91289768639487609246968981 4279207904975981683451671)
              ·
                refine ⟨6418811857463972525177507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4279207904975981683451671 6418811857463972525177507)
                ·
                  refine ⟨9628217786195958787766261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418811857463972525177507 9628217786195958787766261)
                  ·
                    refine ⟨902645417455871136353087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9628217786195958787766261 902645417455871136353087)
                    ·
                      rfl

theorem cell23_5273687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_5273687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273687 prefixEnd_5273687 := by exact prefixLift 5273687
  have htrace : WordTrace (prefixWord ++ tailWord_5273687) baseStart_5273687 baseEnd_5273687 := by
    simpa [prefixWord, tailWord_5273687, baseEnd_5273687] using wordTrace_append hprefix tailTrace_5273687
  have hstable : (prefixWord ++ tailWord_5273687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273687).length < 2 ^ (prefixWord ++ tailWord_5273687).sum := by decide
  have hdescent : baseEnd_5273687 < baseStart_5273687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273713 : List Nat := [1, 2, 2, 2, 1, 1, 4, 10]
def baseStart_5273713 : Nat := 118140960795 + 5273713 * 2 ^ 59
def prefixEnd_5273713 : Nat := 4983230072969 + 3 ^ 40 * 5273713 * 2
def baseEnd_5273713 : Nat := 100294429735727048419783

theorem tailTrace_5273713 : CollatzResearch.WordTrace tailWord_5273713 prefixEnd_5273713 100294429735727048419783 := by
  unfold tailWord_5273713
  simp only [CollatzResearch.WordTrace]
  refine ⟨192348115143245954318833793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128232076762163969545889195 192348115143245954318833793)
  ·
    refine ⟨144261086357434465739125345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192348115143245954318833793 144261086357434465739125345)
    ·
      refine ⟨108195814768075849304344009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144261086357434465739125345 108195814768075849304344009)
      ·
        refine ⟨81146861076056886978258007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108195814768075849304344009 81146861076056886978258007)
        ·
          refine ⟨121720291614085330467387011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81146861076056886978258007 121720291614085330467387011)
          ·
            refine ⟨182580437421127995701080517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121720291614085330467387011 182580437421127995701080517)
            ·
              refine ⟨34233832016461499193952597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182580437421127995701080517 34233832016461499193952597)
              ·
                refine ⟨100294429735727048419783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34233832016461499193952597 100294429735727048419783)
                ·
                  rfl

theorem cell23_5273713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 10].length) (baseStart_5273713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273713 prefixEnd_5273713 := by exact prefixLift 5273713
  have htrace : WordTrace (prefixWord ++ tailWord_5273713) baseStart_5273713 baseEnd_5273713 := by
    simpa [prefixWord, tailWord_5273713, baseEnd_5273713] using wordTrace_append hprefix tailTrace_5273713
  have hstable : (prefixWord ++ tailWord_5273713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273713).length < 2 ^ (prefixWord ++ tailWord_5273713).sum := by decide
  have hdescent : baseEnd_5273713 < baseStart_5273713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273724 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_5273724 : Nat := 118140960795 + 5273724 * 2 ^ 59
def prefixEnd_5273724 : Nat := 4983230072969 + 3 ^ 40 * 5273724 * 2
def baseEnd_5273724 : Nat := 2707955251151829764296591

theorem tailTrace_5273724 : CollatzResearch.WordTrace tailWord_5273724 prefixEnd_5273724 2707955251151829764296591 := by
  unfold tailWord_5273724
  simp only [CollatzResearch.WordTrace]
  refine ⟨96174258173103051598742113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128232344230804068798322817 96174258173103051598742113)
  ·
    refine ⟨72130693629827288699056585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96174258173103051598742113 72130693629827288699056585)
    ·
      refine ⟨54098020222370466524292439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72130693629827288699056585 54098020222370466524292439)
      ·
        refine ⟨81147030333555699786438659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54098020222370466524292439 81147030333555699786438659)
        ·
          refine ⟨121720545500333549679657989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81147030333555699786438659 121720545500333549679657989)
          ·
            refine ⟨22822602281312540564935873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121720545500333549679657989 22822602281312540564935873)
            ·
              refine ⟨17116951710984405423701905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22822602281312540564935873 17116951710984405423701905)
              ·
                refine ⟨12837713783238304067776429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17116951710984405423701905 12837713783238304067776429)
                ·
                  refine ⟨4814142668714364025416161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12837713783238304067776429 4814142668714364025416161)
                  ·
                    refine ⟨3610607001535773019062121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4814142668714364025416161 3610607001535773019062121)
                    ·
                      refine ⟨2707955251151829764296591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610607001535773019062121 2707955251151829764296591)
                      ·
                        rfl

theorem cell23_5273724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_5273724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273724 prefixEnd_5273724 := by exact prefixLift 5273724
  have htrace : WordTrace (prefixWord ++ tailWord_5273724) baseStart_5273724 baseEnd_5273724 := by
    simpa [prefixWord, tailWord_5273724, baseEnd_5273724] using wordTrace_append hprefix tailTrace_5273724
  have hstable : (prefixWord ++ tailWord_5273724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273724).length < 2 ^ (prefixWord ++ tailWord_5273724).sum := by decide
  have hdescent : baseEnd_5273724 < baseStart_5273724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273797 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_5273797 : Nat := 118140960795 + 5273797 * 2 ^ 59
def prefixEnd_5273797 : Nat := 4983230072969 + 3 ^ 40 * 5273797 * 2
def baseEnd_5273797 : Nat := 2707992735239607978683755

theorem tailTrace_5273797 : CollatzResearch.WordTrace tailWord_5273797 prefixEnd_5273797 2707992735239607978683755 := by
  unfold tailWord_5273797
  simp only [CollatzResearch.WordTrace]
  refine ⟨192351178874941636664891645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128234119249961091109927763 192351178874941636664891645)
  ·
    refine ⟨72131692078103113749334367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192351178874941636664891645 72131692078103113749334367)
    ·
      refine ⟨108197538117154670624001551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72131692078103113749334367 108197538117154670624001551)
      ·
        refine ⟨162296307175732005936002327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108197538117154670624001551 162296307175732005936002327)
        ·
          refine ⟨243444460763598008904003491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162296307175732005936002327 243444460763598008904003491)
          ·
            refine ⟨365166691145397013356005237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243444460763598008904003491 365166691145397013356005237)
            ·
              refine ⟨34234377294880970002125491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365166691145397013356005237 34234377294880970002125491)
              ·
                refine ⟨51351565942321455003188237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34234377294880970002125491 51351565942321455003188237)
                ·
                  refine ⟨19256837228370545626195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51351565942321455003188237 19256837228370545626195589)
                  ·
                    refine ⟨3610656980319477304911673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19256837228370545626195589 3610656980319477304911673)
                    ·
                      refine ⟨2707992735239607978683755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610656980319477304911673 2707992735239607978683755)
                      ·
                        rfl

theorem cell23_5273797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_5273797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273797 prefixEnd_5273797 := by exact prefixLift 5273797
  have htrace : WordTrace (prefixWord ++ tailWord_5273797) baseStart_5273797 baseEnd_5273797 := by
    simpa [prefixWord, tailWord_5273797, baseEnd_5273797] using wordTrace_append hprefix tailTrace_5273797
  have hstable : (prefixWord ++ tailWord_5273797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273797).length < 2 ^ (prefixWord ++ tailWord_5273797).sum := by decide
  have hdescent : baseEnd_5273797 < baseStart_5273797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273814 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5273814 : Nat := 118140960795 + 5273814 * 2 ^ 59
def prefixEnd_5273814 : Nat := 4983230072969 + 3 ^ 40 * 5273814 * 2
def baseEnd_5273814 : Nat := 2708001464410734412171177

theorem tailTrace_5273814 : CollatzResearch.WordTrace tailWord_5273814 prefixEnd_5273814 2708001464410734412171177 := by
  unfold tailWord_5273814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021987432242503035516281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128234532610586699045506997 12021987432242503035516281)
  ·
    refine ⟨9016490574181877276637211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12021987432242503035516281 9016490574181877276637211)
    ·
      refine ⟨13524735861272815914955817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016490574181877276637211 13524735861272815914955817)
      ·
        refine ⟨10143551895954611936216863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13524735861272815914955817 10143551895954611936216863)
        ·
          refine ⟨15215327843931917904325295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143551895954611936216863 15215327843931917904325295)
          ·
            refine ⟨22822991765897876856487943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215327843931917904325295 22822991765897876856487943)
            ·
              refine ⟨34234487648846815284731915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22822991765897876856487943 34234487648846815284731915)
              ·
                refine ⟨51351731473270222927097873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34234487648846815284731915 51351731473270222927097873)
                ·
                  refine ⟨38513798604952667195323405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51351731473270222927097873 38513798604952667195323405)
                  ·
                    refine ⟨14442674476857250198246277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38513798604952667195323405 14442674476857250198246277)
                    ·
                      refine ⟨2708001464410734412171177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14442674476857250198246277 2708001464410734412171177)
                      ·
                        rfl

theorem cell23_5273814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5273814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273814 prefixEnd_5273814 := by exact prefixLift 5273814
  have htrace : WordTrace (prefixWord ++ tailWord_5273814) baseStart_5273814 baseEnd_5273814 := by
    simpa [prefixWord, tailWord_5273814, baseEnd_5273814] using wordTrace_append hprefix tailTrace_5273814
  have hstable : (prefixWord ++ tailWord_5273814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273814).length < 2 ^ (prefixWord ++ tailWord_5273814).sum := by decide
  have hdescent : baseEnd_5273814 < baseStart_5273814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273831 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5273831 : Nat := 118140960795 + 5273831 * 2 ^ 59
def prefixEnd_5273831 : Nat := 4983230072969 + 3 ^ 40 * 5273831 * 2
def baseEnd_5273831 : Nat := 2708010193581860845658599

theorem tailTrace_5273831 : CollatzResearch.WordTrace tailWord_5273831 prefixEnd_5273831 2708010193581860845658599 := by
  unfold tailWord_5273831
  simp only [CollatzResearch.WordTrace]
  refine ⟨192352418956818460471629347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128234945971212306981086231 192352418956818460471629347)
  ·
    refine ⟨288528628435227690707444021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192352418956818460471629347 288528628435227690707444021)
    ·
      refine ⟨27049558915802596003822877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288528628435227690707444021 27049558915802596003822877)
      ·
        refine ⟨10143584593425973501433579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27049558915802596003822877 10143584593425973501433579)
        ·
          refine ⟨15215376890138960252150369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143584593425973501433579 15215376890138960252150369)
          ·
            refine ⟨11411532667604220189112777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15215376890138960252150369 11411532667604220189112777)
            ·
              refine ⟨8558649500703165141834583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11411532667604220189112777 8558649500703165141834583)
              ·
                refine ⟨12837974251054747712751875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8558649500703165141834583 12837974251054747712751875)
                ·
                  refine ⟨19256961376582121569127813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12837974251054747712751875 19256961376582121569127813)
                  ·
                    refine ⟨3610680258109147794211465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19256961376582121569127813 3610680258109147794211465)
                    ·
                      refine ⟨2708010193581860845658599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610680258109147794211465 2708010193581860845658599)
                      ·
                        rfl

theorem cell23_5273831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5273831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273831 prefixEnd_5273831 := by exact prefixLift 5273831
  have htrace : WordTrace (prefixWord ++ tailWord_5273831) baseStart_5273831 baseEnd_5273831 := by
    simpa [prefixWord, tailWord_5273831, baseEnd_5273831] using wordTrace_append hprefix tailTrace_5273831
  have hstable : (prefixWord ++ tailWord_5273831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273831).length < 2 ^ (prefixWord ++ tailWord_5273831).sum := by decide
  have hdescent : baseEnd_5273831 < baseStart_5273831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273887 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5273887 : Nat := 118140960795 + 5273887 * 2 ^ 59
def prefixEnd_5273887 : Nat := 4983230072969 + 3 ^ 40 * 5273887 * 2
def baseEnd_5273887 : Nat := 2708038948498512626558341

theorem tailTrace_5273887 : CollatzResearch.WordTrace tailWord_5273887 prefixEnd_5273887 2708038948498512626558341 := by
  unfold tailWord_5273887
  simp only [CollatzResearch.WordTrace]
  refine ⟨192354461444615582035667915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128236307629743721357111943 192354461444615582035667915)
  ·
    refine ⟨288531692166923373053501873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192354461444615582035667915 288531692166923373053501873)
    ·
      refine ⟨216398769125192529790126405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288531692166923373053501873 216398769125192529790126405)
      ·
        refine ⟨40574769210973599335648701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216398769125192529790126405 40574769210973599335648701)
        ·
          refine ⟨15215538454115099750868263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40574769210973599335648701 15215538454115099750868263)
          ·
            refine ⟨22823307681172649626302395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215538454115099750868263 22823307681172649626302395)
            ·
              refine ⟨34234961521758974439453593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22823307681172649626302395 34234961521758974439453593)
              ·
                refine ⟨25676221141319230829590195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34234961521758974439453593 25676221141319230829590195)
                ·
                  refine ⟨38514331711978846244385293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25676221141319230829590195 38514331711978846244385293)
                  ·
                    refine ⟨14442874391992067341644485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38514331711978846244385293 14442874391992067341644485)
                    ·
                      refine ⟨2708038948498512626558341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14442874391992067341644485 2708038948498512626558341)
                      ·
                        rfl

theorem cell23_5273887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5273887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273887 prefixEnd_5273887 := by exact prefixLift 5273887
  have htrace : WordTrace (prefixWord ++ tailWord_5273887) baseStart_5273887 baseEnd_5273887 := by
    simpa [prefixWord, tailWord_5273887, baseEnd_5273887] using wordTrace_append hprefix tailTrace_5273887
  have hstable : (prefixWord ++ tailWord_5273887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273887).length < 2 ^ (prefixWord ++ tailWord_5273887).sum := by decide
  have hdescent : baseEnd_5273887 < baseStart_5273887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273907 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3]
def baseStart_5273907 : Nat := 118140960795 + 5273907 * 2 ^ 59
def prefixEnd_5273907 : Nat := 4983230072969 + 3 ^ 40 * 5273907 * 2
def baseEnd_5273907 : Nat := 2708049218111602548308249

theorem tailTrace_5273907 : CollatzResearch.WordTrace tailWord_5273907 prefixEnd_5273907 2708049218111602548308249 := by
  unfold tailWord_5273907
  simp only [CollatzResearch.WordTrace]
  refine ⟨192355190904543125451395975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128236793936362083634263983 192355190904543125451395975)
  ·
    refine ⟨288532786356814688177093963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192355190904543125451395975 288532786356814688177093963)
    ·
      refine ⟨432799179535222032265640945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288532786356814688177093963 432799179535222032265640945)
      ·
        refine ⟨324599384651416524199230709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432799179535222032265640945 324599384651416524199230709)
        ·
          refine ⟨30431192311070299143677879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 324599384651416524199230709 30431192311070299143677879)
          ·
            refine ⟨45646788466605448715516819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30431192311070299143677879 45646788466605448715516819)
            ·
              refine ⟨68470182699908173073275229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45646788466605448715516819 68470182699908173073275229)
              ·
                refine ⟨25676318512465564902478211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68470182699908173073275229 25676318512465564902478211)
                ·
                  refine ⟨38514477768698347353717317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25676318512465564902478211 38514477768698347353717317)
                  ·
                    refine ⟨7221464581630940128821997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38514477768698347353717317 7221464581630940128821997)
                    ·
                      refine ⟨2708049218111602548308249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221464581630940128821997 2708049218111602548308249)
                      ·
                        rfl

theorem cell23_5273907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_5273907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273907 prefixEnd_5273907 := by exact prefixLift 5273907
  have htrace : WordTrace (prefixWord ++ tailWord_5273907) baseStart_5273907 baseEnd_5273907 := by
    simpa [prefixWord, tailWord_5273907, baseEnd_5273907] using wordTrace_append hprefix tailTrace_5273907
  have hstable : (prefixWord ++ tailWord_5273907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273907).length < 2 ^ (prefixWord ++ tailWord_5273907).sum := by decide
  have hdescent : baseEnd_5273907 < baseStart_5273907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273921 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5273921 : Nat := 118140960795 + 5273921 * 2 ^ 59
def prefixEnd_5273921 : Nat := 4983230072969 + 3 ^ 40 * 5273921 * 2
def baseEnd_5273921 : Nat := 2708056406840765493533185

theorem tailTrace_5273921 : CollatzResearch.WordTrace tailWord_5273921 prefixEnd_5273921 2708056406840765493533185 := by
  unfold tailWord_5273921
  simp only [CollatzResearch.WordTrace]
  refine ⟨192355701526492405842405617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128237134350994937228270411 192355701526492405842405617)
  ·
    refine ⟨144266776144869304381804213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192355701526492405842405617 144266776144869304381804213)
    ·
      refine ⟨13525010263581497285794145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144266776144869304381804213 13525010263581497285794145)
      ·
        refine ⟨10143757697686122964345609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13525010263581497285794145 10143757697686122964345609)
        ·
          refine ⟨7607818273264592223259207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143757697686122964345609 7607818273264592223259207)
          ·
            refine ⟨11411727409896888334888811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607818273264592223259207 11411727409896888334888811)
            ·
              refine ⟨17117591114845332502333217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11411727409896888334888811 17117591114845332502333217)
              ·
                refine ⟨12838193336133999376749913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17117591114845332502333217 12838193336133999376749913)
                ·
                  refine ⟨9628645002100499532562435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12838193336133999376749913 9628645002100499532562435)
                  ·
                    refine ⟨14442967503150749298843653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9628645002100499532562435 14442967503150749298843653)
                    ·
                      refine ⟨2708056406840765493533185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14442967503150749298843653 2708056406840765493533185)
                      ·
                        rfl

theorem cell23_5273921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5273921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273921 prefixEnd_5273921 := by exact prefixLift 5273921
  have htrace : WordTrace (prefixWord ++ tailWord_5273921) baseStart_5273921 baseEnd_5273921 := by
    simpa [prefixWord, tailWord_5273921, baseEnd_5273921] using wordTrace_append hprefix tailTrace_5273921
  have hstable : (prefixWord ++ tailWord_5273921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273921).length < 2 ^ (prefixWord ++ tailWord_5273921).sum := by decide
  have hdescent : baseEnd_5273921 < baseStart_5273921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273927 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 6]
def baseStart_5273927 : Nat := 118140960795 + 5273927 * 2 ^ 59
def prefixEnd_5273927 : Nat := 4983230072969 + 3 ^ 40 * 5273927 * 2
def baseEnd_5273927 : Nat := 300895498636076941117573

theorem tailTrace_5273927 : CollatzResearch.WordTrace tailWord_5273927 prefixEnd_5273927 300895498636076941117573 := by
  unfold tailWord_5273927
  simp only [CollatzResearch.WordTrace]
  refine ⟨192355920364470668867124035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128237280242980445911416023 192355920364470668867124035)
  ·
    refine ⟨288533880546706003300686053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192355920364470668867124035 288533880546706003300686053)
    ·
      refine ⟨54100102602507375618878635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288533880546706003300686053 54100102602507375618878635)
      ·
        refine ⟨81150153903761063428317953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54100102602507375618878635 81150153903761063428317953)
        ·
          refine ⟨60862615427820797571238465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81150153903761063428317953 60862615427820797571238465)
          ·
            refine ⟨45646961570865598178428849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60862615427820797571238465 45646961570865598178428849)
            ·
              refine ⟨34235221178149198633821637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45646961570865598178428849 34235221178149198633821637)
              ·
                refine ⟨6419103970902974743841557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34235221178149198633821637 6419103970902974743841557)
                ·
                  refine ⟨300895498636076941117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6419103970902974743841557 300895498636076941117573)
                  ·
                    rfl

theorem cell23_5273927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 6].length) (baseStart_5273927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273927 prefixEnd_5273927 := by exact prefixLift 5273927
  have htrace : WordTrace (prefixWord ++ tailWord_5273927) baseStart_5273927 baseEnd_5273927 := by
    simpa [prefixWord, tailWord_5273927, baseEnd_5273927] using wordTrace_append hprefix tailTrace_5273927
  have hstable : (prefixWord ++ tailWord_5273927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273927).length < 2 ^ (prefixWord ++ tailWord_5273927).sum := by decide
  have hdescent : baseEnd_5273927 < baseStart_5273927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273981 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_5273981 : Nat := 118140960795 + 5273981 * 2 ^ 59
def prefixEnd_5273981 : Nat := 4983230072969 + 3 ^ 40 * 5273981 * 2
def baseEnd_5273981 : Nat := 2708087215680035258782909

theorem tailTrace_5273981 : CollatzResearch.WordTrace tailWord_5273981 prefixEnd_5273981 2708087215680035258782909 := by
  unfold tailWord_5273981
  simp only [CollatzResearch.WordTrace]
  refine ⟨192357889906275036089589797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128238593270850024059726531 192357889906275036089589797)
  ·
    refine ⟨36067104357426569266798087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192357889906275036089589797 36067104357426569266798087)
    ·
      refine ⟨54100656536139853900197131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36067104357426569266798087 54100656536139853900197131)
      ·
        refine ⟨81150984804209780850295697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54100656536139853900197131 81150984804209780850295697)
        ·
          refine ⟨60863238603157335637721773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81150984804209780850295697 60863238603157335637721773)
          ·
            refine ⟨22823714476184000864145665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60863238603157335637721773 22823714476184000864145665)
            ·
              refine ⟨17117785857138000648109249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22823714476184000864145665 17117785857138000648109249)
              ·
                refine ⟨12838339392853500486081937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17117785857138000648109249 12838339392853500486081937)
                ·
                  refine ⟨9628754544640125364561453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12838339392853500486081937 9628754544640125364561453)
                  ·
                    refine ⟨3610782954240047011710545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9628754544640125364561453 3610782954240047011710545)
                    ·
                      refine ⟨2708087215680035258782909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610782954240047011710545 2708087215680035258782909)
                      ·
                        rfl

theorem cell23_5273981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_5273981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273981 prefixEnd_5273981 := by exact prefixLift 5273981
  have htrace : WordTrace (prefixWord ++ tailWord_5273981) baseStart_5273981 baseEnd_5273981 := by
    simpa [prefixWord, tailWord_5273981, baseEnd_5273981] using wordTrace_append hprefix tailTrace_5273981
  have hstable : (prefixWord ++ tailWord_5273981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273981).length < 2 ^ (prefixWord ++ tailWord_5273981).sum := by decide
  have hdescent : baseEnd_5273981 < baseStart_5273981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273988 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_5273988 : Nat := 118140960795 + 5273988 * 2 ^ 59
def prefixEnd_5273988 : Nat := 4983230072969 + 3 ^ 40 * 5273988 * 2
def baseEnd_5273988 : Nat := 2708090810044616731395377

theorem tailTrace_5273988 : CollatzResearch.WordTrace tailWord_5273988 prefixEnd_5273988 2708090810044616731395377 := by
  unfold tailWord_5273988
  simp only [CollatzResearch.WordTrace]
  refine ⟨96179072608624838142547309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128238763478166450856729745 96179072608624838142547309)
  ·
    refine ⟨36067152228234314303455241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96179072608624838142547309 36067152228234314303455241)
    ·
      refine ⟨27050364171175735727591431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36067152228234314303455241 27050364171175735727591431)
      ·
        refine ⟨40575546256763603591387147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050364171175735727591431 40575546256763603591387147)
        ·
          refine ⟨60863319385145405387080721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40575546256763603591387147 60863319385145405387080721)
          ·
            refine ⟨45647489538859054040310541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60863319385145405387080721 45647489538859054040310541)
            ·
              refine ⟨17117808577072145265116453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45647489538859054040310541 17117808577072145265116453)
              ·
                refine ⟨3209589108201027237209335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17117808577072145265116453 3209589108201027237209335)
                ·
                  refine ⟨4814383662301540855814003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209589108201027237209335 4814383662301540855814003)
                  ·
                    refine ⟨7221575493452311283721005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4814383662301540855814003 7221575493452311283721005)
                    ·
                      refine ⟨2708090810044616731395377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221575493452311283721005 2708090810044616731395377)
                      ·
                        rfl

theorem cell23_5273988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_5273988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273988 prefixEnd_5273988 := by exact prefixLift 5273988
  have htrace : WordTrace (prefixWord ++ tailWord_5273988) baseStart_5273988 baseEnd_5273988 := by
    simpa [prefixWord, tailWord_5273988, baseEnd_5273988] using wordTrace_append hprefix tailTrace_5273988
  have hstable : (prefixWord ++ tailWord_5273988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273988).length < 2 ^ (prefixWord ++ tailWord_5273988).sum := by decide
  have hdescent : baseEnd_5273988 < baseStart_5273988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274007 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5274007 : Nat := 118140960795 + 5274007 * 2 ^ 59
def prefixEnd_5274007 : Nat := 4983230072969 + 3 ^ 40 * 5274007 * 2
def baseEnd_5274007 : Nat := 2708100566177052157057789

theorem tailTrace_5274007 : CollatzResearch.WordTrace tailWord_5274007 prefixEnd_5274007 2708100566177052157057789 := by
  unfold tailWord_5274007
  simp only [CollatzResearch.WordTrace]
  refine ⟨192358838204180842530036275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128239225469453895020024183 192358838204180842530036275)
  ·
    refine ⟨288538257306271263795054413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192358838204180842530036275 288538257306271263795054413)
    ·
      refine ⟨108201846489851723923145405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288538257306271263795054413 108201846489851723923145405)
      ·
        refine ⟨40575692433694396471179527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108201846489851723923145405 40575692433694396471179527)
        ·
          refine ⟨60863538650541594706769291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40575692433694396471179527 60863538650541594706769291)
          ·
            refine ⟨91295307975812392060153937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60863538650541594706769291 91295307975812392060153937)
            ·
              refine ⟨68471480981859294045115453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91295307975812392060153937 68471480981859294045115453)
              ·
                refine ⟨25676805368197235266918295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68471480981859294045115453 25676805368197235266918295)
                ·
                  refine ⟨38515208052295852900377443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25676805368197235266918295 38515208052295852900377443)
                  ·
                    refine ⟨57772812078443779350566165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38515208052295852900377443 57772812078443779350566165)
                    ·
                      refine ⟨2708100566177052157057789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57772812078443779350566165 2708100566177052157057789)
                      ·
                        rfl

theorem cell23_5274007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5274007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274007 prefixEnd_5274007 := by exact prefixLift 5274007
  have htrace : WordTrace (prefixWord ++ tailWord_5274007) baseStart_5274007 baseEnd_5274007 := by
    simpa [prefixWord, tailWord_5274007, baseEnd_5274007] using wordTrace_append hprefix tailTrace_5274007
  have hstable : (prefixWord ++ tailWord_5274007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274007).length < 2 ^ (prefixWord ++ tailWord_5274007).sum := by decide
  have hdescent : baseEnd_5274007 < baseStart_5274007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274045 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_5274045 : Nat := 118140960795 + 5274045 * 2 ^ 59
def prefixEnd_5274045 : Nat := 4983230072969 + 3 ^ 40 * 5274045 * 2
def baseEnd_5274045 : Nat := 2708120078441923008382615

theorem tailTrace_5274045 : CollatzResearch.WordTrace tailWord_5274045 prefixEnd_5274045 2708120078441923008382615 := by
  unfold tailWord_5274045
  simp only [CollatzResearch.WordTrace]
  refine ⟨192360224178043175019919589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128240149452028783346613059 192360224178043175019919589)
  ·
    refine ⟨36067542033383095316234923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192360224178043175019919589 36067542033383095316234923)
    ·
      refine ⟨54101313050074642974352385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36067542033383095316234923 54101313050074642974352385)
      ·
        refine ⟨40575984787555982230764289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54101313050074642974352385 40575984787555982230764289)
        ·
          refine ⟨30431988590666986673073217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40575984787555982230764289 30431988590666986673073217)
          ·
            refine ⟨22823991443000240004804913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30431988590666986673073217 22823991443000240004804913)
            ·
              refine ⟨17117993582250180003603685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22823991443000240004804913 17117993582250180003603685)
              ·
                refine ⟨3209623796671908750675691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17117993582250180003603685 3209623796671908750675691)
                ·
                  refine ⟨4814435695007863126013537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209623796671908750675691 4814435695007863126013537)
                  ·
                    refine ⟨3610826771255897344510153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4814435695007863126013537 3610826771255897344510153)
                    ·
                      refine ⟨2708120078441923008382615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610826771255897344510153 2708120078441923008382615)
                      ·
                        rfl

theorem cell23_5274045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_5274045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274045 prefixEnd_5274045 := by exact prefixLift 5274045
  have htrace : WordTrace (prefixWord ++ tailWord_5274045) baseStart_5274045 baseEnd_5274045 := by
    simpa [prefixWord, tailWord_5274045, baseEnd_5274045] using wordTrace_append hprefix tailTrace_5274045
  have hstable : (prefixWord ++ tailWord_5274045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274045).length < 2 ^ (prefixWord ++ tailWord_5274045).sum := by decide
  have hdescent : baseEnd_5274045 < baseStart_5274045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274067 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_5274067 : Nat := 118140960795 + 5274067 * 2 ^ 59
def prefixEnd_5274067 : Nat := 4983230072969 + 3 ^ 40 * 5274067 * 2
def baseEnd_5274067 : Nat := 2708131375016321922307513

theorem tailTrace_5274067 : CollatzResearch.WordTrace tailWord_5274067 prefixEnd_5274067 2708131375016321922307513 := by
  unfold tailWord_5274067
  simp only [CollatzResearch.WordTrace]
  refine ⟨192361026583963472777220455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128240684389308981851480303 192361026583963472777220455)
  ·
    refine ⟨288541539875945209165830683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192361026583963472777220455 288541539875945209165830683)
    ·
      refine ⟨432812309813917813748746025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288541539875945209165830683 432812309813917813748746025)
      ·
        refine ⟨324609232360438360311559519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432812309813917813748746025 324609232360438360311559519)
        ·
          refine ⟨486913848540657540467339279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324609232360438360311559519 486913848540657540467339279)
          ·
            refine ⟨730370772810986310701008919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486913848540657540467339279 730370772810986310701008919)
            ·
              refine ⟨1095556159216479466051513379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730370772810986310701008919 1095556159216479466051513379)
              ·
                refine ⟨1643334238824719199077270069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095556159216479466051513379 1643334238824719199077270069)
                ·
                  refine ⟨154062584889817424913494069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643334238824719199077270069 154062584889817424913494069)
                  ·
                    refine ⟨14443367333420383585640069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154062584889817424913494069 14443367333420383585640069)
                    ·
                      refine ⟨2708131375016321922307513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14443367333420383585640069 2708131375016321922307513)
                      ·
                        rfl

theorem cell23_5274067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_5274067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274067 prefixEnd_5274067 := by exact prefixLift 5274067
  have htrace : WordTrace (prefixWord ++ tailWord_5274067) baseStart_5274067 baseEnd_5274067 := by
    simpa [prefixWord, tailWord_5274067, baseEnd_5274067] using wordTrace_append hprefix tailTrace_5274067
  have hstable : (prefixWord ++ tailWord_5274067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274067).length < 2 ^ (prefixWord ++ tailWord_5274067).sum := by decide
  have hdescent : baseEnd_5274067 < baseStart_5274067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274088 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5274088 : Nat := 118140960795 + 5274088 * 2 ^ 59
def prefixEnd_5274088 : Nat := 4983230072969 + 3 ^ 40 * 5274088 * 2
def baseEnd_5274088 : Nat := 2708142158110066340144917

theorem tailTrace_5274088 : CollatzResearch.WordTrace tailWord_5274088 prefixEnd_5274088 2708142158110066340144917 := by
  unfold tailWord_5274088
  simp only [CollatzResearch.WordTrace]
  refine ⟨96180896258443696681867459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128241195011258262242489945 96180896258443696681867459)
  ·
    refine ⟨144271344387665545022801189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96180896258443696681867459 144271344387665545022801189)
    ·
      refine ⟨27050877072687289691775223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144271344387665545022801189 27050877072687289691775223)
      ·
        refine ⟨40576315609030934537662835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050877072687289691775223 40576315609030934537662835)
        ·
          refine ⟨60864473413546401806494253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40576315609030934537662835 60864473413546401806494253)
          ·
            refine ⟨22824177530079900677435345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60864473413546401806494253 22824177530079900677435345)
            ·
              refine ⟨17118133147559925508076509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22824177530079900677435345 17118133147559925508076509)
              ·
                refine ⟨6419299930334972065528691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17118133147559925508076509 6419299930334972065528691)
                ·
                  refine ⟨9628949895502458098293037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6419299930334972065528691 9628949895502458098293037)
                  ·
                    refine ⟨3610856210813421786859889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9628949895502458098293037 3610856210813421786859889)
                    ·
                      refine ⟨2708142158110066340144917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610856210813421786859889 2708142158110066340144917)
                      ·
                        rfl

theorem cell23_5274088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5274088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274088 prefixEnd_5274088 := by exact prefixLift 5274088
  have htrace : WordTrace (prefixWord ++ tailWord_5274088) baseStart_5274088 baseEnd_5274088 := by
    simpa [prefixWord, tailWord_5274088, baseEnd_5274088] using wordTrace_append hprefix tailTrace_5274088
  have hstable : (prefixWord ++ tailWord_5274088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274088).length < 2 ^ (prefixWord ++ tailWord_5274088).sum := by decide
  have hdescent : baseEnd_5274088 < baseStart_5274088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274104 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_5274104 : Nat := 118140960795 + 5274104 * 2 ^ 59
def prefixEnd_5274104 : Nat := 4983230072969 + 3 ^ 40 * 5274104 * 2
def baseEnd_5274104 : Nat := 2708150373800538277544843

theorem tailTrace_5274104 : CollatzResearch.WordTrace tailWord_5274104 prefixEnd_5274104 2708150373800538277544843 := by
  unfold tailWord_5274104
  simp only [CollatzResearch.WordTrace]
  refine ⟨96181188042414714048158683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128241584056552952064211577 96181188042414714048158683)
  ·
    refine ⟨144271782063622071072238025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96181188042414714048158683 144271782063622071072238025)
    ·
      refine ⟨108203836547716553304178519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144271782063622071072238025 108203836547716553304178519)
      ·
        refine ⟨162305754821574829956267779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108203836547716553304178519 162305754821574829956267779)
        ·
          refine ⟨243458632232362244934401669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162305754821574829956267779 243458632232362244934401669)
          ·
            refine ⟨45648493543567920925200313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243458632232362244934401669 45648493543567920925200313)
            ·
              refine ⟨34236370157675940693900235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45648493543567920925200313 34236370157675940693900235)
              ·
                refine ⟨51354555236513911040850353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34236370157675940693900235 51354555236513911040850353)
                ·
                  refine ⟨38515916427385433280637765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51354555236513911040850353 38515916427385433280637765)
                  ·
                    refine ⟨7221734330134768740119581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38515916427385433280637765 7221734330134768740119581)
                    ·
                      refine ⟨2708150373800538277544843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221734330134768740119581 2708150373800538277544843)
                      ·
                        rfl

theorem cell23_5274104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_5274104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274104 prefixEnd_5274104 := by exact prefixLift 5274104
  have htrace : WordTrace (prefixWord ++ tailWord_5274104) baseStart_5274104 baseEnd_5274104 := by
    simpa [prefixWord, tailWord_5274104, baseEnd_5274104] using wordTrace_append hprefix tailTrace_5274104
  have hstable : (prefixWord ++ tailWord_5274104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274104).length < 2 ^ (prefixWord ++ tailWord_5274104).sum := by decide
  have hdescent : baseEnd_5274104 < baseStart_5274104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274135 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5274135 : Nat := 118140960795 + 5274135 * 2 ^ 59
def prefixEnd_5274135 : Nat := 4983230072969 + 3 ^ 40 * 5274135 * 2
def baseEnd_5274135 : Nat := 2708166291700827656257201

theorem tailTrace_5274135 : CollatzResearch.WordTrace tailWord_5274135 prefixEnd_5274135 2708166291700827656257201 := by
  unfold tailWord_5274135
  simp only [CollatzResearch.WordTrace]
  refine ⟨192363506747717120390695859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128242337831811413593797239 192363506747717120390695859)
  ·
    refine ⟨288545260121575680586043789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192363506747717120390695859 288545260121575680586043789)
    ·
      refine ⟨108204472545590880219766421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288545260121575680586043789 108204472545590880219766421)
      ·
        refine ⟨5072084650574572510301551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108204472545590880219766421 5072084650574572510301551)
        ·
          refine ⟨7608126975861858765452327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072084650574572510301551 7608126975861858765452327)
          ·
            refine ⟨11412190463792788148178491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7608126975861858765452327 11412190463792788148178491)
            ·
              refine ⟨17118285695689182222267737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11412190463792788148178491 17118285695689182222267737)
              ·
                refine ⟨12838714271766886666700803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17118285695689182222267737 12838714271766886666700803)
                ·
                  refine ⟨19258071407650330000051205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12838714271766886666700803 19258071407650330000051205)
                  ·
                    refine ⟨3610888388934436875009601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19258071407650330000051205 3610888388934436875009601)
                    ·
                      refine ⟨2708166291700827656257201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610888388934436875009601 2708166291700827656257201)
                      ·
                        rfl

theorem cell23_5274135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5274135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274135 prefixEnd_5274135 := by exact prefixLift 5274135
  have htrace : WordTrace (prefixWord ++ tailWord_5274135) baseStart_5274135 baseEnd_5274135 := by
    simpa [prefixWord, tailWord_5274135, baseEnd_5274135] using wordTrace_append hprefix tailTrace_5274135
  have hstable : (prefixWord ++ tailWord_5274135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274135).length < 2 ^ (prefixWord ++ tailWord_5274135).sum := by decide
  have hdescent : baseEnd_5274135 < baseStart_5274135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274152 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5274152 : Nat := 118140960795 + 5274152 * 2 ^ 59
def prefixEnd_5274152 : Nat := 4983230072969 + 3 ^ 40 * 5274152 * 2
def baseEnd_5274152 : Nat := 2708175020871954089744623

theorem tailTrace_5274152 : CollatzResearch.WordTrace tailWord_5274152 prefixEnd_5274152 2708175020871954089744623 := by
  unfold tailWord_5274152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96182063394327766147032355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128242751192437021529376473 96182063394327766147032355)
  ·
    refine ⟨144273095091491649220548533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96182063394327766147032355 144273095091491649220548533)
    ·
      refine ⟨13525602664827342114426425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144273095091491649220548533 13525602664827342114426425)
      ·
        refine ⟨10144201998620506585819819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13525602664827342114426425 10144201998620506585819819)
        ·
          refine ⟨15216302997930759878729729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10144201998620506585819819 15216302997930759878729729)
          ·
            refine ⟨11412227248448069909047297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15216302997930759878729729 11412227248448069909047297)
            ·
              refine ⟨8559170436336052431785473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11412227248448069909047297 8559170436336052431785473)
              ·
                refine ⟨6419377827252039323839105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8559170436336052431785473 6419377827252039323839105)
                ·
                  refine ⟨4814533370439029492879329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6419377827252039323839105 4814533370439029492879329)
                  ·
                    refine ⟨3610900027829272119659497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4814533370439029492879329 3610900027829272119659497)
                    ·
                      refine ⟨2708175020871954089744623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610900027829272119659497 2708175020871954089744623)
                      ·
                        rfl

theorem cell23_5274152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5274152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274152 prefixEnd_5274152 := by exact prefixLift 5274152
  have htrace : WordTrace (prefixWord ++ tailWord_5274152) baseStart_5274152 baseEnd_5274152 := by
    simpa [prefixWord, tailWord_5274152, baseEnd_5274152] using wordTrace_append hprefix tailTrace_5274152
  have hstable : (prefixWord ++ tailWord_5274152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274152).length < 2 ^ (prefixWord ++ tailWord_5274152).sum := by decide
  have hdescent : baseEnd_5274152 < baseStart_5274152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274161 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_5274161 : Nat := 118140960795 + 5274161 * 2 ^ 59
def prefixEnd_5274161 : Nat := 4983230072969 + 3 ^ 40 * 5274161 * 2
def baseEnd_5274161 : Nat := 2708179642197844554532081

theorem tailTrace_5274161 : CollatzResearch.WordTrace tailWord_5274161 prefixEnd_5274161 2708179642197844554532081 := by
  unfold tailWord_5274161
  simp only [CollatzResearch.WordTrace]
  refine ⟨192364455045622926831142337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128242970030415284554094891 192364455045622926831142337)
  ·
    refine ⟨144273341284217195123356753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192364455045622926831142337 144273341284217195123356753)
    ·
      refine ⟨108205005963162896342517565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144273341284217195123356753 108205005963162896342517565)
      ·
        refine ⟨40576877236186086128444087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108205005963162896342517565 40576877236186086128444087)
        ·
          refine ⟨60865315854279129192666131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40576877236186086128444087 60865315854279129192666131)
          ·
            refine ⟨91297973781418693788999197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60865315854279129192666131 91297973781418693788999197)
            ·
              refine ⟨34236740168032010170874699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91297973781418693788999197 34236740168032010170874699)
              ·
                refine ⟨51355110252048015256312049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34236740168032010170874699 51355110252048015256312049)
                ·
                  refine ⟨38516332689036011442234037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51355110252048015256312049 38516332689036011442234037)
                  ·
                    refine ⟨3610906189597126072709441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38516332689036011442234037 3610906189597126072709441)
                    ·
                      refine ⟨2708179642197844554532081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610906189597126072709441 2708179642197844554532081)
                      ·
                        rfl

theorem cell23_5274161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_5274161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274161 prefixEnd_5274161 := by exact prefixLift 5274161
  have htrace : WordTrace (prefixWord ++ tailWord_5274161) baseStart_5274161 baseEnd_5274161 := by
    simpa [prefixWord, tailWord_5274161, baseEnd_5274161] using wordTrace_append hprefix tailTrace_5274161
  have hstable : (prefixWord ++ tailWord_5274161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274161).length < 2 ^ (prefixWord ++ tailWord_5274161).sum := by decide
  have hdescent : baseEnd_5274161 < baseStart_5274161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274191 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_5274191 : Nat := 118140960795 + 5274191 * 2 ^ 59
def prefixEnd_5274191 : Nat := 4983230072969 + 3 ^ 40 * 5274191 * 2
def baseEnd_5274191 : Nat := 2708195046617479437156943

theorem tailTrace_5274191 : CollatzResearch.WordTrace tailWord_5274191 prefixEnd_5274191 2708195046617479437156943 := by
  unfold tailWord_5274191
  simp only [CollatzResearch.WordTrace]
  refine ⟨192365549235514241954734427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128243699490342827969822951 192365549235514241954734427)
  ·
    refine ⟨288548323853271362932101641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192365549235514241954734427 288548323853271362932101641)
    ·
      refine ⟨216411242889953522199076231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288548323853271362932101641 216411242889953522199076231)
      ·
        refine ⟨324616864334930283298614347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216411242889953522199076231 324616864334930283298614347)
        ·
          refine ⟨486925296502395424947921521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324616864334930283298614347 486925296502395424947921521)
          ·
            refine ⟨365193972376796568710941141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486925296502395424947921521 365193972376796568710941141)
            ·
              refine ⟨8559233727581169579162683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365193972376796568710941141 8559233727581169579162683)
              ·
                refine ⟨12838850591371754368744025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559233727581169579162683 12838850591371754368744025)
                ·
                  refine ⟨9629137943528815776558019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12838850591371754368744025 9629137943528815776558019)
                  ·
                    refine ⟨14443706915293223664837029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9629137943528815776558019 14443706915293223664837029)
                    ·
                      refine ⟨2708195046617479437156943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14443706915293223664837029 2708195046617479437156943)
                      ·
                        rfl

theorem cell23_5274191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_5274191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274191 prefixEnd_5274191 := by exact prefixLift 5274191
  have htrace : WordTrace (prefixWord ++ tailWord_5274191) baseStart_5274191 baseEnd_5274191 := by
    simpa [prefixWord, tailWord_5274191, baseEnd_5274191] using wordTrace_append hprefix tailTrace_5274191
  have hstable : (prefixWord ++ tailWord_5274191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274191).length < 2 ^ (prefixWord ++ tailWord_5274191).sum := by decide
  have hdescent : baseEnd_5274191 < baseStart_5274191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274211 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3]
def baseStart_5274211 : Nat := 118140960795 + 5274211 * 2 ^ 59
def prefixEnd_5274211 : Nat := 4983230072969 + 3 ^ 40 * 5274211 * 2
def baseEnd_5274211 : Nat := 2708205316230569358906851

theorem tailTrace_5274211 : CollatzResearch.WordTrace tailWord_5274211 prefixEnd_5274211 2708205316230569358906851 := by
  unfold tailWord_5274211
  simp only [CollatzResearch.WordTrace]
  refine ⟨192366278695441785370462487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128244185796961190246974991 192366278695441785370462487)
  ·
    refine ⟨288549418043162678055693731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192366278695441785370462487 288549418043162678055693731)
    ·
      refine ⟨432824127064744017083540597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288549418043162678055693731 432824127064744017083540597)
      ·
        refine ⟨40577261912319751601581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 432824127064744017083540597 40577261912319751601581931)
        ·
          refine ⟨60865892868479627402372897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40577261912319751601581931 60865892868479627402372897)
          ·
            refine ⟨45649419651359720551779673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60865892868479627402372897 45649419651359720551779673)
            ·
              refine ⟨34237064738519790413834755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45649419651359720551779673 34237064738519790413834755)
              ·
                refine ⟨51355597107779685620752133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34237064738519790413834755 51355597107779685620752133)
                ·
                  refine ⟨9629174457708691053891025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51355597107779685620752133 9629174457708691053891025)
                  ·
                    refine ⟨7221880843281518290418269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9629174457708691053891025 7221880843281518290418269)
                    ·
                      refine ⟨2708205316230569358906851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221880843281518290418269 2708205316230569358906851)
                      ·
                        rfl

theorem cell23_5274211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_5274211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274211 prefixEnd_5274211 := by exact prefixLift 5274211
  have htrace : WordTrace (prefixWord ++ tailWord_5274211) baseStart_5274211 baseEnd_5274211 := by
    simpa [prefixWord, tailWord_5274211, baseEnd_5274211] using wordTrace_append hprefix tailTrace_5274211
  have hstable : (prefixWord ++ tailWord_5274211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274211).length < 2 ^ (prefixWord ++ tailWord_5274211).sum := by decide
  have hdescent : baseEnd_5274211 < baseStart_5274211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274218 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_5274218 : Nat := 118140960795 + 5274218 * 2 ^ 59
def prefixEnd_5274218 : Nat := 4983230072969 + 3 ^ 40 * 5274218 * 2
def baseEnd_5274218 : Nat := 902736303531716943839773

theorem tailTrace_5274218 : CollatzResearch.WordTrace tailWord_5274218 prefixEnd_5274218 902736303531716943839773 := by
  unfold tailWord_5274218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091633501604106391491827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128244356004277617043978205 48091633501604106391491827)
  ·
    refine ⟨72137450252406159587237741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48091633501604106391491827 72137450252406159587237741)
    ·
      refine ⟨27051543844652309845214153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72137450252406159587237741 27051543844652309845214153)
      ·
        refine ⟨20288657883489232383910615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27051543844652309845214153 20288657883489232383910615)
        ·
          refine ⟨30432986825233848575865923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20288657883489232383910615 30432986825233848575865923)
          ·
            refine ⟨45649480237850772863798885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30432986825233848575865923 45649480237850772863798885)
            ·
              refine ⟨8559277544597019911962291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45649480237850772863798885 8559277544597019911962291)
              ·
                refine ⟨12838916316895529867943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559277544597019911962291 12838916316895529867943437)
                ·
                  refine ⟨4814593618835823700478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12838916316895529867943437 4814593618835823700478789)
                  ·
                    refine ⟨902736303531716943839773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814593618835823700478789 902736303531716943839773)
                    ·
                      rfl

theorem cell23_5274218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_5274218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274218 prefixEnd_5274218 := by exact prefixLift 5274218
  have htrace : WordTrace (prefixWord ++ tailWord_5274218) baseStart_5274218 baseEnd_5274218 := by
    simpa [prefixWord, tailWord_5274218, baseEnd_5274218] using wordTrace_append hprefix tailTrace_5274218
  have hstable : (prefixWord ++ tailWord_5274218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274218).length < 2 ^ (prefixWord ++ tailWord_5274218).sum := by decide
  have hdescent : baseEnd_5274218 < baseStart_5274218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274241 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_5274241 : Nat := 118140960795 + 5274241 * 2 ^ 59
def prefixEnd_5274241 : Nat := 4983230072969 + 3 ^ 40 * 5274241 * 2
def baseEnd_5274241 : Nat := 2708220720650204241531713

theorem tailTrace_5274241 : CollatzResearch.WordTrace tailWord_5274241 prefixEnd_5274241 2708220720650204241531713 := by
  unfold tailWord_5274241
  simp only [CollatzResearch.WordTrace]
  refine ⟨192367372885333100494054577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128244915256888733662703051 192367372885333100494054577)
  ·
    refine ⟨144275529663999825370540933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192367372885333100494054577 144275529663999825370540933)
    ·
      refine ⟨27051661811999967256976425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144275529663999825370540933 27051661811999967256976425)
      ·
        refine ⟨20288746358999975442732319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27051661811999967256976425 20288746358999975442732319)
        ·
          refine ⟨30433119538499963164098479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20288746358999975442732319 30433119538499963164098479)
          ·
            refine ⟨45649679307749944746147719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30433119538499963164098479 45649679307749944746147719)
            ·
              refine ⟨68474518961624917119221579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45649679307749944746147719 68474518961624917119221579)
              ·
                refine ⟨102711778442437375678832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68474518961624917119221579 102711778442437375678832369)
                ·
                  refine ⟨77033833831828031759124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102711778442437375678832369 77033833831828031759124277)
                  ·
                    refine ⟨7221921921733877977417901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77033833831828031759124277 7221921921733877977417901)
                    ·
                      refine ⟨2708220720650204241531713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221921921733877977417901 2708220720650204241531713)
                      ·
                        rfl

theorem cell23_5274241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_5274241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274241 prefixEnd_5274241 := by exact prefixLift 5274241
  have htrace : WordTrace (prefixWord ++ tailWord_5274241) baseStart_5274241 baseEnd_5274241 := by
    simpa [prefixWord, tailWord_5274241, baseEnd_5274241] using wordTrace_append hprefix tailTrace_5274241
  have hstable : (prefixWord ++ tailWord_5274241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274241).length < 2 ^ (prefixWord ++ tailWord_5274241).sum := by decide
  have hdescent : baseEnd_5274241 < baseStart_5274241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274295 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 1, 5]
def baseStart_5274295 : Nat := 118140960795 + 5274295 * 2 ^ 59
def prefixEnd_5274295 : Nat := 4983230072969 + 3 ^ 40 * 5274295 * 2
def baseEnd_5274295 : Nat := 902749482868515676752155

theorem tailTrace_5274295 : CollatzResearch.WordTrace tailWord_5274295 prefixEnd_5274295 902749482868515676752155 := by
  unfold tailWord_5274295
  simp only [CollatzResearch.WordTrace]
  refine ⟨192369342427137467716520339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128246228284758311811013559 192369342427137467716520339)
  ·
    refine ⟨288554013640706201574780509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192369342427137467716520339 288554013640706201574780509)
    ·
      refine ⟨108207755115264825590542691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288554013640706201574780509 108207755115264825590542691)
      ·
        refine ⟨162311632672897238385814037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108207755115264825590542691 162311632672897238385814037)
        ·
          refine ⟨7608357781542058049335033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162311632672897238385814037 7608357781542058049335033)
          ·
            refine ⟨5706268336156543537001275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7608357781542058049335033 5706268336156543537001275)
            ·
              refine ⟨8559402504234815305501913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706268336156543537001275 8559402504234815305501913)
              ·
                refine ⟨6419551878176111479126435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8559402504234815305501913 6419551878176111479126435)
                ·
                  refine ⟨9629327817264167218689653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6419551878176111479126435 9629327817264167218689653)
                  ·
                    refine ⟨902749482868515676752155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9629327817264167218689653 902749482868515676752155)
                    ·
                      rfl

theorem cell23_5274295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_5274295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274295 prefixEnd_5274295 := by exact prefixLift 5274295
  have htrace : WordTrace (prefixWord ++ tailWord_5274295) baseStart_5274295 baseEnd_5274295 := by
    simpa [prefixWord, tailWord_5274295, baseEnd_5274295] using wordTrace_append hprefix tailTrace_5274295
  have hstable : (prefixWord ++ tailWord_5274295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274295).length < 2 ^ (prefixWord ++ tailWord_5274295).sum := by decide
  have hdescent : baseEnd_5274295 < baseStart_5274295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274308 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5274308 : Nat := 118140960795 + 5274308 * 2 ^ 59
def prefixEnd_5274308 : Nat := 4983230072969 + 3 ^ 40 * 5274308 * 2
def baseEnd_5274308 : Nat := 902751707951351826464635

theorem tailTrace_5274308 : CollatzResearch.WordTrace tailWord_5274308 prefixEnd_5274308 902751707951351826464635 := by
  unfold tailWord_5274308
  simp only [CollatzResearch.WordTrace]
  refine ⟨96184908288045185468371789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128246544384060247291162385 96184908288045185468371789)
  ·
    refine ⟨36069340608016944550639421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96184908288045185468371789 36069340608016944550639421)
    ·
      refine ⟨13526002728006354206489783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36069340608016944550639421 13526002728006354206489783)
      ·
        refine ⟨20289004092009531309734675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526002728006354206489783 20289004092009531309734675)
        ·
          refine ⟨30433506138014296964602013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20289004092009531309734675 30433506138014296964602013)
          ·
            refine ⟨11412564801755361361725755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30433506138014296964602013 11412564801755361361725755)
            ·
              refine ⟨17118847202633042042588633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11412564801755361361725755 17118847202633042042588633)
              ·
                refine ⟨12839135401974781531941475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17118847202633042042588633 12839135401974781531941475)
                ·
                  refine ⟨19258703102962172297912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839135401974781531941475 19258703102962172297912213)
                  ·
                    refine ⟨902751707951351826464635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19258703102962172297912213 902751707951351826464635)
                    ·
                      rfl

theorem cell23_5274308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5274308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274308 prefixEnd_5274308 := by exact prefixLift 5274308
  have htrace : WordTrace (prefixWord ++ tailWord_5274308) baseStart_5274308 baseEnd_5274308 := by
    simpa [prefixWord, tailWord_5274308, baseEnd_5274308] using wordTrace_append hprefix tailTrace_5274308
  have hstable : (prefixWord ++ tailWord_5274308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274308).length < 2 ^ (prefixWord ++ tailWord_5274308).sum := by decide
  have hdescent : baseEnd_5274308 < baseStart_5274308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274318 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_5274318 : Nat := 118140960795 + 5274318 * 2 ^ 59
def prefixEnd_5274318 : Nat := 4983230072969 + 3 ^ 40 * 5274318 * 2
def baseEnd_5274318 : Nat := 2708260258660600440268859

theorem tailTrace_5274318 : CollatzResearch.WordTrace tailWord_5274318 prefixEnd_5274318 2708260258660600440268859 := by
  unfold tailWord_5274318
  simp only [CollatzResearch.WordTrace]
  refine ⟨24046272663256767830575951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128246787537369428429738405 24046272663256767830575951)
  ·
    refine ⟨36069408994885151745863927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24046272663256767830575951 36069408994885151745863927)
    ·
      refine ⟨54104113492327727618795891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36069408994885151745863927 54104113492327727618795891)
      ·
        refine ⟨81156170238491591428193837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54104113492327727618795891 81156170238491591428193837)
        ·
          refine ⟨30433563839434346785572689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81156170238491591428193837 30433563839434346785572689)
          ·
            refine ⟨22825172879575760089179517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30433563839434346785572689 22825172879575760089179517)
            ·
              refine ⟨8559439829840910033442319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22825172879575760089179517 8559439829840910033442319)
              ·
                refine ⟨12839159744761365050163479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559439829840910033442319 12839159744761365050163479)
                ·
                  refine ⟨19258739617142047575245219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839159744761365050163479 19258739617142047575245219)
                  ·
                    refine ⟨28888109425713071362867829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19258739617142047575245219 28888109425713071362867829)
                    ·
                      refine ⟨2708260258660600440268859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28888109425713071362867829 2708260258660600440268859)
                      ·
                        rfl

theorem cell23_5274318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_5274318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274318 prefixEnd_5274318 := by exact prefixLift 5274318
  have htrace : WordTrace (prefixWord ++ tailWord_5274318) baseStart_5274318 baseEnd_5274318 := by
    simpa [prefixWord, tailWord_5274318, baseEnd_5274318] using wordTrace_append hprefix tailTrace_5274318
  have hstable : (prefixWord ++ tailWord_5274318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274318).length < 2 ^ (prefixWord ++ tailWord_5274318).sum := by decide
  have hdescent : baseEnd_5274318 < baseStart_5274318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274348 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_5274348 : Nat := 118140960795 + 5274348 * 2 ^ 59
def prefixEnd_5274348 : Nat := 4983230072969 + 3 ^ 40 * 5274348 * 2
def baseEnd_5274348 : Nat := 2708275663080235322893721

theorem tailTrace_5274348 : CollatzResearch.WordTrace tailWord_5274348 prefixEnd_5274348 2708275663080235322893721 := by
  unfold tailWord_5274348
  simp only [CollatzResearch.WordTrace]
  refine ⟨96185637747972728884099849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128247516997296971845466465 96185637747972728884099849)
  ·
    refine ⟨72139228310979546663074887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96185637747972728884099849 72139228310979546663074887)
    ·
      refine ⟨108208842466469319994612331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72139228310979546663074887 108208842466469319994612331)
      ·
        refine ⟨162313263699703979991918497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108208842466469319994612331 162313263699703979991918497)
        ·
          refine ⟨121734947774777984993938873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162313263699703979991918497 121734947774777984993938873)
          ·
            refine ⟨91301210831083488745454155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121734947774777984993938873 91301210831083488745454155)
            ·
              refine ⟨136951816246625233118181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91301210831083488745454155 136951816246625233118181233)
              ·
                refine ⟨102713862184968924838635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136951816246625233118181233 102713862184968924838635925)
                ·
                  refine ⟨4814712289920418351811059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102713862184968924838635925 4814712289920418351811059)
                  ·
                    refine ⟨7222068434880627527716589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4814712289920418351811059 7222068434880627527716589)
                    ·
                      refine ⟨2708275663080235322893721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222068434880627527716589 2708275663080235322893721)
                      ·
                        rfl

theorem cell23_5274348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_5274348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274348 prefixEnd_5274348 := by exact prefixLift 5274348
  have htrace : WordTrace (prefixWord ++ tailWord_5274348) baseStart_5274348 baseEnd_5274348 := by
    simpa [prefixWord, tailWord_5274348, baseEnd_5274348] using wordTrace_append hprefix tailTrace_5274348
  have hstable : (prefixWord ++ tailWord_5274348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274348).length < 2 ^ (prefixWord ++ tailWord_5274348).sum := by decide
  have hdescent : baseEnd_5274348 < baseStart_5274348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274366 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_5274366 : Nat := 118140960795 + 5274366 * 2 ^ 59
def prefixEnd_5274366 : Nat := 4983230072969 + 3 ^ 40 * 5274366 * 2
def baseEnd_5274366 : Nat := 2708284905732016252468639

theorem tailTrace_5274366 : CollatzResearch.WordTrace tailWord_5274366 prefixEnd_5274366 2708284905732016252468639 := by
  unfold tailWord_5274366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24046491501235030855294369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128247954673253497894903301 24046491501235030855294369)
  ·
    refine ⟨18034868625926273141470777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24046491501235030855294369 18034868625926273141470777)
    ·
      refine ⟨13526151469444704856103083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18034868625926273141470777 13526151469444704856103083)
      ·
        refine ⟨20289227204167057284154625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526151469444704856103083 20289227204167057284154625)
        ·
          refine ⟨15216920403125292963115969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20289227204167057284154625 15216920403125292963115969)
          ·
            refine ⟨11412690302343969722336977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15216920403125292963115969 11412690302343969722336977)
            ·
              refine ⟨8559517726757977291752733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11412690302343969722336977 8559517726757977291752733)
              ·
                refine ⟨3209819147534241484407275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8559517726757977291752733 3209819147534241484407275)
                ·
                  refine ⟨4814728721301362226610913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209819147534241484407275 4814728721301362226610913)
                  ·
                    refine ⟨3611046540976021669958185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4814728721301362226610913 3611046540976021669958185)
                    ·
                      refine ⟨2708284905732016252468639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611046540976021669958185 2708284905732016252468639)
                      ·
                        rfl

theorem cell23_5274366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_5274366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274366 prefixEnd_5274366 := by exact prefixLift 5274366
  have htrace : WordTrace (prefixWord ++ tailWord_5274366) baseStart_5274366 baseEnd_5274366 := by
    simpa [prefixWord, tailWord_5274366, baseEnd_5274366] using wordTrace_append hprefix tailTrace_5274366
  have hstable : (prefixWord ++ tailWord_5274366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274366).length < 2 ^ (prefixWord ++ tailWord_5274366).sum := by decide
  have hdescent : baseEnd_5274366 < baseStart_5274366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274408 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5274408 : Nat := 118140960795 + 5274408 * 2 ^ 59
def prefixEnd_5274408 : Nat := 4983230072969 + 3 ^ 40 * 5274408 * 2
def baseEnd_5274408 : Nat := 2708306471919505088143445

theorem tailTrace_5274408 : CollatzResearch.WordTrace tailWord_5274408 prefixEnd_5274408 2708306471919505088143445 := by
  unfold tailWord_5274408
  simp only [CollatzResearch.WordTrace]
  refine ⟨96186731937864044007691939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128248975917152058676922585 96186731937864044007691939)
  ·
    refine ⟨144280097906796066011537909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96186731937864044007691939 144280097906796066011537909)
    ·
      refine ⟨13526259178762131188581679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144280097906796066011537909 13526259178762131188581679)
      ·
        refine ⟨20289388768143196782872519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526259178762131188581679 20289388768143196782872519)
        ·
          refine ⟨30434083152214795174308779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20289388768143196782872519 30434083152214795174308779)
          ·
            refine ⟨45651124728322192761463169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30434083152214795174308779 45651124728322192761463169)
            ·
              refine ⟨34238343546241644571097377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45651124728322192761463169 34238343546241644571097377)
              ·
                refine ⟨25678757659681233428323033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34238343546241644571097377 25678757659681233428323033)
                ·
                  refine ⟨19259068244760925071242275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25678757659681233428323033 19259068244760925071242275)
                  ·
                    refine ⟨28888602367141387606863413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19259068244760925071242275 28888602367141387606863413)
                    ·
                      refine ⟨2708306471919505088143445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28888602367141387606863413 2708306471919505088143445)
                      ·
                        rfl

theorem cell23_5274408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5274408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274408 prefixEnd_5274408 := by exact prefixLift 5274408
  have htrace : WordTrace (prefixWord ++ tailWord_5274408) baseStart_5274408 baseEnd_5274408 := by
    simpa [prefixWord, tailWord_5274408, baseEnd_5274408] using wordTrace_append hprefix tailTrace_5274408
  have hstable : (prefixWord ++ tailWord_5274408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274408).length < 2 ^ (prefixWord ++ tailWord_5274408).sum := by decide
  have hdescent : baseEnd_5274408 < baseStart_5274408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274488 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_5274488 : Nat := 118140960795 + 5274488 * 2 ^ 59
def prefixEnd_5274488 : Nat := 4983230072969 + 3 ^ 40 * 5274488 * 2
def baseEnd_5274488 : Nat := 902782516790621591714359

theorem tailTrace_5274488 : CollatzResearch.WordTrace tailWord_5274488 prefixEnd_5274488 902782516790621591714359 := by
  unfold tailWord_5274488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96188190857719130839148059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128250921143625507785530745 96188190857719130839148059)
  ·
    refine ⟨144282286286578696258722089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96188190857719130839148059 144282286286578696258722089)
    ·
      refine ⟨108211714714934022194041567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144282286286578696258722089 108211714714934022194041567)
      ·
        refine ⟨162317572072401033291062351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108211714714934022194041567 162317572072401033291062351)
        ·
          refine ⟨243476358108601549936593527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162317572072401033291062351 243476358108601549936593527)
          ·
            refine ⟨365214537162902324904890291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243476358108601549936593527 365214537162902324904890291)
            ·
              refine ⟨547821805744353487357335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365214537162902324904890291 547821805744353487357335437)
              ·
                refine ⟨205433177154132557759000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 547821805744353487357335437 205433177154132557759000789)
                ·
                  refine ⟨4814840089549981822476581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 205433177154132557759000789 4814840089549981822476581)
                  ·
                    refine ⟨902782516790621591714359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814840089549981822476581 902782516790621591714359)
                    ·
                      rfl

theorem cell23_5274488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_5274488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274488 prefixEnd_5274488 := by exact prefixLift 5274488
  have htrace : WordTrace (prefixWord ++ tailWord_5274488) baseStart_5274488 baseEnd_5274488 := by
    simpa [prefixWord, tailWord_5274488, baseEnd_5274488] using wordTrace_append hprefix tailTrace_5274488
  have hstable : (prefixWord ++ tailWord_5274488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274488).length < 2 ^ (prefixWord ++ tailWord_5274488).sum := by decide
  have hdescent : baseEnd_5274488 < baseStart_5274488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274522 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_5274522 : Nat := 118140960795 + 5274522 * 2 ^ 59
def prefixEnd_5274522 : Nat := 4983230072969 + 3 ^ 40 * 5274522 * 2
def baseEnd_5274522 : Nat := 902788336238039214039307

theorem tailTrace_5274522 : CollatzResearch.WordTrace tailWord_5274522 prefixEnd_5274522 902788336238039214039307 := by
  unfold tailWord_5274522
  simp only [CollatzResearch.WordTrace]
  refine ⟨48094405449328771371258455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128251747864876723656689213 48094405449328771371258455)
  ·
    refine ⟨72141608173993157056887683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48094405449328771371258455 72141608173993157056887683)
    ·
      refine ⟨108212412260989735585331525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72141608173993157056887683 108212412260989735585331525)
      ·
        refine ⟨20289827298935575422249661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108212412260989735585331525 20289827298935575422249661)
        ·
          refine ⟨7608685237100840783343623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20289827298935575422249661 7608685237100840783343623)
          ·
            refine ⟨11413027855651261175015435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7608685237100840783343623 11413027855651261175015435)
            ·
              refine ⟨17119541783476891762523153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11413027855651261175015435 17119541783476891762523153)
              ·
                refine ⟨12839656337607668821892365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17119541783476891762523153 12839656337607668821892365)
                ·
                  refine ⟨4814871126602875808209637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12839656337607668821892365 4814871126602875808209637)
                  ·
                    refine ⟨902788336238039214039307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814871126602875808209637 902788336238039214039307)
                    ·
                      rfl

theorem cell23_5274522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_5274522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274522 prefixEnd_5274522 := by exact prefixLift 5274522
  have htrace : WordTrace (prefixWord ++ tailWord_5274522) baseStart_5274522 baseEnd_5274522 := by
    simpa [prefixWord, tailWord_5274522, baseEnd_5274522] using wordTrace_append hprefix tailTrace_5274522
  have hstable : (prefixWord ++ tailWord_5274522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274522).length < 2 ^ (prefixWord ++ tailWord_5274522).sum := by decide
  have hdescent : baseEnd_5274522 < baseStart_5274522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274595 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 6, 4]
def baseStart_5274595 : Nat := 118140960795 + 5274595 * 2 ^ 59
def prefixEnd_5274595 : Nat := 4983230072969 + 3 ^ 40 * 5274595 * 2
def baseEnd_5274595 : Nat := 902800830933965285501695

theorem tailTrace_5274595 : CollatzResearch.WordTrace tailWord_5274595 prefixEnd_5274595 902800830933965285501695 := by
  unfold tailWord_5274595
  simp only [CollatzResearch.WordTrace]
  refine ⟨192380284326050618952441239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128253522884033745968294159 192380284326050618952441239)
  ·
    refine ⟨288570426489075928428661859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192380284326050618952441239 288570426489075928428661859)
    ·
      refine ⟨432855639733613892642992789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288570426489075928428661859 432855639733613892642992789)
      ·
        refine ⟨20290108112513151217640287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 432855639733613892642992789 20290108112513151217640287)
        ·
          refine ⟨30435162168769726826460431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290108112513151217640287 30435162168769726826460431)
          ·
            refine ⟨45652743253154590239690647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30435162168769726826460431 45652743253154590239690647)
            ·
              refine ⟨68479114879731885359535971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45652743253154590239690647 68479114879731885359535971)
              ·
                refine ⟨102718672319597828039303957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68479114879731885359535971 102718672319597828039303957)
                ·
                  refine ⟨4814937764981148189342373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102718672319597828039303957 4814937764981148189342373)
                  ·
                    refine ⟨902800830933965285501695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814937764981148189342373 902800830933965285501695)
                    ·
                      rfl

theorem cell23_5274595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 4].length) (baseStart_5274595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274595 prefixEnd_5274595 := by exact prefixLift 5274595
  have htrace : WordTrace (prefixWord ++ tailWord_5274595) baseStart_5274595 baseEnd_5274595 := by
    simpa [prefixWord, tailWord_5274595, baseEnd_5274595] using wordTrace_append hprefix tailTrace_5274595
  have hstable : (prefixWord ++ tailWord_5274595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274595).length < 2 ^ (prefixWord ++ tailWord_5274595).sum := by decide
  have hdescent : baseEnd_5274595 < baseStart_5274595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274602 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_5274602 : Nat := 118140960795 + 5274602 * 2 ^ 59
def prefixEnd_5274602 : Nat := 4983230072969 + 3 ^ 40 * 5274602 * 2
def baseEnd_5274602 : Nat := 2708406087166477329117553

theorem tailTrace_5274602 : CollatzResearch.WordTrace tailWord_5274602 prefixEnd_5274602 2708406087166477329117553 := by
  unfold tailWord_5274602
  simp only [CollatzResearch.WordTrace]
  refine ⟨48095134909256314786986515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128253693091350172765297373 48095134909256314786986515)
  ·
    refine ⟨72142702363884472180479773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48095134909256314786986515 72142702363884472180479773)
    ·
      refine ⟨27053513386456677067679915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72142702363884472180479773 27053513386456677067679915)
      ·
        refine ⟨40580270079685015601519873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27053513386456677067679915 40580270079685015601519873)
        ·
          refine ⟨30435202559763761701139905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40580270079685015601519873 30435202559763761701139905)
          ·
            refine ⟨22826401919822821275854929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30435202559763761701139905 22826401919822821275854929)
            ·
              refine ⟨17119801439867115956891197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22826401919822821275854929 17119801439867115956891197)
              ·
                refine ⟨6419925539950168483834199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17119801439867115956891197 6419925539950168483834199)
                ·
                  refine ⟨9629888309925252725751299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6419925539950168483834199 9629888309925252725751299)
                  ·
                    refine ⟨14444832464887879088626949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9629888309925252725751299 14444832464887879088626949)
                    ·
                      refine ⟨2708406087166477329117553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14444832464887879088626949 2708406087166477329117553)
                      ·
                        rfl

theorem cell23_5274602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_5274602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274602 prefixEnd_5274602 := by exact prefixLift 5274602
  have htrace : WordTrace (prefixWord ++ tailWord_5274602) baseStart_5274602 baseEnd_5274602 := by
    simpa [prefixWord, tailWord_5274602, baseEnd_5274602] using wordTrace_append hprefix tailTrace_5274602
  have hstable : (prefixWord ++ tailWord_5274602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274602).length < 2 ^ (prefixWord ++ tailWord_5274602).sum := by decide
  have hdescent : baseEnd_5274602 < baseStart_5274602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274613 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5274613 : Nat := 118140960795 + 5274613 * 2 ^ 59
def prefixEnd_5274613 : Nat := 4983230072969 + 3 ^ 40 * 5274613 * 2
def baseEnd_5274613 : Nat := 2708411735453676786080003

theorem tailTrace_5274613 : CollatzResearch.WordTrace tailWord_5274613 prefixEnd_5274613 2708411735453676786080003 := by
  unfold tailWord_5274613
  simp only [CollatzResearch.WordTrace]
  refine ⟨192380940839985408026596493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128253960559990272017730995 192380940839985408026596493)
  ·
    refine ⟨72142852814994528009973685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192380940839985408026596493 72142852814994528009973685)
    ·
      refine ⟨6763392451405737000935033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72142852814994528009973685 6763392451405737000935033)
      ·
        refine ⟨5072544338554302750701275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6763392451405737000935033 5072544338554302750701275)
        ·
          refine ⟨7608816507831454126051913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072544338554302750701275 7608816507831454126051913)
          ·
            refine ⟨5706612380873590594538935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7608816507831454126051913 5706612380873590594538935)
            ·
              refine ⟨8559918571310385891808403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706612380873590594538935 8559918571310385891808403)
              ·
                refine ⟨12839877856965578837712605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559918571310385891808403 12839877856965578837712605)
                ·
                  refine ⟨4814954196362092064142227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12839877856965578837712605 4814954196362092064142227)
                  ·
                    refine ⟨7222431294543138096213341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4814954196362092064142227 7222431294543138096213341)
                    ·
                      refine ⟨2708411735453676786080003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222431294543138096213341 2708411735453676786080003)
                      ·
                        rfl

theorem cell23_5274613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5274613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274613 prefixEnd_5274613 := by exact prefixLift 5274613
  have htrace : WordTrace (prefixWord ++ tailWord_5274613) baseStart_5274613 baseEnd_5274613 := by
    simpa [prefixWord, tailWord_5274613, baseEnd_5274613] using wordTrace_append hprefix tailTrace_5274613
  have hstable : (prefixWord ++ tailWord_5274613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274613).length < 2 ^ (prefixWord ++ tailWord_5274613).sum := by decide
  have hdescent : baseEnd_5274613 < baseStart_5274613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274625 : List Nat := [1, 2, 4, 1, 2, 3, 2, 8]
def baseStart_5274625 : Nat := 118140960795 + 5274625 * 2 ^ 59
def prefixEnd_5274625 : Nat := 4983230072969 + 3 ^ 40 * 5274625 * 2
def baseEnd_5274625 : Nat := 100311773971167805152961

theorem tailTrace_5274625 : CollatzResearch.WordTrace tailWord_5274625 prefixEnd_5274625 100311773971167805152961 := by
  unfold tailWord_5274625
  simp only [CollatzResearch.WordTrace]
  refine ⟨192381378515941934076033329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128254252343961289384022219 192381378515941934076033329)
  ·
    refine ⟨144286033886956450557024997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192381378515941934076033329 144286033886956450557024997)
    ·
      refine ⟨27053631353804334479442187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144286033886956450557024997 27053631353804334479442187)
      ·
        refine ⟨40580447030706501719163281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27053631353804334479442187 40580447030706501719163281)
        ·
          refine ⟨30435335273029876289372461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40580447030706501719163281 30435335273029876289372461)
          ·
            refine ⟨11413250727386203608514673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30435335273029876289372461 11413250727386203608514673)
            ·
              refine ⟨8559938045539652706386005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11413250727386203608514673 8559938045539652706386005)
              ·
                refine ⟨100311773971167805152961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8559938045539652706386005 100311773971167805152961)
                ·
                  rfl

theorem cell23_5274625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 8].length) (baseStart_5274625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274625 prefixEnd_5274625 := by exact prefixLift 5274625
  have htrace : WordTrace (prefixWord ++ tailWord_5274625) baseStart_5274625 baseEnd_5274625 := by
    simpa [prefixWord, tailWord_5274625, baseEnd_5274625] using wordTrace_append hprefix tailTrace_5274625
  have hstable : (prefixWord ++ tailWord_5274625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274625).length < 2 ^ (prefixWord ++ tailWord_5274625).sum := by decide
  have hdescent : baseEnd_5274625 < baseStart_5274625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274656 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5274656 : Nat := 118140960795 + 5274656 * 2 ^ 59
def prefixEnd_5274656 : Nat := 4983230072969 + 3 ^ 40 * 5274656 * 2
def baseEnd_5274656 : Nat := 2708433815121820117842305

theorem tailTrace_5274656 : CollatzResearch.WordTrace tailWord_5274656 prefixEnd_5274656 2708433815121820117842305 := by
  unfold tailWord_5274656
  simp only [CollatzResearch.WordTrace]
  refine ⟨96191254589414813185205911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128255006119219750913607881 96191254589414813185205911)
  ·
    refine ⟨144286881884122219777808867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96191254589414813185205911 144286881884122219777808867)
    ·
      refine ⟨216430322826183329666713301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144286881884122219777808867 216430322826183329666713301)
      ·
        refine ⟨5072585691238671789063593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 216430322826183329666713301 5072585691238671789063593)
        ·
          refine ⟨3804439268429003841797695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072585691238671789063593 3804439268429003841797695)
          ·
            refine ⟨5706658902643505762696543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3804439268429003841797695 5706658902643505762696543)
            ·
              refine ⟨8559988353965258644044815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706658902643505762696543 8559988353965258644044815)
              ·
                refine ⟨12839982530947887966067223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559988353965258644044815 12839982530947887966067223)
                ·
                  refine ⟨19259973796421831949100835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839982530947887966067223 19259973796421831949100835)
                  ·
                    refine ⟨28889960694632747923651253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19259973796421831949100835 28889960694632747923651253)
                    ·
                      refine ⟨2708433815121820117842305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28889960694632747923651253 2708433815121820117842305)
                      ·
                        rfl

theorem cell23_5274656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5274656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274656 prefixEnd_5274656 := by exact prefixLift 5274656
  have htrace : WordTrace (prefixWord ++ tailWord_5274656) baseStart_5274656 baseEnd_5274656 := by
    simpa [prefixWord, tailWord_5274656, baseEnd_5274656] using wordTrace_append hprefix tailTrace_5274656
  have hstable : (prefixWord ++ tailWord_5274656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274656).length < 2 ^ (prefixWord ++ tailWord_5274656).sum := by decide
  have hdescent : baseEnd_5274656 < baseStart_5274656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274685 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_5274685 : Nat := 118140960795 + 5274685 * 2 ^ 59
def prefixEnd_5274685 : Nat := 4983230072969 + 3 ^ 40 * 5274685 * 2
def baseEnd_5274685 : Nat := 902816235353600168126557

theorem tailTrace_5274685 : CollatzResearch.WordTrace tailWord_5274685 prefixEnd_5274685 902816235353600168126557 := by
  unfold tailWord_5274685
  simp only [CollatzResearch.WordTrace]
  refine ⟨192383566895724564323217509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128255711263816376215478339 192383566895724564323217509)
  ·
    refine ⟨36071918792948355810603283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192383566895724564323217509 36071918792948355810603283)
    ·
      refine ⟨54107878189422533715904925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36071918792948355810603283 54107878189422533715904925)
      ·
        refine ⟨20290454321033450143464347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54107878189422533715904925 20290454321033450143464347)
        ·
          refine ⟨30435681481550175215196521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290454321033450143464347 30435681481550175215196521)
          ·
            refine ⟨22826761111162631411397391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30435681481550175215196521 22826761111162631411397391)
            ·
              refine ⟨34240141666743947117096087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22826761111162631411397391 34240141666743947117096087)
              ·
                refine ⟨51360212500115920675644131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34240141666743947117096087 51360212500115920675644131)
                ·
                  refine ⟨77040318750173881013466197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51360212500115920675644131 77040318750173881013466197)
                  ·
                    refine ⟨902816235353600168126557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77040318750173881013466197 902816235353600168126557)
                    ·
                      rfl

theorem cell23_5274685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_5274685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274685 prefixEnd_5274685 := by exact prefixLift 5274685
  have htrace : WordTrace (prefixWord ++ tailWord_5274685) baseStart_5274685 baseEnd_5274685 := by
    simpa [prefixWord, tailWord_5274685, baseEnd_5274685] using wordTrace_append hprefix tailTrace_5274685
  have hstable : (prefixWord ++ tailWord_5274685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274685).length < 2 ^ (prefixWord ++ tailWord_5274685).sum := by decide
  have hdescent : baseEnd_5274685 < baseStart_5274685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274686 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5274686 : Nat := 118140960795 + 5274686 * 2 ^ 59
def prefixEnd_5274686 : Nat := 4983230072969 + 3 ^ 40 * 5274686 * 2
def baseEnd_5274686 : Nat := 2708449219541455000467167

theorem tailTrace_5274686 : CollatzResearch.WordTrace tailWord_5274686 prefixEnd_5274686 2708449219541455000467167 := by
  unfold tailWord_5274686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047950421090117686750489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128255735579147294329335941 24047950421090117686750489)
  ·
    refine ⟨18035962815817588265062867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24047950421090117686750489 18035962815817588265062867)
    ·
      refine ⟨27053944223726382397594301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18035962815817588265062867 27053944223726382397594301)
      ·
        refine ⟨10145229083897393399097863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27053944223726382397594301 10145229083897393399097863)
        ·
          refine ⟨15217843625846090098646795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145229083897393399097863 15217843625846090098646795)
          ·
            refine ⟨22826765438769135147970193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15217843625846090098646795 22826765438769135147970193)
            ·
              refine ⟨17120074079076851360977645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22826765438769135147970193 17120074079076851360977645)
              ·
                refine ⟨6420027779653819260366617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17120074079076851360977645 6420027779653819260366617)
                ·
                  refine ⟨4815020834740364445274963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420027779653819260366617 4815020834740364445274963)
                  ·
                    refine ⟨7222531252110546667912445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815020834740364445274963 7222531252110546667912445)
                    ·
                      refine ⟨2708449219541455000467167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222531252110546667912445 2708449219541455000467167)
                      ·
                        rfl

theorem cell23_5274686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5274686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274686 prefixEnd_5274686 := by exact prefixLift 5274686
  have htrace : WordTrace (prefixWord ++ tailWord_5274686) baseStart_5274686 baseEnd_5274686 := by
    simpa [prefixWord, tailWord_5274686, baseEnd_5274686] using wordTrace_append hprefix tailTrace_5274686
  have hstable : (prefixWord ++ tailWord_5274686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274686).length < 2 ^ (prefixWord ++ tailWord_5274686).sum := by decide
  have hdescent : baseEnd_5274686 < baseStart_5274686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274709 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5274709 : Nat := 118140960795 + 5274709 * 2 ^ 59
def prefixEnd_5274709 : Nat := 4983230072969 + 3 ^ 40 * 5274709 * 2
def baseEnd_5274709 : Nat := 2708461029596508410479561

theorem tailTrace_5274709 : CollatzResearch.WordTrace tailWord_5274709 prefixEnd_5274709 2708461029596508410479561 := by
  unfold tailWord_5274709
  simp only [CollatzResearch.WordTrace]
  refine ⟨192384442247637616422091181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128256294831758410948060787 192384442247637616422091181)
  ·
    refine ⟨72144165842864106158284193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192384442247637616422091181 72144165842864106158284193)
    ·
      refine ⟨54108124382148079618713145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72144165842864106158284193 54108124382148079618713145)
      ·
        refine ⟨40581093286611059714034859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54108124382148079618713145 40581093286611059714034859)
        ·
          refine ⟨60871639929916589571052289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40581093286611059714034859 60871639929916589571052289)
          ·
            refine ⟨45653729947437442178289217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60871639929916589571052289 45653729947437442178289217)
            ·
              refine ⟨34240297460578081633716913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45653729947437442178289217 34240297460578081633716913)
              ·
                refine ⟨25680223095433561225287685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34240297460578081633716913 25680223095433561225287685)
                ·
                  refine ⟨4815041830393792729741441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25680223095433561225287685 4815041830393792729741441)
                  ·
                    refine ⟨3611281372795344547306081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815041830393792729741441 3611281372795344547306081)
                    ·
                      refine ⟨2708461029596508410479561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611281372795344547306081 2708461029596508410479561)
                      ·
                        rfl

theorem cell23_5274709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5274709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274709 prefixEnd_5274709 := by exact prefixLift 5274709
  have htrace : WordTrace (prefixWord ++ tailWord_5274709) baseStart_5274709 baseEnd_5274709 := by
    simpa [prefixWord, tailWord_5274709, baseEnd_5274709] using wordTrace_append hprefix tailTrace_5274709
  have hstable : (prefixWord ++ tailWord_5274709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274709).length < 2 ^ (prefixWord ++ tailWord_5274709).sum := by decide
  have hdescent : baseEnd_5274709 < baseStart_5274709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274732 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 5]
def baseStart_5274732 : Nat := 118140960795 + 5274732 * 2 ^ 59
def prefixEnd_5274732 : Nat := 4983230072969 + 3 ^ 40 * 5274732 * 2
def baseEnd_5274732 : Nat := 300941426627951313387995

theorem tailTrace_5274732 : CollatzResearch.WordTrace tailWord_5274732 prefixEnd_5274732 300941426627951313387995 := by
  unfold tailWord_5274732
  simp only [CollatzResearch.WordTrace]
  refine ⟨96192640563277145675089225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128256854084369527566785633 96192640563277145675089225)
  ·
    refine ⟨72144480422457859256316919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96192640563277145675089225 72144480422457859256316919)
    ·
      refine ⟨108216720633686788884475379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72144480422457859256316919 108216720633686788884475379)
      ·
        refine ⟨162325080950530183326713069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108216720633686788884475379 162325080950530183326713069)
        ·
          refine ⟨60871905356448818747517401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162325080950530183326713069 60871905356448818747517401)
          ·
            refine ⟨45653929017336614060638051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60871905356448818747517401 45653929017336614060638051)
            ·
              refine ⟨68480893526004921090957077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45653929017336614060638051 68480893526004921090957077)
              ·
                refine ⟨3210041884031480676138613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68480893526004921090957077 3210041884031480676138613)
                ·
                  refine ⟨300941426627951313387995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210041884031480676138613 300941426627951313387995)
                  ·
                    rfl

theorem cell23_5274732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_5274732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274732 prefixEnd_5274732 := by exact prefixLift 5274732
  have htrace : WordTrace (prefixWord ++ tailWord_5274732) baseStart_5274732 baseEnd_5274732 := by
    simpa [prefixWord, tailWord_5274732, baseEnd_5274732] using wordTrace_append hprefix tailTrace_5274732
  have hstable : (prefixWord ++ tailWord_5274732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274732).length < 2 ^ (prefixWord ++ tailWord_5274732).sum := by decide
  have hdescent : baseEnd_5274732 < baseStart_5274732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274752 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2]
def baseStart_5274752 : Nat := 118140960795 + 5274752 * 2 ^ 59
def prefixEnd_5274752 : Nat := 4983230072969 + 3 ^ 40 * 5274752 * 2
def baseEnd_5274752 : Nat := 2708483109264651742241863

theorem tailTrace_5274752 : CollatzResearch.WordTrace tailWord_5274752 prefixEnd_5274752 2708483109264651742241863 := by
  unfold tailWord_5274752
  simp only [CollatzResearch.WordTrace]
  refine ⟨96193005293240917382953255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128257340390987889843937673 96193005293240917382953255)
  ·
    refine ⟨144289507939861376074429883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96193005293240917382953255 144289507939861376074429883)
    ·
      refine ⟨216434261909792064111644825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144289507939861376074429883 216434261909792064111644825)
      ·
        refine ⟨162325696432344048083733619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216434261909792064111644825 162325696432344048083733619)
        ·
          refine ⟨243488544648516072125600429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162325696432344048083733619 243488544648516072125600429)
          ·
            refine ⟨91308204243193527047100161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243488544648516072125600429 91308204243193527047100161)
            ·
              refine ⟨68481153182395145285325121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91308204243193527047100161 68481153182395145285325121)
              ·
                refine ⟨51360864886796358963993841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68481153182395145285325121 51360864886796358963993841)
                ·
                  refine ⟨38520648665097269222995381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51360864886796358963993841 38520648665097269222995381)
                  ·
                    refine ⟨3611310812352868989655817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38520648665097269222995381 3611310812352868989655817)
                    ·
                      refine ⟨2708483109264651742241863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611310812352868989655817 2708483109264651742241863)
                      ·
                        rfl

theorem cell23_5274752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_5274752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274752 prefixEnd_5274752 := by exact prefixLift 5274752
  have htrace : WordTrace (prefixWord ++ tailWord_5274752) baseStart_5274752 baseEnd_5274752 := by
    simpa [prefixWord, tailWord_5274752, baseEnd_5274752] using wordTrace_append hprefix tailTrace_5274752
  have hstable : (prefixWord ++ tailWord_5274752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274752).length < 2 ^ (prefixWord ++ tailWord_5274752).sum := by decide
  have hdescent : baseEnd_5274752 < baseStart_5274752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274762 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_5274762 : Nat := 118140960795 + 5274762 * 2 ^ 59
def prefixEnd_5274762 : Nat := 4983230072969 + 3 ^ 40 * 5274762 * 2
def baseEnd_5274762 : Nat := 902829414690398901038939

theorem tailTrace_5274762 : CollatzResearch.WordTrace tailWord_5274762 prefixEnd_5274762 902829414690398901038939 := by
  unfold tailWord_5274762
  simp only [CollatzResearch.WordTrace]
  refine ⟨48096593829111401618442635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128257583544297070982513693 48096593829111401618442635)
  ·
    refine ⟨72144890743667102427663953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48096593829111401618442635 72144890743667102427663953)
    ·
      refine ⟨54108668057750326820747965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72144890743667102427663953 54108668057750326820747965)
      ·
        refine ⟨20290750521656372557780487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54108668057750326820747965 20290750521656372557780487)
        ·
          refine ⟨30436125782484558836670731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290750521656372557780487 30436125782484558836670731)
          ·
            refine ⟨45654188673726838255006097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30436125782484558836670731 45654188673726838255006097)
            ·
              refine ⟨34240641505295128691254573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45654188673726838255006097 34240641505295128691254573)
              ·
                refine ⟨12840240564485673259220465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34240641505295128691254573 12840240564485673259220465)
                ·
                  refine ⟨9630180423364254944415349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12840240564485673259220465 9630180423364254944415349)
                  ·
                    refine ⟨902829414690398901038939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9630180423364254944415349 902829414690398901038939)
                    ·
                      rfl

theorem cell23_5274762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_5274762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274762 prefixEnd_5274762 := by exact prefixLift 5274762
  have htrace : WordTrace (prefixWord ++ tailWord_5274762) baseStart_5274762 baseEnd_5274762 := by
    simpa [prefixWord, tailWord_5274762, baseEnd_5274762] using wordTrace_append hprefix tailTrace_5274762
  have hstable : (prefixWord ++ tailWord_5274762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274762).length < 2 ^ (prefixWord ++ tailWord_5274762).sum := by decide
  have hdescent : baseEnd_5274762 < baseStart_5274762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274766 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_5274766 : Nat := 118140960795 + 5274766 * 2 ^ 59
def prefixEnd_5274766 : Nat := 4983230072969 + 3 ^ 40 * 5274766 * 2
def baseEnd_5274766 : Nat := 300943366443757187496311

theorem tailTrace_5274766 : CollatzResearch.WordTrace tailWord_5274766 prefixEnd_5274766 300943366443757187496311 := by
  unfold tailWord_5274766
  simp only [CollatzResearch.WordTrace]
  refine ⟨24048315151053889394614519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128257680805620743437944101 24048315151053889394614519)
  ·
    refine ⟨36072472726580834091921779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24048315151053889394614519 36072472726580834091921779)
    ·
      refine ⟨54108709089871251137882669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36072472726580834091921779 54108709089871251137882669)
      ·
        refine ⟨20290765908701719176706001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54108709089871251137882669 20290765908701719176706001)
        ·
          refine ⟨15218074431526289382529501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20290765908701719176706001 15218074431526289382529501)
          ·
            refine ⟨5706777911822358518448563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15218074431526289382529501 5706777911822358518448563)
            ·
              refine ⟨8560166867733537777672845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706777911822358518448563 8560166867733537777672845)
              ·
                refine ⟨3210062575400076666627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8560166867733537777672845 3210062575400076666627317)
                ·
                  refine ⟨300943366443757187496311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210062575400076666627317 300943366443757187496311)
                  ·
                    rfl

theorem cell23_5274766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_5274766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274766 prefixEnd_5274766 := by exact prefixLift 5274766
  have htrace : WordTrace (prefixWord ++ tailWord_5274766) baseStart_5274766 baseEnd_5274766 := by
    simpa [prefixWord, tailWord_5274766, baseEnd_5274766] using wordTrace_append hprefix tailTrace_5274766
  have hstable : (prefixWord ++ tailWord_5274766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274766).length < 2 ^ (prefixWord ++ tailWord_5274766).sum := by decide
  have hdescent : baseEnd_5274766 < baseStart_5274766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274852 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_5274852 : Nat := 118140960795 + 5274852 * 2 ^ 59
def prefixEnd_5274852 : Nat := 4983230072969 + 3 ^ 40 * 5274852 * 2
def baseEnd_5274852 : Nat := 902844819110033783663801

theorem tailTrace_5274852 : CollatzResearch.WordTrace tailWord_5274852 prefixEnd_5274852 902844819110033783663801 := by
  unfold tailWord_5274852
  simp only [CollatzResearch.WordTrace]
  refine ⟨96194828943059775922273405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128259771924079701229697873 96194828943059775922273405)
  ·
    refine ⟨36073060853647415970852527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96194828943059775922273405 36073060853647415970852527)
    ·
      refine ⟨54109591280471123956278791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36073060853647415970852527 54109591280471123956278791)
      ·
        refine ⟨81164386920706685934418187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54109591280471123956278791 81164386920706685934418187)
        ·
          refine ⟨121746580381060028901627281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81164386920706685934418187 121746580381060028901627281)
          ·
            refine ⟨91309935285795021676220461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121746580381060028901627281 91309935285795021676220461)
            ·
              refine ⟨34241225732173133128582673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91309935285795021676220461 34241225732173133128582673)
              ·
                refine ⟨25680919299129849846437005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34241225732173133128582673 25680919299129849846437005)
                ·
                  refine ⟨9630344737173693692413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25680919299129849846437005 9630344737173693692413877)
                  ·
                    refine ⟨902844819110033783663801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9630344737173693692413877 902844819110033783663801)
                    ·
                      rfl

theorem cell23_5274852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_5274852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274852 prefixEnd_5274852 := by exact prefixLift 5274852
  have htrace : WordTrace (prefixWord ++ tailWord_5274852) baseStart_5274852 baseEnd_5274852 := by
    simpa [prefixWord, tailWord_5274852, baseEnd_5274852] using wordTrace_append hprefix tailTrace_5274852
  have hstable : (prefixWord ++ tailWord_5274852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274852).length < 2 ^ (prefixWord ++ tailWord_5274852).sum := by decide
  have hdescent : baseEnd_5274852 < baseStart_5274852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274876 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_5274876 : Nat := 118140960795 + 5274876 * 2 ^ 59
def prefixEnd_5274876 : Nat := 4983230072969 + 3 ^ 40 * 5274876 * 2
def baseEnd_5274876 : Nat := 2708546780865809257091293

theorem tailTrace_5274876 : CollatzResearch.WordTrace tailWord_5274876 prefixEnd_5274876 2708546780865809257091293 := by
  unfold tailWord_5274876
  simp only [CollatzResearch.WordTrace]
  refine ⟨96195266619016301971710241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128260355492021735962280321 96195266619016301971710241)
  ·
    refine ⟨72146449964262226478782681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96195266619016301971710241 72146449964262226478782681)
    ·
      refine ⟨54109837473196669859087011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72146449964262226478782681 54109837473196669859087011)
      ·
        refine ⟨81164756209795004788630517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54109837473196669859087011 81164756209795004788630517)
        ·
          refine ⟨7609195894668281698934111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81164756209795004788630517 7609195894668281698934111)
          ·
            refine ⟨11413793842002422548401167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609195894668281698934111 11413793842002422548401167)
            ·
              refine ⟨17120690763003633822601751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11413793842002422548401167 17120690763003633822601751)
              ·
                refine ⟨25681036144505450733902627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17120690763003633822601751 25681036144505450733902627)
                ·
                  refine ⟨38521554216758176100853941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25681036144505450733902627 38521554216758176100853941)
                  ·
                    refine ⟨3611395707821079009455057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38521554216758176100853941 3611395707821079009455057)
                    ·
                      refine ⟨2708546780865809257091293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611395707821079009455057 2708546780865809257091293)
                      ·
                        rfl

theorem cell23_5274876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_5274876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274876 prefixEnd_5274876 := by exact prefixLift 5274876
  have htrace : WordTrace (prefixWord ++ tailWord_5274876) baseStart_5274876 baseEnd_5274876 := by
    simpa [prefixWord, tailWord_5274876, baseEnd_5274876] using wordTrace_append hprefix tailTrace_5274876
  have hstable : (prefixWord ++ tailWord_5274876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274876).length < 2 ^ (prefixWord ++ tailWord_5274876).sum := by decide
  have hdescent : baseEnd_5274876 < baseStart_5274876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274883 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 1, 1, 3]
def baseStart_5274883 : Nat := 118140960795 + 5274883 * 2 ^ 59
def prefixEnd_5274883 : Nat := 4983230072969 + 3 ^ 40 * 5274883 * 2
def baseEnd_5274883 : Nat := 2708550375230390729703761

theorem tailTrace_5274883 : CollatzResearch.WordTrace tailWord_5274883 prefixEnd_5274883 2708550375230390729703761 := by
  unfold tailWord_5274883
  simp only [CollatzResearch.WordTrace]
  refine ⟨192390788549007244138925303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128260525699338162759283535 192390788549007244138925303)
  ·
    refine ⟨288586182823510866208387955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192390788549007244138925303 288586182823510866208387955)
    ·
      refine ⟨432879274235266299312581933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288586182823510866208387955 432879274235266299312581933)
      ·
        refine ⟨162329727838224862242218225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432879274235266299312581933 162329727838224862242218225)
        ·
          refine ⟨121747295878668646681663669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162329727838224862242218225 121747295878668646681663669)
          ·
            refine ⟨11413808988625185626405969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121747295878668646681663669 11413808988625185626405969)
            ·
              refine ⟨8560356741468889219804477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11413808988625185626405969 8560356741468889219804477)
              ·
                refine ⟨3210133778050833457426679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8560356741468889219804477 3210133778050833457426679)
                ·
                  refine ⟨4815200667076250186140019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210133778050833457426679 4815200667076250186140019)
                  ·
                    refine ⟨7222801000614375279210029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815200667076250186140019 7222801000614375279210029)
                    ·
                      refine ⟨2708550375230390729703761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222801000614375279210029 2708550375230390729703761)
                      ·
                        rfl

theorem cell23_5274883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_5274883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274883 prefixEnd_5274883 := by exact prefixLift 5274883
  have htrace : WordTrace (prefixWord ++ tailWord_5274883) baseStart_5274883 baseEnd_5274883 := by
    simpa [prefixWord, tailWord_5274883, baseEnd_5274883] using wordTrace_append hprefix tailTrace_5274883
  have hstable : (prefixWord ++ tailWord_5274883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274883).length < 2 ^ (prefixWord ++ tailWord_5274883).sum := by decide
  have hdescent : baseEnd_5274883 < baseStart_5274883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274889 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_5274889 : Nat := 118140960795 + 5274889 * 2 ^ 59
def prefixEnd_5274889 : Nat := 4983230072969 + 3 ^ 40 * 5274889 * 2
def baseEnd_5274889 : Nat := 2708553456114317706228733

theorem tailTrace_5274889 : CollatzResearch.WordTrace tailWord_5274889 prefixEnd_5274889 2708553456114317706228733 := by
  unfold tailWord_5274889
  simp only [CollatzResearch.WordTrace]
  refine ⟨192391007386985507163643721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128260671591323671442429147 192391007386985507163643721)
  ·
    refine ⟨144293255540239130372732791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192391007386985507163643721 144293255540239130372732791)
    ·
      refine ⟨216439883310358695559099187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144293255540239130372732791 216439883310358695559099187)
      ·
        refine ⟨324659824965538043338648781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216439883310358695559099187 324659824965538043338648781)
        ·
          refine ⟨121747434362076766251993293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324659824965538043338648781 121747434362076766251993293)
          ·
            refine ⟨45655287885778787344497485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121747434362076766251993293 45655287885778787344497485)
            ·
              refine ⟨17120732957167045254186557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45655287885778787344497485 17120732957167045254186557)
              ·
                refine ⟨6420274858937641970319959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17120732957167045254186557 6420274858937641970319959)
                ·
                  refine ⟨9630412288406462955479939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6420274858937641970319959 9630412288406462955479939)
                  ·
                    refine ⟨14445618432609694433219909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9630412288406462955479939 14445618432609694433219909)
                    ·
                      refine ⟨2708553456114317706228733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14445618432609694433219909 2708553456114317706228733)
                      ·
                        rfl

theorem cell23_5274889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_5274889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274889 prefixEnd_5274889 := by exact prefixLift 5274889
  have htrace : WordTrace (prefixWord ++ tailWord_5274889) baseStart_5274889 baseEnd_5274889 := by
    simpa [prefixWord, tailWord_5274889, baseEnd_5274889] using wordTrace_append hprefix tailTrace_5274889
  have hstable : (prefixWord ++ tailWord_5274889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274889).length < 2 ^ (prefixWord ++ tailWord_5274889).sum := by decide
  have hdescent : baseEnd_5274889 < baseStart_5274889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274909 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5274909 : Nat := 118140960795 + 5274909 * 2 ^ 59
def prefixEnd_5274909 : Nat := 4983230072969 + 3 ^ 40 * 5274909 * 2
def baseEnd_5274909 : Nat := 2708563725727407627978641

theorem tailTrace_5274909 : CollatzResearch.WordTrace tailWord_5274909 prefixEnd_5274909 2708563725727407627978641 := by
  unfold tailWord_5274909
  simp only [CollatzResearch.WordTrace]
  refine ⟨192391736846913050579371781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128261157897942033719581187 192391736846913050579371781)
  ·
    refine ⟨36073450658796196983632209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192391736846913050579371781 36073450658796196983632209)
    ·
      refine ⟨27055087994097147737724157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36073450658796196983632209 27055087994097147737724157)
      ·
        refine ⟨10145657997786430401646559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27055087994097147737724157 10145657997786430401646559)
        ·
          refine ⟨15218486996679645602469839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145657997786430401646559 15218486996679645602469839)
          ·
            refine ⟨22827730495019468403704759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15218486996679645602469839 22827730495019468403704759)
            ·
              refine ⟨34241595742529202605557139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22827730495019468403704759 34241595742529202605557139)
              ·
                refine ⟨51362393613793803908335709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34241595742529202605557139 51362393613793803908335709)
                ·
                  refine ⟨19260897605172676465625891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51362393613793803908335709 19260897605172676465625891)
                  ·
                    refine ⟨28891346407759014698438837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19260897605172676465625891 28891346407759014698438837)
                    ·
                      refine ⟨2708563725727407627978641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28891346407759014698438837 2708563725727407627978641)
                      ·
                        rfl

theorem cell23_5274909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5274909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274909 prefixEnd_5274909 := by exact prefixLift 5274909
  have htrace : WordTrace (prefixWord ++ tailWord_5274909) baseStart_5274909 baseEnd_5274909 := by
    simpa [prefixWord, tailWord_5274909, baseEnd_5274909] using wordTrace_append hprefix tailTrace_5274909
  have hstable : (prefixWord ++ tailWord_5274909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274909).length < 2 ^ (prefixWord ++ tailWord_5274909).sum := by decide
  have hdescent : baseEnd_5274909 < baseStart_5274909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274929 : List Nat := [1, 2, 2, 3, 3, 1, 4, 7]
def baseStart_5274929 : Nat := 118140960795 + 5274929 * 2 ^ 59
def prefixEnd_5274929 : Nat := 4983230072969 + 3 ^ 40 * 5274929 * 2
def baseEnd_5274929 : Nat := 100317555382981390730687

theorem tailTrace_5274929 : CollatzResearch.WordTrace tailWord_5274929 prefixEnd_5274929 100317555382981390730687 := by
  unfold tailWord_5274929
  simp only [CollatzResearch.WordTrace]
  refine ⟨192392466306840593995099841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128261644204560395996733227 192392466306840593995099841)
  ·
    refine ⟨144294349730130445496324881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192392466306840593995099841 144294349730130445496324881)
    ·
      refine ⟨108220762297597834122243661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144294349730130445496324881 108220762297597834122243661)
      ·
        refine ⟨40582785861599187795841373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108220762297597834122243661 40582785861599187795841373)
        ·
          refine ⟨15218544698099695423440515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40582785861599187795841373 15218544698099695423440515)
          ·
            refine ⟨22827817047149543135160773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15218544698099695423440515 22827817047149543135160773)
            ·
              refine ⟨4280215696340539337842645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22827817047149543135160773 4280215696340539337842645)
              ·
                refine ⟨100317555382981390730687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4280215696340539337842645 100317555382981390730687)
                ·
                  rfl

theorem cell23_5274929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 7].length) (baseStart_5274929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274929 prefixEnd_5274929 := by exact prefixLift 5274929
  have htrace : WordTrace (prefixWord ++ tailWord_5274929) baseStart_5274929 baseEnd_5274929 := by
    simpa [prefixWord, tailWord_5274929, baseEnd_5274929] using wordTrace_append hprefix tailTrace_5274929
  have hstable : (prefixWord ++ tailWord_5274929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274929).length < 2 ^ (prefixWord ++ tailWord_5274929).sum := by decide
  have hdescent : baseEnd_5274929 < baseStart_5274929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274934 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5274934 : Nat := 118140960795 + 5274934 * 2 ^ 59
def prefixEnd_5274934 : Nat := 4983230072969 + 3 ^ 40 * 5274934 * 2
def baseEnd_5274934 : Nat := 2708576562743770030166027

theorem tailTrace_5274934 : CollatzResearch.WordTrace tailWord_5274934 prefixEnd_5274934 2708576562743770030166027 := by
  unfold tailWord_5274934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024540541988904990564491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128261765781214986566021237 12024540541988904990564491)
  ·
    refine ⟨18036810812983357485846737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12024540541988904990564491 18036810812983357485846737)
    ·
      refine ⟨13527608109737518114385053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18036810812983357485846737 13527608109737518114385053)
      ·
        refine ⟨5072853041151569292894395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13527608109737518114385053 5072853041151569292894395)
        ·
          refine ⟨7609279561727353939341593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072853041151569292894395 7609279561727353939341593)
          ·
            refine ⟨5706959671295515454506195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7609279561727353939341593 5706959671295515454506195)
            ·
              refine ⟨8560439506943273181759293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706959671295515454506195 8560439506943273181759293)
              ·
                refine ⟨3210164815103727443159735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8560439506943273181759293 3210164815103727443159735)
                ·
                  refine ⟨4815247222655591164739603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210164815103727443159735 4815247222655591164739603)
                  ·
                    refine ⟨7222870833983386747109405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815247222655591164739603 7222870833983386747109405)
                    ·
                      refine ⟨2708576562743770030166027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222870833983386747109405 2708576562743770030166027)
                      ·
                        rfl

theorem cell23_5274934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5274934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274934 prefixEnd_5274934 := by exact prefixLift 5274934
  have htrace : WordTrace (prefixWord ++ tailWord_5274934) baseStart_5274934 baseEnd_5274934 := by
    simpa [prefixWord, tailWord_5274934, baseEnd_5274934] using wordTrace_append hprefix tailTrace_5274934
  have hstable : (prefixWord ++ tailWord_5274934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274934).length < 2 ^ (prefixWord ++ tailWord_5274934).sum := by decide
  have hdescent : baseEnd_5274934 < baseStart_5274934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274940 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_5274940 : Nat := 118140960795 + 5274940 * 2 ^ 59
def prefixEnd_5274940 : Nat := 4983230072969 + 3 ^ 40 * 5274940 * 2
def baseEnd_5274940 : Nat := 2708579643627697006690999

theorem tailTrace_5274940 : CollatzResearch.WordTrace tailWord_5274940 prefixEnd_5274940 2708579643627697006690999 := by
  unfold tailWord_5274940
  simp only [CollatzResearch.WordTrace]
  refine ⟨96196433754900371436875137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128261911673200495249166849 96196433754900371436875137)
  ·
    refine ⟨72147325316175278577656353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96196433754900371436875137 72147325316175278577656353)
    ·
      refine ⟨54110493987131458933242265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72147325316175278577656353 54110493987131458933242265)
      ·
        refine ⟨40582870490348594199931699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54110493987131458933242265 40582870490348594199931699)
        ·
          refine ⟨60874305735522891299897549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40582870490348594199931699 60874305735522891299897549)
          ·
            refine ⟨22827864650821084237461581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60874305735522891299897549 22827864650821084237461581)
            ·
              refine ⟨8560449244057906589048093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22827864650821084237461581 8560449244057906589048093)
              ·
                refine ⟨3210168466521714970893035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8560449244057906589048093 3210168466521714970893035)
                ·
                  refine ⟨4815252699782572456339553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210168466521714970893035 4815252699782572456339553)
                  ·
                    refine ⟨3611439524836929342254665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815252699782572456339553 3611439524836929342254665)
                    ·
                      refine ⟨2708579643627697006690999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611439524836929342254665 2708579643627697006690999)
                      ·
                        rfl

theorem cell23_5274940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_5274940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274940 prefixEnd_5274940 := by exact prefixLift 5274940
  have htrace : WordTrace (prefixWord ++ tailWord_5274940) baseStart_5274940 baseEnd_5274940 := by
    simpa [prefixWord, tailWord_5274940, baseEnd_5274940] using wordTrace_append hprefix tailTrace_5274940
  have hstable : (prefixWord ++ tailWord_5274940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274940).length < 2 ^ (prefixWord ++ tailWord_5274940).sum := by decide
  have hdescent : baseEnd_5274940 < baseStart_5274940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274952 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5274952 : Nat := 118140960795 + 5274952 * 2 ^ 59
def prefixEnd_5274952 : Nat := 4983230072969 + 3 ^ 40 * 5274952 * 2
def baseEnd_5274952 : Nat := 2708585805395550959740943

theorem tailTrace_5274952 : CollatzResearch.WordTrace tailWord_5274952 prefixEnd_5274952 2708585805395550959740943 := by
  unfold tailWord_5274952
  simp only [CollatzResearch.WordTrace]
  refine ⟨96196652592878634461593555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128262203457171512615458073 96196652592878634461593555)
  ·
    refine ⟨144294978889317951692390333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96196652592878634461593555 144294978889317951692390333)
    ·
      refine ⟨54110617083494231884646375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144294978889317951692390333 54110617083494231884646375)
      ·
        refine ⟨81165925625241347826969563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54110617083494231884646375 81165925625241347826969563)
        ·
          refine ⟨121748888437862021740454345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81165925625241347826969563 121748888437862021740454345)
          ·
            refine ⟨91311666328396516305340759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121748888437862021740454345 91311666328396516305340759)
            ·
              refine ⟨136967499492594774458011139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91311666328396516305340759 136967499492594774458011139)
              ·
                refine ⟨205451249238892161687016709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136967499492594774458011139 205451249238892161687016709)
                ·
                  refine ⟨38522109232292280316315633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205451249238892161687016709 38522109232292280316315633)
                  ·
                    refine ⟨28891581924219210237236725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38522109232292280316315633 28891581924219210237236725)
                    ·
                      refine ⟨2708585805395550959740943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28891581924219210237236725 2708585805395550959740943)
                      ·
                        rfl

theorem cell23_5274952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5274952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274952 prefixEnd_5274952 := by exact prefixLift 5274952
  have htrace : WordTrace (prefixWord ++ tailWord_5274952) baseStart_5274952 baseEnd_5274952 := by
    simpa [prefixWord, tailWord_5274952, baseEnd_5274952] using wordTrace_append hprefix tailTrace_5274952
  have hstable : (prefixWord ++ tailWord_5274952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274952).length < 2 ^ (prefixWord ++ tailWord_5274952).sum := by decide
  have hdescent : baseEnd_5274952 < baseStart_5274952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274956 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5274956 : Nat := 118140960795 + 5274956 * 2 ^ 59
def prefixEnd_5274956 : Nat := 4983230072969 + 3 ^ 40 * 5274956 * 2
def baseEnd_5274956 : Nat := 2708587859318168944090925

theorem tailTrace_5274956 : CollatzResearch.WordTrace tailWord_5274956 prefixEnd_5274956 2708587859318168944090925 := by
  unfold tailWord_5274956
  simp only [CollatzResearch.WordTrace]
  refine ⟨96196725538871388803166361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128262300718495185070888481 96196725538871388803166361)
  ·
    refine ⟨72147544154153541602374771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96196725538871388803166361 72147544154153541602374771)
    ·
      refine ⟨108221316231230312403562157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72147544154153541602374771 108221316231230312403562157)
      ·
        refine ⟨40582993586711367151335809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108221316231230312403562157 40582993586711367151335809)
        ·
          refine ⟨30437245190033525363501857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40582993586711367151335809 30437245190033525363501857)
          ·
            refine ⟨22827933892525144022626393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30437245190033525363501857 22827933892525144022626393)
            ·
              refine ⟨17120950419393858016969795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22827933892525144022626393 17120950419393858016969795)
              ·
                refine ⟨25681425629090787025454693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17120950419393858016969795 25681425629090787025454693)
                ·
                  refine ⟨4815267305454522567272755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25681425629090787025454693 4815267305454522567272755)
                  ·
                    refine ⟨7222900958181783850909133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815267305454522567272755 7222900958181783850909133)
                    ·
                      refine ⟨2708587859318168944090925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7222900958181783850909133 2708587859318168944090925)
                      ·
                        rfl

theorem cell23_5274956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5274956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274956 prefixEnd_5274956 := by exact prefixLift 5274956
  have htrace : WordTrace (prefixWord ++ tailWord_5274956) baseStart_5274956 baseEnd_5274956 := by
    simpa [prefixWord, tailWord_5274956, baseEnd_5274956] using wordTrace_append hprefix tailTrace_5274956
  have hstable : (prefixWord ++ tailWord_5274956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274956).length < 2 ^ (prefixWord ++ tailWord_5274956).sum := by decide
  have hdescent : baseEnd_5274956 < baseStart_5274956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5274983 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_5274983 : Nat := 118140960795 + 5274983 * 2 ^ 59
def prefixEnd_5274983 : Nat := 4983230072969 + 3 ^ 40 * 5274983 * 2
def baseEnd_5274983 : Nat := 2708601723295840338453301

theorem tailTrace_5274983 : CollatzResearch.WordTrace tailWord_5274983 prefixEnd_5274983 2708601723295840338453301 := by
  unfold tailWord_5274983
  simp only [CollatzResearch.WordTrace]
  refine ⟨192394435848644961217565603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128262957232429974145043735 192394435848644961217565603)
  ·
    refine ⟨288591653772967441826348405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192394435848644961217565603 288591653772967441826348405)
    ·
      refine ⟨27055467541215697671220163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288591653772967441826348405 27055467541215697671220163)
      ·
        refine ⟨40583201311823546506830245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055467541215697671220163 40583201311823546506830245)
        ·
          refine ⟨7609350245966914970030671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40583201311823546506830245 7609350245966914970030671)
          ·
            refine ⟨11414025368950372455046007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609350245966914970030671 11414025368950372455046007)
            ·
              refine ⟨17121038053425558682569011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414025368950372455046007 17121038053425558682569011)
              ·
                refine ⟨25681557080138338023853517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121038053425558682569011 25681557080138338023853517)
                ·
                  refine ⟨9630583905051876758945069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25681557080138338023853517 9630583905051876758945069)
                  ·
                    refine ⟨3611468964394453784604401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9630583905051876758945069 3611468964394453784604401)
                    ·
                      refine ⟨2708601723295840338453301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611468964394453784604401 2708601723295840338453301)
                      ·
                        rfl

theorem cell23_5274983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_5274983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5274983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5274983 prefixEnd_5274983 := by exact prefixLift 5274983
  have htrace : WordTrace (prefixWord ++ tailWord_5274983) baseStart_5274983 baseEnd_5274983 := by
    simpa [prefixWord, tailWord_5274983, baseEnd_5274983] using wordTrace_append hprefix tailTrace_5274983
  have hstable : (prefixWord ++ tailWord_5274983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5274983).length < 2 ^ (prefixWord ++ tailWord_5274983).sum := by decide
  have hdescent : baseEnd_5274983 < baseStart_5274983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5274983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275002 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_5275002 : Nat := 118140960795 + 5275002 * 2 ^ 59
def prefixEnd_5275002 : Nat := 4983230072969 + 3 ^ 40 * 5275002 * 2
def baseEnd_5275002 : Nat := 300956831047586196012857

theorem tailTrace_5275002 : CollatzResearch.WordTrace tailWord_5275002 prefixEnd_5275002 300956831047586196012857 := by
  unfold tailWord_5275002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48098782208894031865626815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128263419223717418308338173 48098782208894031865626815)
  ·
    refine ⟨72148173313341047798440223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48098782208894031865626815 72148173313341047798440223)
    ·
      refine ⟨108222259970011571697660335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72148173313341047798440223 108222259970011571697660335)
      ·
        refine ⟨162333389955017357546490503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108222259970011571697660335 162333389955017357546490503)
        ·
          refine ⟨243500084932526036319735755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162333389955017357546490503 243500084932526036319735755)
          ·
            refine ⟨365250127398789054479603633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243500084932526036319735755 365250127398789054479603633)
            ·
              refine ⟨273937595549091790859702725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365250127398789054479603633 273937595549091790859702725)
              ·
                refine ⟨51363299165454710786194261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273937595549091790859702725 51363299165454710786194261)
                ·
                  refine ⟨300956831047586196012857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51363299165454710786194261 300956831047586196012857)
                  ·
                    rfl

theorem cell23_5275002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_5275002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275002 prefixEnd_5275002 := by exact prefixLift 5275002
  have htrace : WordTrace (prefixWord ++ tailWord_5275002) baseStart_5275002 baseEnd_5275002 := by
    simpa [prefixWord, tailWord_5275002, baseEnd_5275002] using wordTrace_append hprefix tailTrace_5275002
  have hstable : (prefixWord ++ tailWord_5275002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275002).length < 2 ^ (prefixWord ++ tailWord_5275002).sum := by decide
  have hdescent : baseEnd_5275002 < baseStart_5275002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275013 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_5275013 : Nat := 118140960795 + 5275013 * 2 ^ 59
def prefixEnd_5275013 : Nat := 4983230072969 + 3 ^ 40 * 5275013 * 2
def baseEnd_5275013 : Nat := 2708617127715475221078163

theorem tailTrace_5275013 : CollatzResearch.WordTrace tailWord_5275013 prefixEnd_5275013 2708617127715475221078163 := by
  unfold tailWord_5275013
  simp only [CollatzResearch.WordTrace]
  refine ⟨192395530038536276341157693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128263686692357517560771795 192395530038536276341157693)
  ·
    refine ⟨72148323764451103627934135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192395530038536276341157693 72148323764451103627934135)
    ·
      refine ⟨108222485646676655441901203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72148323764451103627934135 108222485646676655441901203)
      ·
        refine ⟨162333728470014983162851805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108222485646676655441901203 162333728470014983162851805)
        ·
          refine ⟨60875148176255618686069427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162333728470014983162851805 60875148176255618686069427)
          ·
            refine ⟨91312722264383428029104141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60875148176255618686069427 91312722264383428029104141)
            ·
              refine ⟨34242270849143785510914053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91312722264383428029104141 34242270849143785510914053)
              ·
                refine ⟨6420425784214459783296385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34242270849143785510914053 6420425784214459783296385)
                ·
                  refine ⟨4815319338160844837472289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420425784214459783296385 4815319338160844837472289)
                  ·
                    refine ⟨3611489503620633628104217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815319338160844837472289 3611489503620633628104217)
                    ·
                      refine ⟨2708617127715475221078163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611489503620633628104217 2708617127715475221078163)
                      ·
                        rfl

theorem cell23_5275013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_5275013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275013 prefixEnd_5275013 := by exact prefixLift 5275013
  have htrace : WordTrace (prefixWord ++ tailWord_5275013) baseStart_5275013 baseEnd_5275013 := by
    simpa [prefixWord, tailWord_5275013, baseEnd_5275013] using wordTrace_append hprefix tailTrace_5275013
  have hstable : (prefixWord ++ tailWord_5275013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275013).length < 2 ^ (prefixWord ++ tailWord_5275013).sum := by decide
  have hdescent : baseEnd_5275013 < baseStart_5275013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275029 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_5275029 : Nat := 118140960795 + 5275029 * 2 ^ 59
def prefixEnd_5275029 : Nat := 4983230072969 + 3 ^ 40 * 5275029 * 2
def baseEnd_5275029 : Nat := 2708625343405947158478089

theorem tailTrace_5275029 : CollatzResearch.WordTrace tailWord_5275029 prefixEnd_5275029 2708625343405947158478089 := by
  unfold tailWord_5275029
  simp only [CollatzResearch.WordTrace]
  refine ⟨192396113606478311073740141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128264075737652207382493427 192396113606478311073740141)
  ·
    refine ⟨72148542602429366652652553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192396113606478311073740141 72148542602429366652652553)
    ·
      refine ⟨54111406951822024989489415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72148542602429366652652553 54111406951822024989489415)
      ·
        refine ⟨81167110427733037484234123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54111406951822024989489415 81167110427733037484234123)
        ·
          refine ⟨121750665641599556226351185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81167110427733037484234123 121750665641599556226351185)
          ·
            refine ⟨91312999231199667169763389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121750665641599556226351185 91312999231199667169763389)
            ·
              refine ⟨34242374711699875188661271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91312999231199667169763389 34242374711699875188661271)
              ·
                refine ⟨51363562067549812782991907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34242374711699875188661271 51363562067549812782991907)
                ·
                  refine ⟨77045343101324719174487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51363562067549812782991907 77045343101324719174487861)
                  ·
                    refine ⟨7223000915749192422608237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77045343101324719174487861 7223000915749192422608237)
                    ·
                      refine ⟨2708625343405947158478089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7223000915749192422608237 2708625343405947158478089)
                      ·
                        rfl

theorem cell23_5275029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_5275029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275029 prefixEnd_5275029 := by exact prefixLift 5275029
  have htrace : WordTrace (prefixWord ++ tailWord_5275029) baseStart_5275029 baseEnd_5275029 := by
    simpa [prefixWord, tailWord_5275029, baseEnd_5275029] using wordTrace_append hprefix tailTrace_5275029
  have hstable : (prefixWord ++ tailWord_5275029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275029).length < 2 ^ (prefixWord ++ tailWord_5275029).sum := by decide
  have hdescent : baseEnd_5275029 < baseStart_5275029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275053 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 5]
def baseStart_5275053 : Nat := 118140960795 + 5275053 * 2 ^ 59
def prefixEnd_5275053 : Nat := 4983230072969 + 3 ^ 40 * 5275053 * 2
def baseEnd_5275053 : Nat := 300959740771295007175331

theorem tailTrace_5275053 : CollatzResearch.WordTrace tailWord_5275053 prefixEnd_5275053 300959740771295007175331 := by
  unfold tailWord_5275053
  simp only [CollatzResearch.WordTrace]
  refine ⟨192396988958391363172613813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128264659305594242115075875 192396988958391363172613813)
  ·
    refine ⟨18037217714849190297432545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192396988958391363172613813 18037217714849190297432545)
    ·
      refine ⟨13527913286136892723074409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18037217714849190297432545 13527913286136892723074409)
      ·
        refine ⟨10145934964602669542305807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13527913286136892723074409 10145934964602669542305807)
        ·
          refine ⟨15218902446904004313458711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145934964602669542305807 15218902446904004313458711)
          ·
            refine ⟨22828353670356006470188067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15218902446904004313458711 22828353670356006470188067)
            ·
              refine ⟨34242530505534009705282101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22828353670356006470188067 34242530505534009705282101)
              ·
                refine ⟨3210237234893813409870197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34242530505534009705282101 3210237234893813409870197)
                ·
                  refine ⟨300959740771295007175331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210237234893813409870197 300959740771295007175331)
                  ·
                    rfl

theorem cell23_5275053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_5275053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275053 prefixEnd_5275053 := by exact prefixLift 5275053
  have htrace : WordTrace (prefixWord ++ tailWord_5275053) baseStart_5275053 baseEnd_5275053 := by
    simpa [prefixWord, tailWord_5275053, baseEnd_5275053] using wordTrace_append hprefix tailTrace_5275053
  have hstable : (prefixWord ++ tailWord_5275053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275053).length < 2 ^ (prefixWord ++ tailWord_5275053).sum := by decide
  have hdescent : baseEnd_5275053 < baseStart_5275053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275096 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_5275096 : Nat := 118140960795 + 5275096 * 2 ^ 59
def prefixEnd_5275096 : Nat := 4983230072969 + 3 ^ 40 * 5275096 * 2
def baseEnd_5275096 : Nat := 902886582203266132113427

theorem tailTrace_5275096 : CollatzResearch.WordTrace tailWord_5275096 prefixEnd_5275096 902886582203266132113427 := by
  unfold tailWord_5275096
  simp only [CollatzResearch.WordTrace]
  refine ⟨96199278648617790758214571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128265704864823721010952761 96199278648617790758214571)
  ·
    refine ⟨144298917972926686137321857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96199278648617790758214571 144298917972926686137321857)
    ·
      refine ⟨108224188479695014602991393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144298917972926686137321857 108224188479695014602991393)
      ·
        refine ⟨81168141359771260952243545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108224188479695014602991393 81168141359771260952243545)
        ·
          refine ⟨60876106019828445714182659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81168141359771260952243545 60876106019828445714182659)
          ·
            refine ⟨91314159029742668571273989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60876106019828445714182659 91314159029742668571273989)
            ·
              refine ⟨17121404818076750357113873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91314159029742668571273989 17121404818076750357113873)
              ·
                refine ⟨12841053613557562767835405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17121404818076750357113873 12841053613557562767835405)
                ·
                  refine ⟨4815395105084086037938277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12841053613557562767835405 4815395105084086037938277)
                  ·
                    refine ⟨902886582203266132113427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4815395105084086037938277 902886582203266132113427)
                    ·
                      rfl

theorem cell23_5275096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_5275096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275096 prefixEnd_5275096 := by exact prefixLift 5275096
  have htrace : WordTrace (prefixWord ++ tailWord_5275096) baseStart_5275096 baseEnd_5275096 := by
    simpa [prefixWord, tailWord_5275096, baseEnd_5275096] using wordTrace_append hprefix tailTrace_5275096
  have hstable : (prefixWord ++ tailWord_5275096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275096).length < 2 ^ (prefixWord ++ tailWord_5275096).sum := by decide
  have hdescent : baseEnd_5275096 < baseStart_5275096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275126 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_5275126 : Nat := 118140960795 + 5275126 * 2 ^ 59
def prefixEnd_5275126 : Nat := 4983230072969 + 3 ^ 40 * 5275126 * 2
def baseEnd_5275126 : Nat := 300963905669937030996127

theorem tailTrace_5275126 : CollatzResearch.WordTrace tailWord_5275126 prefixEnd_5275126 300963905669937030996127 := by
  unfold tailWord_5275126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024978217945431040001327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128266434324751264426680821 12024978217945431040001327)
  ·
    refine ⟨18037467326918146560001991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12024978217945431040001327 18037467326918146560001991)
    ·
      refine ⟨27056200990377219840002987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18037467326918146560001991 27056200990377219840002987)
      ·
        refine ⟨40584301485565829760004481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27056200990377219840002987 40584301485565829760004481)
        ·
          refine ⟨30438226114174372320003361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40584301485565829760004481 30438226114174372320003361)
          ·
            refine ⟨22828669585630779240002521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30438226114174372320003361 22828669585630779240002521)
            ·
              refine ⟨17121502189223084430001891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22828669585630779240002521 17121502189223084430001891)
              ·
                refine ⟨25682253283834626645002837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121502189223084430001891 25682253283834626645002837)
                ·
                  refine ⟨300963905669937030996127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25682253283834626645002837 300963905669937030996127)
                  ·
                    rfl

theorem cell23_5275126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_5275126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275126 prefixEnd_5275126 := by exact prefixLift 5275126
  have htrace : WordTrace (prefixWord ++ tailWord_5275126) baseStart_5275126 baseEnd_5275126 := by
    simpa [prefixWord, tailWord_5275126, baseEnd_5275126] using wordTrace_append hprefix tailTrace_5275126
  have hstable : (prefixWord ++ tailWord_5275126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275126).length < 2 ^ (prefixWord ++ tailWord_5275126).sum := by decide
  have hdescent : baseEnd_5275126 < baseStart_5275126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275130 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_5275130 : Nat := 118140960795 + 5275130 * 2 ^ 59
def prefixEnd_5275130 : Nat := 4983230072969 + 3 ^ 40 * 5275130 * 2
def baseEnd_5275130 : Nat := 902892401650683754438375

theorem tailTrace_5275130 : CollatzResearch.WordTrace tailWord_5275130 prefixEnd_5275130 902892401650683754438375 := by
  unfold tailWord_5275130
  simp only [CollatzResearch.WordTrace]
  refine ⟨48099949344778101330791711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128266531586074936882111229 48099949344778101330791711)
  ·
    refine ⟨72149924017167151996187567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48099949344778101330791711 72149924017167151996187567)
    ·
      refine ⟨108224886025750727994281351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72149924017167151996187567 108224886025750727994281351)
      ·
        refine ⟨162337329038626091991422027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108224886025750727994281351 162337329038626091991422027)
        ·
          refine ⟨243505993557939137987133041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162337329038626091991422027 243505993557939137987133041)
          ·
            refine ⟨182629495168454353490349781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243505993557939137987133041 182629495168454353490349781)
            ·
              refine ⟨4280378793010648909930073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182629495168454353490349781 4280378793010648909930073)
              ·
                refine ⟨3210284094757986682447555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280378793010648909930073 3210284094757986682447555)
                ·
                  refine ⟨4815426142136980023671333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210284094757986682447555 4815426142136980023671333)
                  ·
                    refine ⟨902892401650683754438375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4815426142136980023671333 902892401650683754438375)
                    ·
                      rfl

theorem cell23_5275130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_5275130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275130 prefixEnd_5275130 := by exact prefixLift 5275130
  have htrace : WordTrace (prefixWord ++ tailWord_5275130) baseStart_5275130 baseEnd_5275130 := by
    simpa [prefixWord, tailWord_5275130, baseEnd_5275130] using wordTrace_append hprefix tailTrace_5275130
  have hstable : (prefixWord ++ tailWord_5275130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275130).length < 2 ^ (prefixWord ++ tailWord_5275130).sum := by decide
  have hdescent : baseEnd_5275130 < baseStart_5275130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275143 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 6]
def baseStart_5275143 : Nat := 118140960795 + 5275143 * 2 ^ 59
def prefixEnd_5275143 : Nat := 4983230072969 + 3 ^ 40 * 5275143 * 2
def baseEnd_5275143 : Nat := 300964875577839968050285

theorem tailTrace_5275143 : CollatzResearch.WordTrace tailWord_5275143 prefixEnd_5275143 300964875577839968050285 := by
  unfold tailWord_5275143
  simp only [CollatzResearch.WordTrace]
  refine ⟨192400271528065308543390083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128266847685376872362260055 192400271528065308543390083)
  ·
    refine ⟨288600407292097962815085125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192400271528065308543390083 288600407292097962815085125)
    ·
      refine ⟨54112576367268368027828461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288600407292097962815085125 54112576367268368027828461)
      ·
        refine ⟨20292216137725638010435673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54112576367268368027828461 20292216137725638010435673)
        ·
          refine ⟨15219162103294228507826755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20292216137725638010435673 15219162103294228507826755)
          ·
            refine ⟨22828743154941342761740133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15219162103294228507826755 22828743154941342761740133)
            ·
              refine ⟨4280389341551501767826275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22828743154941342761740133 4280389341551501767826275)
              ·
                refine ⟨6420584012327252651739413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4280389341551501767826275 6420584012327252651739413)
                ·
                  refine ⟨300964875577839968050285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6420584012327252651739413 300964875577839968050285)
                  ·
                    rfl

theorem cell23_5275143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 6].length) (baseStart_5275143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275143 prefixEnd_5275143 := by exact prefixLift 5275143
  have htrace : WordTrace (prefixWord ++ tailWord_5275143) baseStart_5275143 baseEnd_5275143 := by
    simpa [prefixWord, tailWord_5275143, baseEnd_5275143] using wordTrace_append hprefix tailTrace_5275143
  have hstable : (prefixWord ++ tailWord_5275143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275143).length < 2 ^ (prefixWord ++ tailWord_5275143).sum := by decide
  have hdescent : baseEnd_5275143 < baseStart_5275143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275187 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 1, 1, 3]
def baseStart_5275187 : Nat := 118140960795 + 5275187 * 2 ^ 59
def prefixEnd_5275187 : Nat := 4983230072969 + 3 ^ 40 * 5275187 * 2
def baseEnd_5275187 : Nat := 2708706473349357540302363

theorem tailTrace_5275187 : CollatzResearch.WordTrace tailWord_5275187 prefixEnd_5275187 2708706473349357540302363 := by
  unfold tailWord_5275187
  simp only [CollatzResearch.WordTrace]
  refine ⟨192401876339905904057991815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128267917559937269371994543 192401876339905904057991815)
  ·
    refine ⟨288602814509858856086987723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192401876339905904057991815 288602814509858856086987723)
    ·
      refine ⟨432904221764788284130481585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288602814509858856086987723 432904221764788284130481585)
      ·
        refine ⟨324678166323591213097861189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432904221764788284130481585 324678166323591213097861189)
        ·
          refine ⟨60877156185673352455848973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324678166323591213097861189 60877156185673352455848973)
          ·
            refine ⟨22828933569627507170943365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60877156185673352455848973 22828933569627507170943365)
            ·
              refine ⟨4280425044305157594551881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22828933569627507170943365 4280425044305157594551881)
              ·
                refine ⟨3210318783228868195913911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280425044305157594551881 3210318783228868195913911)
                ·
                  refine ⟨4815478174843302293870867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210318783228868195913911 4815478174843302293870867)
                  ·
                    refine ⟨7223217262264953440806301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815478174843302293870867 7223217262264953440806301)
                    ·
                      refine ⟨2708706473349357540302363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7223217262264953440806301 2708706473349357540302363)
                      ·
                        rfl

theorem cell23_5275187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 1, 3].length) (baseStart_5275187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275187 prefixEnd_5275187 := by exact prefixLift 5275187
  have htrace : WordTrace (prefixWord ++ tailWord_5275187) baseStart_5275187 baseEnd_5275187 := by
    simpa [prefixWord, tailWord_5275187, baseEnd_5275187] using wordTrace_append hprefix tailTrace_5275187
  have hstable : (prefixWord ++ tailWord_5275187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275187).length < 2 ^ (prefixWord ++ tailWord_5275187).sum := by decide
  have hdescent : baseEnd_5275187 < baseStart_5275187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_5275209 : Nat := 118140960795 + 5275209 * 2 ^ 59
def prefixEnd_5275209 : Nat := 4983230072969 + 3 ^ 40 * 5275209 * 2
def baseEnd_5275209 : Nat := 2708717769923756454227261

theorem tailTrace_5275209 : CollatzResearch.WordTrace tailWord_5275209 prefixEnd_5275209 2708717769923756454227261 := by
  unfold tailWord_5275209
  simp only [CollatzResearch.WordTrace]
  refine ⟨192402678745826201815292681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128268452497217467876861787 192402678745826201815292681)
  ·
    refine ⟨144302009059369651361469511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192402678745826201815292681 144302009059369651361469511)
    ·
      refine ⟨216453013589054477042204267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144302009059369651361469511 216453013589054477042204267)
      ·
        refine ⟨324679520383581715563306401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216453013589054477042204267 324679520383581715563306401)
        ·
          refine ⟨243509640287686286672479801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324679520383581715563306401 243509640287686286672479801)
          ·
            refine ⟨182632230215764715004359851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243509640287686286672479801 182632230215764715004359851)
            ·
              refine ⟨273948345323647072506539777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182632230215764715004359851 273948345323647072506539777)
              ·
                refine ⟨205461258992735304379904833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273948345323647072506539777 205461258992735304379904833)
                ·
                  refine ⟨154095944244551478284928625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205461258992735304379904833 154095944244551478284928625)
                  ·
                    refine ⟨115571958183413608713696469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154095944244551478284928625 115571958183413608713696469)
                    ·
                      refine ⟨2708717769923756454227261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115571958183413608713696469 2708717769923756454227261)
                      ·
                        rfl

theorem cell23_5275209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_5275209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275209 prefixEnd_5275209 := by exact prefixLift 5275209
  have htrace : WordTrace (prefixWord ++ tailWord_5275209) baseStart_5275209 baseEnd_5275209 := by
    simpa [prefixWord, tailWord_5275209, baseEnd_5275209] using wordTrace_append hprefix tailTrace_5275209
  have hstable : (prefixWord ++ tailWord_5275209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275209).length < 2 ^ (prefixWord ++ tailWord_5275209).sum := by decide
  have hdescent : baseEnd_5275209 < baseStart_5275209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275210 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_5275210 : Nat := 118140960795 + 5275210 * 2 ^ 59
def prefixEnd_5275210 : Nat := 4983230072969 + 3 ^ 40 * 5275210 * 2
def baseEnd_5275210 : Nat := 2708718283404410950314757

theorem tailTrace_5275210 : CollatzResearch.WordTrace tailWord_5275210 prefixEnd_5275210 2708718283404410950314757 := by
  unfold tailWord_5275210
  simp only [CollatzResearch.WordTrace]
  refine ⟨48100678804705644746519771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128268476812548385990719389 48100678804705644746519771)
  ·
    refine ⟨72151018207058467119779657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48100678804705644746519771 72151018207058467119779657)
    ·
      refine ⟨54113263655293850339834743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72151018207058467119779657 54113263655293850339834743)
      ·
        refine ⟨81169895482940775509752115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54113263655293850339834743 81169895482940775509752115)
        ·
          refine ⟨121754843224411163264628173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81169895482940775509752115 121754843224411163264628173)
          ·
            refine ⟨45658066209154186224235565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121754843224411163264628173 45658066209154186224235565)
            ·
              refine ⟨17121774828432819834088337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45658066209154186224235565 17121774828432819834088337)
              ·
                refine ⟨12841331121324614875566253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17121774828432819834088337 12841331121324614875566253)
                ·
                  refine ⟨4815499170496730578337345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12841331121324614875566253 4815499170496730578337345)
                  ·
                    refine ⟨3611624377872547933753009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815499170496730578337345 3611624377872547933753009)
                    ·
                      refine ⟨2708718283404410950314757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611624377872547933753009 2708718283404410950314757)
                      ·
                        rfl

theorem cell23_5275210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_5275210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275210 prefixEnd_5275210 := by exact prefixLift 5275210
  have htrace : WordTrace (prefixWord ++ tailWord_5275210) baseStart_5275210 baseEnd_5275210 := by
    simpa [prefixWord, tailWord_5275210, baseEnd_5275210] using wordTrace_append hprefix tailTrace_5275210
  have hstable : (prefixWord ++ tailWord_5275210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275210).length < 2 ^ (prefixWord ++ tailWord_5275210).sum := by decide
  have hdescent : baseEnd_5275210 < baseStart_5275210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275216 : List Nat := [2, 1, 1, 1, 1, 3, 7, 7]
def baseStart_5275216 : Nat := 118140960795 + 5275216 * 2 ^ 59
def prefixEnd_5275216 : Nat := 4983230072969 + 3 ^ 40 * 5275216 * 2
def baseEnd_5275216 : Nat := 100323013492160663957027

theorem tailTrace_5275216 : CollatzResearch.WordTrace tailWord_5275216 prefixEnd_5275216 100323013492160663957027 := by
  unfold tailWord_5275216
  simp only [CollatzResearch.WordTrace]
  refine ⟨96201467028400421005398751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128268622704533894673865001 96201467028400421005398751)
  ·
    refine ⟨144302200542600631508098127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96201467028400421005398751 144302200542600631508098127)
    ·
      refine ⟨216453300813900947262147191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144302200542600631508098127 216453300813900947262147191)
      ·
        refine ⟨324679951220851420893220787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216453300813900947262147191 324679951220851420893220787)
        ·
          refine ⟨487019926831277131339831181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324679951220851420893220787 487019926831277131339831181)
          ·
            refine ⟨182632472561728924252436693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487019926831277131339831181 182632472561728924252436693)
            ·
              refine ⟨4280448575665521662166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182632472561728924252436693 4280448575665521662166485)
              ·
                refine ⟨100323013492160663957027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4280448575665521662166485 100323013492160663957027)
                ·
                  rfl

theorem cell23_5275216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 7].length) (baseStart_5275216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275216 prefixEnd_5275216 := by exact prefixLift 5275216
  have htrace : WordTrace (prefixWord ++ tailWord_5275216) baseStart_5275216 baseEnd_5275216 := by
    simpa [prefixWord, tailWord_5275216, baseEnd_5275216] using wordTrace_append hprefix tailTrace_5275216
  have hstable : (prefixWord ++ tailWord_5275216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275216).length < 2 ^ (prefixWord ++ tailWord_5275216).sum := by decide
  have hdescent : baseEnd_5275216 < baseStart_5275216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275219 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_5275219 : Nat := 118140960795 + 5275219 * 2 ^ 59
def prefixEnd_5275219 : Nat := 4983230072969 + 3 ^ 40 * 5275219 * 2
def baseEnd_5275219 : Nat := 2708722904730301415102215

theorem tailTrace_5275219 : CollatzResearch.WordTrace tailWord_5275219 prefixEnd_5275219 2708722904730301415102215 := by
  unfold tailWord_5275219
  simp only [CollatzResearch.WordTrace]
  refine ⟨192403043475789973523156711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128268695650526649015437807 192403043475789973523156711)
  ·
    refine ⟨288604565213684960284735067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192403043475789973523156711 288604565213684960284735067)
    ·
      refine ⟨432906847820527440427102601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288604565213684960284735067 432906847820527440427102601)
      ·
        refine ⟨324680135865395580320326951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432906847820527440427102601 324680135865395580320326951)
        ·
          refine ⟨487020203798093370480490427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324680135865395580320326951 487020203798093370480490427)
          ·
            refine ⟨730530305697140055720735641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487020203798093370480490427 730530305697140055720735641)
            ·
              refine ⟨547897729272855041790551731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730530305697140055720735641 547897729272855041790551731)
              ·
                refine ⟨821846593909282562685827597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547897729272855041790551731 821846593909282562685827597)
                ·
                  refine ⟨308192472715980961007185349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821846593909282562685827597 308192472715980961007185349)
                  ·
                    refine ⟨57786088634246430188847253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308192472715980961007185349 57786088634246430188847253)
                    ·
                      refine ⟨2708722904730301415102215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57786088634246430188847253 2708722904730301415102215)
                      ·
                        rfl

theorem cell23_5275219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_5275219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275219 prefixEnd_5275219 := by exact prefixLift 5275219
  have htrace : WordTrace (prefixWord ++ tailWord_5275219) baseStart_5275219 baseEnd_5275219 := by
    simpa [prefixWord, tailWord_5275219, baseEnd_5275219] using wordTrace_append hprefix tailTrace_5275219
  have hstable : (prefixWord ++ tailWord_5275219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275219).length < 2 ^ (prefixWord ++ tailWord_5275219).sum := by decide
  have hdescent : baseEnd_5275219 < baseStart_5275219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275334 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5275334 : Nat := 118140960795 + 5275334 * 2 ^ 59
def prefixEnd_5275334 : Nat := 4983230072969 + 3 ^ 40 * 5275334 * 2
def baseEnd_5275334 : Nat := 2708781955005568465164187

theorem tailTrace_5275334 : CollatzResearch.WordTrace tailWord_5275334 prefixEnd_5275334 2708781955005568465164187 := by
  unfold tailWord_5275334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012726183449167130112283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128271491913582232109062037 6012726183449167130112283)
  ·
    refine ⟨9019089275173750695168425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012726183449167130112283 9019089275173750695168425)
    ·
      refine ⟨6764316956380313021376319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9019089275173750695168425 6764316956380313021376319)
      ·
        refine ⟨10146475434570469532064479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764316956380313021376319 10146475434570469532064479)
        ·
          refine ⟨15219713151855704298096719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10146475434570469532064479 15219713151855704298096719)
          ·
            refine ⟨22829569727783556447145079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15219713151855704298096719 22829569727783556447145079)
            ·
              refine ⟨34244354591675334670717619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22829569727783556447145079 34244354591675334670717619)
              ·
                refine ⟨51366531887513002006076429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34244354591675334670717619 51366531887513002006076429)
                ·
                  refine ⟨19262449457817375752278661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51366531887513002006076429 19262449457817375752278661)
                  ·
                    refine ⟨3611709273340757953552249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19262449457817375752278661 3611709273340757953552249)
                    ·
                      refine ⟨2708781955005568465164187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611709273340757953552249 2708781955005568465164187)
                      ·
                        rfl

theorem cell23_5275334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5275334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275334 prefixEnd_5275334 := by exact prefixLift 5275334
  have htrace : WordTrace (prefixWord ++ tailWord_5275334) baseStart_5275334 baseEnd_5275334 := by
    simpa [prefixWord, tailWord_5275334, baseEnd_5275334] using wordTrace_append hprefix tailTrace_5275334
  have hstable : (prefixWord ++ tailWord_5275334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275334).length < 2 ^ (prefixWord ++ tailWord_5275334).sum := by decide
  have hdescent : baseEnd_5275334 < baseStart_5275334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275343 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 5, 2]
def baseStart_5275343 : Nat := 118140960795 + 5275343 * 2 ^ 59
def prefixEnd_5275343 : Nat := 4983230072969 + 3 ^ 40 * 5275343 * 2
def baseEnd_5275343 : Nat := 2708786576331458929951645

theorem tailTrace_5275343 : CollatzResearch.WordTrace tailWord_5275343 prefixEnd_5275343 2708786576331458929951645 := by
  unfold tailWord_5275343
  simp only [CollatzResearch.WordTrace]
  refine ⟨192407566127340742700670683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128271710751560495133780455 192407566127340742700670683)
  ·
    refine ⟨288611349191011114051006025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192407566127340742700670683 288611349191011114051006025)
    ·
      refine ⟨216458511893258335538254519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288611349191011114051006025 216458511893258335538254519)
      ·
        refine ⟨324687767839887503307381779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216458511893258335538254519 324687767839887503307381779)
        ·
          refine ⟨487031651759831254961072669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324687767839887503307381779 487031651759831254961072669)
          ·
            refine ⟨182636869409936720610402251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487031651759831254961072669 182636869409936720610402251)
            ·
              refine ⟨273955304114905080915603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182636869409936720610402251 273955304114905080915603377)
              ·
                refine ⟨205466478086178810686702533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273955304114905080915603377 205466478086178810686702533)
                ·
                  refine ⟨38524964641158527003756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205466478086178810686702533 38524964641158527003756725)
                  ·
                    refine ⟨3611715435108611906602193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38524964641158527003756725 3611715435108611906602193)
                    ·
                      refine ⟨2708786576331458929951645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611715435108611906602193 2708786576331458929951645)
                      ·
                        rfl

theorem cell23_5275343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5, 2].length) (baseStart_5275343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275343 prefixEnd_5275343 := by exact prefixLift 5275343
  have htrace : WordTrace (prefixWord ++ tailWord_5275343) baseStart_5275343 baseEnd_5275343 := by
    simpa [prefixWord, tailWord_5275343, baseEnd_5275343] using wordTrace_append hprefix tailTrace_5275343
  have hstable : (prefixWord ++ tailWord_5275343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275343).length < 2 ^ (prefixWord ++ tailWord_5275343).sum := by decide
  have hdescent : baseEnd_5275343 < baseStart_5275343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275353 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_5275353 : Nat := 118140960795 + 5275353 * 2 ^ 59
def prefixEnd_5275353 : Nat := 4983230072969 + 3 ^ 40 * 5275353 * 2
def baseEnd_5275353 : Nat := 902930570379334630275533

theorem tailTrace_5275353 : CollatzResearch.WordTrace tailWord_5275353 prefixEnd_5275353 902930570379334630275533 := by
  unfold tailWord_5275353
  simp only [CollatzResearch.WordTrace]
  refine ⟨192407930857304514408534713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128271953904869676272356475 192407930857304514408534713)
  ·
    refine ⟨144305948142978385806401035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192407930857304514408534713 144305948142978385806401035)
    ·
      refine ⟨216458922214467578709601553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144305948142978385806401035 216458922214467578709601553)
      ·
        refine ⟨162344191660850684032201165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216458922214467578709601553 162344191660850684032201165)
        ·
          refine ⟨60879071872819006512075437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162344191660850684032201165 60879071872819006512075437)
          ·
            refine ⟨22829651952307127442028289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60879071872819006512075437 22829651952307127442028289)
            ·
              refine ⟨17122238964230345581521217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22829651952307127442028289 17122238964230345581521217)
              ·
                refine ⟨12841679223172759186140913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17122238964230345581521217 12841679223172759186140913)
                ·
                  refine ⟨9631259417379569389605685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12841679223172759186140913 9631259417379569389605685)
                  ·
                    refine ⟨902930570379334630275533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9631259417379569389605685 902930570379334630275533)
                    ·
                      rfl

theorem cell23_5275353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_5275353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275353 prefixEnd_5275353 := by exact prefixLift 5275353
  have htrace : WordTrace (prefixWord ++ tailWord_5275353) baseStart_5275353 baseEnd_5275353 := by
    simpa [prefixWord, tailWord_5275353, baseEnd_5275353] using wordTrace_append hprefix tailTrace_5275353
  have hstable : (prefixWord ++ tailWord_5275353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275353).length < 2 ^ (prefixWord ++ tailWord_5275353).sum := by decide
  have hdescent : baseEnd_5275353 < baseStart_5275353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275367 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5275367 : Nat := 118140960795 + 5275367 * 2 ^ 59
def prefixEnd_5275367 : Nat := 4983230072969 + 3 ^ 40 * 5275367 * 2
def baseEnd_5275367 : Nat := 2708798899867166836051535

theorem tailTrace_5275367 : CollatzResearch.WordTrace tailWord_5275367 prefixEnd_5275367 2708798899867166836051535 := by
  unfold tailWord_5275367
  simp only [CollatzResearch.WordTrace]
  refine ⟨192408441479253794799544355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128272294319502529866362903 192408441479253794799544355)
  ·
    refine ⟨288612662218880692199316533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192408441479253794799544355 288612662218880692199316533)
    ·
      refine ⟨27057437083020064893685925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288612662218880692199316533 27057437083020064893685925)
      ·
        refine ⟨5073269453066262167566111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27057437083020064893685925 5073269453066262167566111)
        ·
          refine ⟨7609904179599393251349167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073269453066262167566111 7609904179599393251349167)
          ·
            refine ⟨11414856269399089877023751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609904179599393251349167 11414856269399089877023751)
            ·
              refine ⟨17122284404098634815535627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414856269399089877023751 17122284404098634815535627)
              ·
                refine ⟨25683426606147952223303441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17122284404098634815535627 25683426606147952223303441)
                ·
                  refine ⟨19262569954610964167477581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25683426606147952223303441 19262569954610964167477581)
                  ·
                    refine ⟨7223463732979111562804093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19262569954610964167477581 7223463732979111562804093)
                    ·
                      refine ⟨2708798899867166836051535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7223463732979111562804093 2708798899867166836051535)
                      ·
                        rfl

theorem cell23_5275367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5275367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275367 prefixEnd_5275367 := by exact prefixLift 5275367
  have htrace : WordTrace (prefixWord ++ tailWord_5275367) baseStart_5275367 baseEnd_5275367 := by
    simpa [prefixWord, tailWord_5275367, baseEnd_5275367] using wordTrace_append hprefix tailTrace_5275367
  have hstable : (prefixWord ++ tailWord_5275367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275367).length < 2 ^ (prefixWord ++ tailWord_5275367).sum := by decide
  have hdescent : baseEnd_5275367 < baseStart_5275367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275383 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 5, 4]
def baseStart_5275383 : Nat := 118140960795 + 5275383 * 2 ^ 59
def prefixEnd_5275383 : Nat := 4983230072969 + 3 ^ 40 * 5275383 * 2
def baseEnd_5275383 : Nat := 902935705185879591150487

theorem tailTrace_5275383 : CollatzResearch.WordTrace tailWord_5275383 prefixEnd_5275383 902935705185879591150487 := by
  unfold tailWord_5275383
  simp only [CollatzResearch.WordTrace]
  refine ⟨192409025047195829532126803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128272683364797219688084535 192409025047195829532126803)
  ·
    refine ⟨288613537570793744298190205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192409025047195829532126803 288613537570793744298190205)
    ·
      refine ⟨108230076589047654111821327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288613537570793744298190205 108230076589047654111821327)
      ·
        refine ⟨162345114883571481167731991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108230076589047654111821327 162345114883571481167731991)
        ·
          refine ⟨243517672325357221751597987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162345114883571481167731991 243517672325357221751597987)
          ·
            refine ⟨365276508488035832627396981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243517672325357221751597987 365276508488035832627396981)
            ·
              refine ⟨34244672670753359308818467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365276508488035832627396981 34244672670753359308818467)
              ·
                refine ⟨51367009006130038963227701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34244672670753359308818467 51367009006130038963227701)
                ·
                  refine ⟨4815657094324691152802597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51367009006130038963227701 4815657094324691152802597)
                  ·
                    refine ⟨902935705185879591150487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4815657094324691152802597 902935705185879591150487)
                    ·
                      rfl

theorem cell23_5275383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_5275383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275383 prefixEnd_5275383 := by exact prefixLift 5275383
  have htrace : WordTrace (prefixWord ++ tailWord_5275383) baseStart_5275383 baseEnd_5275383 := by
    simpa [prefixWord, tailWord_5275383, baseEnd_5275383] using wordTrace_append hprefix tailTrace_5275383
  have hstable : (prefixWord ++ tailWord_5275383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275383).length < 2 ^ (prefixWord ++ tailWord_5275383).sum := by decide
  have hdescent : baseEnd_5275383 < baseStart_5275383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275413 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 8]
def baseStart_5275413 : Nat := 118140960795 + 5275413 * 2 ^ 59
def prefixEnd_5275413 : Nat := 4983230072969 + 3 ^ 40 * 5275413 * 2
def baseEnd_5275413 : Nat := 300980279997474850675147

theorem tailTrace_5275413 : CollatzResearch.WordTrace tailWord_5275413 prefixEnd_5275413 300980279997474850675147 := by
  unfold tailWord_5275413
  simp only [CollatzResearch.WordTrace]
  refine ⟨192410119237087144655718893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128273412824724763103812595 192410119237087144655718893)
  ·
    refine ⟨72153794713907679245894585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192410119237087144655718893 72153794713907679245894585)
    ·
      refine ⟨54115346035430759434420939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72153794713907679245894585 54115346035430759434420939)
      ·
        refine ⟨81173019053146139151631409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54115346035430759434420939 81173019053146139151631409)
        ·
          refine ⟨60879764289859604363723557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81173019053146139151631409 60879764289859604363723557)
          ·
            refine ⟨11414955804348675818198167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60879764289859604363723557 11414955804348675818198167)
            ·
              refine ⟨17122433706523013727297251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414955804348675818198167 17122433706523013727297251)
              ·
                refine ⟨25683650559784520590945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17122433706523013727297251 25683650559784520590945877)
                ·
                  refine ⟨300980279997474850675147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25683650559784520590945877 300980279997474850675147)
                  ·
                    rfl

theorem cell23_5275413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_5275413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275413 prefixEnd_5275413 := by exact prefixLift 5275413
  have htrace : WordTrace (prefixWord ++ tailWord_5275413) baseStart_5275413 baseEnd_5275413 := by
    simpa [prefixWord, tailWord_5275413, baseEnd_5275413] using wordTrace_append hprefix tailTrace_5275413
  have hstable : (prefixWord ++ tailWord_5275413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275413).length < 2 ^ (prefixWord ++ tailWord_5275413).sum := by decide
  have hdescent : baseEnd_5275413 < baseStart_5275413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275474 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_5275474 : Nat := 118140960795 + 5275474 * 2 ^ 59
def prefixEnd_5275474 : Nat := 4983230072969 + 3 ^ 40 * 5275474 * 2
def baseEnd_5275474 : Nat := 2708853842297197917413543

theorem tailTrace_5275474 : CollatzResearch.WordTrace tailWord_5275474 prefixEnd_5275474 2708853842297197917413543 := by
  unfold tailWord_5275474
  simp only [CollatzResearch.WordTrace]
  refine ⟨48103086022466538018422369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128274896059910768049126317 48103086022466538018422369)
  ·
    refine ⟨36077314516849903513816777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48103086022466538018422369 36077314516849903513816777)
    ·
      refine ⟨27057985887637427635362583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36077314516849903513816777 27057985887637427635362583)
      ·
        refine ⟨40586978831456141453043875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27057985887637427635362583 40586978831456141453043875)
        ·
          refine ⟨60880468247184212179565813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40586978831456141453043875 60880468247184212179565813)
          ·
            refine ⟨5707543898173519891834295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60880468247184212179565813 5707543898173519891834295)
            ·
              refine ⟨8561315847260279837751443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707543898173519891834295 8561315847260279837751443)
              ·
                refine ⟨12841973770890419756627165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8561315847260279837751443 12841973770890419756627165)
                ·
                  refine ⟨4815740164083907408735187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12841973770890419756627165 4815740164083907408735187)
                  ·
                    refine ⟨7223610246125861113102781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815740164083907408735187 7223610246125861113102781)
                    ·
                      refine ⟨2708853842297197917413543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7223610246125861113102781 2708853842297197917413543)
                      ·
                        rfl

theorem cell23_5275474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_5275474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275474 prefixEnd_5275474 := by exact prefixLift 5275474
  have htrace : WordTrace (prefixWord ++ tailWord_5275474) baseStart_5275474 baseEnd_5275474 := by
    simpa [prefixWord, tailWord_5275474, baseEnd_5275474] using wordTrace_append hprefix tailTrace_5275474
  have hstable : (prefixWord ++ tailWord_5275474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275474).length < 2 ^ (prefixWord ++ tailWord_5275474).sum := by decide
  have hdescent : baseEnd_5275474 < baseStart_5275474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275497 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 3, 2, 2]
def baseStart_5275497 : Nat := 118140960795 + 5275497 * 2 ^ 59
def prefixEnd_5275497 : Nat := 4983230072969 + 3 ^ 40 * 5275497 * 2
def baseEnd_5275497 : Nat := 2708865652352251327425937

theorem tailTrace_5275497 : CollatzResearch.WordTrace tailWord_5275497 prefixEnd_5275497 2708865652352251327425937 := by
  unfold tailWord_5275497
  simp only [CollatzResearch.WordTrace]
  refine ⟨192413182968782827001776745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128275455312521884667851163 192413182968782827001776745)
  ·
    refine ⟨144309887226587120251332559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192413182968782827001776745 144309887226587120251332559)
    ·
      refine ⟨216464830839880680376998839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144309887226587120251332559 216464830839880680376998839)
      ·
        refine ⟨324697246259821020565498259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216464830839880680376998839 324697246259821020565498259)
        ·
          refine ⟨487045869389731530848247389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324697246259821020565498259 487045869389731530848247389)
          ·
            refine ⟨182642201021149324068092771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487045869389731530848247389 182642201021149324068092771)
            ·
              refine ⟨273963301531723986102139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182642201021149324068092771 273963301531723986102139157)
              ·
                refine ⟨12842029759299561848537773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 273963301531723986102139157 12842029759299561848537773)
                ·
                  refine ⟨4815761159737335693201665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12842029759299561848537773 4815761159737335693201665)
                  ·
                    refine ⟨3611820869803001769901249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815761159737335693201665 3611820869803001769901249)
                    ·
                      refine ⟨2708865652352251327425937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3611820869803001769901249 2708865652352251327425937)
                      ·
                        rfl

theorem cell23_5275497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2, 2].length) (baseStart_5275497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275497 prefixEnd_5275497 := by exact prefixLift 5275497
  have htrace : WordTrace (prefixWord ++ tailWord_5275497) baseStart_5275497 baseEnd_5275497 := by
    simpa [prefixWord, tailWord_5275497, baseEnd_5275497] using wordTrace_append hprefix tailTrace_5275497
  have hstable : (prefixWord ++ tailWord_5275497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275497).length < 2 ^ (prefixWord ++ tailWord_5275497).sum := by decide
  have hdescent : baseEnd_5275497 < baseStart_5275497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275544 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5275544 : Nat := 118140960795 + 5275544 * 2 ^ 59
def prefixEnd_5275544 : Nat := 4983230072969 + 3 ^ 40 * 5275544 * 2
def baseEnd_5275544 : Nat := 2708889785943012643538221

theorem tailTrace_5275544 : CollatzResearch.WordTrace tailWord_5275544 prefixEnd_5275544 2708889785943012643538221 := by
  unfold tailWord_5275544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96207448599806277014368843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128276598133075036019158457 96207448599806277014368843)
  ·
    refine ⟨144311172899709415521553265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96207448599806277014368843 144311172899709415521553265)
    ·
      refine ⟨108233379674782061641164949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144311172899709415521553265 108233379674782061641164949)
      ·
        refine ⟨5073439672255409139429607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108233379674782061641164949 5073439672255409139429607)
        ·
          refine ⟨7610159508383113709144411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073439672255409139429607 7610159508383113709144411)
          ·
            refine ⟨11415239262574670563716617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7610159508383113709144411 11415239262574670563716617)
            ·
              refine ⟨8561429446931002922787463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11415239262574670563716617 8561429446931002922787463)
              ·
                refine ⟨12842144170396504384181195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8561429446931002922787463 12842144170396504384181195)
                ·
                  refine ⟨19263216255594756576271793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12842144170396504384181195 19263216255594756576271793)
                  ·
                    refine ⟨14447412191696067432203845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19263216255594756576271793 14447412191696067432203845)
                    ·
                      refine ⟨2708889785943012643538221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14447412191696067432203845 2708889785943012643538221)
                      ·
                        rfl

theorem cell23_5275544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5275544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275544 prefixEnd_5275544 := by exact prefixLift 5275544
  have htrace : WordTrace (prefixWord ++ tailWord_5275544) baseStart_5275544 baseEnd_5275544 := by
    simpa [prefixWord, tailWord_5275544, baseEnd_5275544] using wordTrace_append hprefix tailTrace_5275544
  have hstable : (prefixWord ++ tailWord_5275544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275544).length < 2 ^ (prefixWord ++ tailWord_5275544).sum := by decide
  have hdescent : baseEnd_5275544 < baseStart_5275544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275563 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 6]
def baseStart_5275563 : Nat := 118140960795 + 5275563 * 2 ^ 59
def prefixEnd_5275563 : Nat := 4983230072969 + 3 ^ 40 * 5275563 * 2
def baseEnd_5275563 : Nat := 902966514025149356400211

theorem tailTrace_5275563 : CollatzResearch.WordTrace tailWord_5275563 prefixEnd_5275563 902966514025149356400211 := by
  unfold tailWord_5275563
  simp only [CollatzResearch.WordTrace]
  refine ⟨192415590186543720273679343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128277060124362480182452895 192415590186543720273679343)
  ·
    refine ⟨288623385279815580410519015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192415590186543720273679343 288623385279815580410519015)
    ·
      refine ⟨432935077919723370615778523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288623385279815580410519015 432935077919723370615778523)
      ·
        refine ⟨649402616879585055923667785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432935077919723370615778523 649402616879585055923667785)
        ·
          refine ⟨487051962659688791942750839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649402616879585055923667785 487051962659688791942750839)
          ·
            refine ⟨730577943989533187914126259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487051962659688791942750839 730577943989533187914126259)
            ·
              refine ⟨1095866915984299781871189389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730577943989533187914126259 1095866915984299781871189389)
              ·
                refine ⟨410950093494112418201696021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095866915984299781871189389 410950093494112418201696021)
                ·
                  refine ⟨19263285632536519603204501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 410950093494112418201696021 19263285632536519603204501)
                  ·
                    refine ⟨902966514025149356400211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19263285632536519603204501 902966514025149356400211)
                    ·
                      rfl

theorem cell23_5275563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_5275563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275563 prefixEnd_5275563 := by exact prefixLift 5275563
  have htrace : WordTrace (prefixWord ++ tailWord_5275563) baseStart_5275563 baseEnd_5275563 := by
    simpa [prefixWord, tailWord_5275563, baseEnd_5275563] using wordTrace_append hprefix tailTrace_5275563
  have hstable : (prefixWord ++ tailWord_5275563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275563).length < 2 ^ (prefixWord ++ tailWord_5275563).sum := by decide
  have hdescent : baseEnd_5275563 < baseStart_5275563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275581 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_5275581 : Nat := 118140960795 + 5275581 * 2 ^ 59
def prefixEnd_5275581 : Nat := 4983230072969 + 3 ^ 40 * 5275581 * 2
def baseEnd_5275581 : Nat := 2708908784727228998775551

theorem tailTrace_5275581 : CollatzResearch.WordTrace tailWord_5275581 prefixEnd_5275581 2708908784727228998775551 := by
  unfold tailWord_5275581
  simp only [CollatzResearch.WordTrace]
  refine ⟨192416246700478509347834597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128277497800319006231889731 192416246700478509347834597)
  ·
    refine ⟨36078046256339720502718987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192416246700478509347834597 36078046256339720502718987)
    ·
      refine ⟨54117069384509580754078481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36078046256339720502718987 54117069384509580754078481)
      ·
        refine ⟨40587802038382185565558861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54117069384509580754078481 40587802038382185565558861)
        ·
          refine ⟨15220425764393319587084573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40587802038382185565558861 15220425764393319587084573)
          ·
            refine ⟨5707659661647494845156715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15220425764393319587084573 5707659661647494845156715)
            ·
              refine ⟨8561489492471242267735073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707659661647494845156715 8561489492471242267735073)
              ·
                refine ⟨6421117119353431700801305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8561489492471242267735073 6421117119353431700801305)
                ·
                  refine ⟨4815837839515073775600979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6421117119353431700801305 4815837839515073775600979)
                  ·
                    refine ⟨7223756759272610663401469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815837839515073775600979 7223756759272610663401469)
                    ·
                      refine ⟨2708908784727228998775551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7223756759272610663401469 2708908784727228998775551)
                      ·
                        rfl

theorem cell23_5275581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_5275581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275581 prefixEnd_5275581 := by exact prefixLift 5275581
  have htrace : WordTrace (prefixWord ++ tailWord_5275581) baseStart_5275581 baseEnd_5275581 := by
    simpa [prefixWord, tailWord_5275581, baseEnd_5275581] using wordTrace_append hprefix tailTrace_5275581
  have hstable : (prefixWord ++ tailWord_5275581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275581).length < 2 ^ (prefixWord ++ tailWord_5275581).sum := by decide
  have hdescent : baseEnd_5275581 < baseStart_5275581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275593 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 11]
def baseStart_5275593 : Nat := 118140960795 + 5275593 * 2 ^ 59
def prefixEnd_5275593 : Nat := 4983230072969 + 3 ^ 40 * 5275593 * 2
def baseEnd_5275593 : Nat := 300990549610564772425055

theorem tailTrace_5275593 : CollatzResearch.WordTrace tailWord_5275593 prefixEnd_5275593 300990549610564772425055 := by
  unfold tailWord_5275593
  simp only [CollatzResearch.WordTrace]
  refine ⟨192416684376435035397271433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128277789584290023598180955 192416684376435035397271433)
  ·
    refine ⟨144312513282326276547953575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192416684376435035397271433 144312513282326276547953575)
    ·
      refine ⟨216468769923489414821930363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144312513282326276547953575 216468769923489414821930363)
      ·
        refine ⟨324703154885234122232895545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216468769923489414821930363 324703154885234122232895545)
        ·
          refine ⟨243527366163925591674671659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324703154885234122232895545 243527366163925591674671659)
          ·
            refine ⟨365291049245888387512007489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243527366163925591674671659 365291049245888387512007489)
            ·
              refine ⟨273968286934416290634005617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365291049245888387512007489 273968286934416290634005617)
              ·
                refine ⟨205476215200812217975504213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273968286934416290634005617 205476215200812217975504213)
                ·
                  refine ⟨300990549610564772425055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 205476215200812217975504213 300990549610564772425055)
                  ·
                    rfl

theorem cell23_5275593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_5275593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275593 prefixEnd_5275593 := by exact prefixLift 5275593
  have htrace : WordTrace (prefixWord ++ tailWord_5275593) baseStart_5275593 baseEnd_5275593 := by
    simpa [prefixWord, tailWord_5275593, baseEnd_5275593] using wordTrace_append hprefix tailTrace_5275593
  have hstable : (prefixWord ++ tailWord_5275593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275593).length < 2 ^ (prefixWord ++ tailWord_5275593).sum := by decide
  have hdescent : baseEnd_5275593 < baseStart_5275593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275600 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_5275600 : Nat := 118140960795 + 5275600 * 2 ^ 59
def prefixEnd_5275600 : Nat := 4983230072969 + 3 ^ 40 * 5275600 * 2
def baseEnd_5275600 : Nat := 2708918540859664424437963

theorem tailTrace_5275600 : CollatzResearch.WordTrace tailWord_5275600 prefixEnd_5275600 2708918540859664424437963 := by
  unfold tailWord_5275600
  simp only [CollatzResearch.WordTrace]
  refine ⟨96208469843704837796388127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128277959791606450395184169 96208469843704837796388127)
  ·
    refine ⟨144312704765557256694582191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96208469843704837796388127 144312704765557256694582191)
    ·
      refine ⟨216469057148335885041873287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144312704765557256694582191 216469057148335885041873287)
      ·
        refine ⟨324703585722503827562809931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216469057148335885041873287 324703585722503827562809931)
        ·
          refine ⟨487055378583755741344214897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324703585722503827562809931 487055378583755741344214897)
          ·
            refine ⟨365291533937816806008161173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487055378583755741344214897 365291533937816806008161173)
            ·
              refine ⟨17123040653335162781632555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 365291533937816806008161173 17123040653335162781632555)
              ·
                refine ⟨25684560980002744172448833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17123040653335162781632555 25684560980002744172448833)
                ·
                  refine ⟨19263420735002058129336625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25684560980002744172448833 19263420735002058129336625)
                  ·
                    refine ⟨14447565551251543597002469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19263420735002058129336625 14447565551251543597002469)
                    ·
                      refine ⟨2708918540859664424437963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14447565551251543597002469 2708918540859664424437963)
                      ·
                        rfl

theorem cell23_5275600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_5275600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275600 prefixEnd_5275600 := by exact prefixLift 5275600
  have htrace : WordTrace (prefixWord ++ tailWord_5275600) baseStart_5275600 baseEnd_5275600 := by
    simpa [prefixWord, tailWord_5275600, baseEnd_5275600] using wordTrace_append hprefix tailTrace_5275600
  have hstable : (prefixWord ++ tailWord_5275600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275600).length < 2 ^ (prefixWord ++ tailWord_5275600).sum := by decide
  have hdescent : baseEnd_5275600 < baseStart_5275600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275640 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_5275640 : Nat := 118140960795 + 5275640 * 2 ^ 59
def prefixEnd_5275640 : Nat := 4983230072969 + 3 ^ 40 * 5275640 * 2
def baseEnd_5275640 : Nat := 902979693361948089312593

theorem tailTrace_5275640 : CollatzResearch.WordTrace tailWord_5275640 prefixEnd_5275640 902979693361948089312593 := by
  unfold tailWord_5275640
  simp only [CollatzResearch.WordTrace]
  refine ⟨96209199303632381212116187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128278932404843174949488249 96209199303632381212116187)
  ·
    refine ⟨144313798955448571818174281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96209199303632381212116187 144313798955448571818174281)
    ·
      refine ⟨108235349216586428863630711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144313798955448571818174281 108235349216586428863630711)
      ·
        refine ⟨162353023824879643295446067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108235349216586428863630711 162353023824879643295446067)
        ·
          refine ⟨243529535737319464943169101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162353023824879643295446067 243529535737319464943169101)
          ·
            refine ⟨91323575901494799353688413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243529535737319464943169101 91323575901494799353688413)
            ·
              refine ⟨34246340963060549757633155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91323575901494799353688413 34246340963060549757633155)
              ·
                refine ⟨51369511444590824636449733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34246340963060549757633155 51369511444590824636449733)
                ·
                  refine ⟨9631783395860779619334325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51369511444590824636449733 9631783395860779619334325)
                  ·
                    refine ⟨902979693361948089312593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9631783395860779619334325 902979693361948089312593)
                    ·
                      rfl

theorem cell23_5275640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_5275640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275640 prefixEnd_5275640 := by exact prefixLift 5275640
  have htrace : WordTrace (prefixWord ++ tailWord_5275640) baseStart_5275640 baseEnd_5275640 := by
    simpa [prefixWord, tailWord_5275640, baseEnd_5275640] using wordTrace_append hprefix tailTrace_5275640
  have hstable : (prefixWord ++ tailWord_5275640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275640).length < 2 ^ (prefixWord ++ tailWord_5275640).sum := by decide
  have hdescent : baseEnd_5275640 < baseStart_5275640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275644 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 5]
def baseStart_5275644 : Nat := 118140960795 + 5275644 * 2 ^ 59
def prefixEnd_5275644 : Nat := 4983230072969 + 3 ^ 40 * 5275644 * 2
def baseEnd_5275644 : Nat := 300993459334273583587529

theorem tailTrace_5275644 : CollatzResearch.WordTrace tailWord_5275644 prefixEnd_5275644 300993459334273583587529 := by
  unfold tailWord_5275644
  simp only [CollatzResearch.WordTrace]
  refine ⟨96209272249625135553688993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128279029666166847404918657 96209272249625135553688993)
  ·
    refine ⟨72156954187218851665266745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96209272249625135553688993 72156954187218851665266745)
    ·
      refine ⟨54117715640414138748950059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72156954187218851665266745 54117715640414138748950059)
      ·
        refine ⟨81176573460621208123425089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54117715640414138748950059 81176573460621208123425089)
        ·
          refine ⟨60882430095465906092568817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81176573460621208123425089 60882430095465906092568817)
          ·
            refine ⟨45661822571599429569426613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60882430095465906092568817 45661822571599429569426613)
            ·
              refine ⟨4280795866087446522133745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45661822571599429569426613 4280795866087446522133745)
              ·
                refine ⟨3210596899565584891600309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280795866087446522133745 3210596899565584891600309)
                ·
                  refine ⟨300993459334273583587529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210596899565584891600309 300993459334273583587529)
                  ·
                    rfl

theorem cell23_5275644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_5275644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275644 prefixEnd_5275644 := by exact prefixLift 5275644
  have htrace : WordTrace (prefixWord ++ tailWord_5275644) baseStart_5275644 baseEnd_5275644 := by
    simpa [prefixWord, tailWord_5275644, baseEnd_5275644] using wordTrace_append hprefix tailTrace_5275644
  have hstable : (prefixWord ++ tailWord_5275644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275644).length < 2 ^ (prefixWord ++ tailWord_5275644).sum := by decide
  have hdescent : baseEnd_5275644 < baseStart_5275644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275694 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5275694 : Nat := 118140960795 + 5275694 * 2 ^ 59
def prefixEnd_5275694 : Nat := 4983230072969 + 3 ^ 40 * 5275694 * 2
def baseEnd_5275694 : Nat := 2708966808041187056662531

theorem tailTrace_5275694 : CollatzResearch.WordTrace tailWord_5275694 prefixEnd_5275694 2708966808041187056662531 := by
  unfold tailWord_5275694
  simp only [CollatzResearch.WordTrace]
  refine ⟨24052546018633641205837267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128280245432712753097798757 24052546018633641205837267)
  ·
    refine ⟨36078819027950461808755901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24052546018633641205837267 36078819027950461808755901)
    ·
      refine ⟨13529557135481423178283463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36078819027950461808755901 13529557135481423178283463)
      ·
        refine ⟨20294335703222134767425195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13529557135481423178283463 20294335703222134767425195)
        ·
          refine ⟨30441503554833202151137793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20294335703222134767425195 30441503554833202151137793)
          ·
            refine ⟨22831127666124901613353345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30441503554833202151137793 22831127666124901613353345)
            ·
              refine ⟨17123345749593676210015009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22831127666124901613353345 17123345749593676210015009)
              ·
                refine ⟨12842509312195257157511257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17123345749593676210015009 12842509312195257157511257)
                ·
                  refine ⟨9631881984146442868133443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12842509312195257157511257 9631881984146442868133443)
                  ·
                    refine ⟨14447822976219664302200165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9631881984146442868133443 14447822976219664302200165)
                    ·
                      refine ⟨2708966808041187056662531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14447822976219664302200165 2708966808041187056662531)
                      ·
                        rfl

theorem cell23_5275694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5275694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275694 prefixEnd_5275694 := by exact prefixLift 5275694
  have htrace : WordTrace (prefixWord ++ tailWord_5275694) baseStart_5275694 baseEnd_5275694 := by
    simpa [prefixWord, tailWord_5275694, baseEnd_5275694] using wordTrace_append hprefix tailTrace_5275694
  have hstable : (prefixWord ++ tailWord_5275694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275694).length < 2 ^ (prefixWord ++ tailWord_5275694).sum := by decide
  have hdescent : baseEnd_5275694 < baseStart_5275694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275720 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5275720 : Nat := 118140960795 + 5275720 * 2 ^ 59
def prefixEnd_5275720 : Nat := 4983230072969 + 3 ^ 40 * 5275720 * 2
def baseEnd_5275720 : Nat := 2708980158538203954937411

theorem tailTrace_5275720 : CollatzResearch.WordTrace tailWord_5275720 prefixEnd_5275720 2708980158538203954937411 := by
  unfold tailWord_5275720
  simp only [CollatzResearch.WordTrace]
  refine ⟨96210658223487468043572307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128280877631316624058096409 96210658223487468043572307)
  ·
    refine ⟨144315987335231202065358461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96210658223487468043572307 144315987335231202065358461)
    ·
      refine ⟨54118495250711700774509423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144315987335231202065358461 54118495250711700774509423)
      ·
        refine ⟨81177742876067551161764135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54118495250711700774509423 81177742876067551161764135)
        ·
          refine ⟨121766614314101326742646203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81177742876067551161764135 121766614314101326742646203)
          ·
            refine ⟨182649921471151990113969305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121766614314101326742646203 182649921471151990113969305)
            ·
              refine ⟨136987441103363992585476979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182649921471151990113969305 136987441103363992585476979)
              ·
                refine ⟨205481161655045988878215469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136987441103363992585476979 205481161655045988878215469)
                ·
                  refine ⟨77055435620642245829330801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205481161655045988878215469 77055435620642245829330801)
                  ·
                    refine ⟨57791576715481684371998101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77055435620642245829330801 57791576715481684371998101)
                    ·
                      refine ⟨2708980158538203954937411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57791576715481684371998101 2708980158538203954937411)
                      ·
                        rfl

theorem cell23_5275720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5275720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275720 prefixEnd_5275720 := by exact prefixLift 5275720
  have htrace : WordTrace (prefixWord ++ tailWord_5275720) baseStart_5275720 baseEnd_5275720 := by
    simpa [prefixWord, tailWord_5275720, baseEnd_5275720] using wordTrace_append hprefix tailTrace_5275720
  have hstable : (prefixWord ++ tailWord_5275720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275720).length < 2 ^ (prefixWord ++ tailWord_5275720).sum := by decide
  have hdescent : baseEnd_5275720 < baseStart_5275720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275761 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_5275761 : Nat := 118140960795 + 5275761 * 2 ^ 59
def prefixEnd_5275761 : Nat := 4983230072969 + 3 ^ 40 * 5275761 * 2
def baseEnd_5275761 : Nat := 2709001211245038294524723

theorem tailTrace_5275761 : CollatzResearch.WordTrace tailWord_5275761 prefixEnd_5275761 2709001211245038294524723 := by
  unfold tailWord_5275761
  simp only [CollatzResearch.WordTrace]
  refine ⟨192422811839826400089387137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128281874559884266726258091 192422811839826400089387137)
  ·
    refine ⟨144317108879869800067040353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192422811839826400089387137 144317108879869800067040353)
    ·
      refine ⟨108237831659902350050280265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144317108879869800067040353 108237831659902350050280265)
      ·
        refine ⟨81178373744926762537710199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108237831659902350050280265 81178373744926762537710199)
        ·
          refine ⟨121767560617390143806565299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81178373744926762537710199 121767560617390143806565299)
          ·
            refine ⟨182651340926085215709847949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121767560617390143806565299 182651340926085215709847949)
            ·
              refine ⟨68494252847281955891192981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182651340926085215709847949 68494252847281955891192981)
              ·
                refine ⟨3210668102216341682399671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68494252847281955891192981 3210668102216341682399671)
                ·
                  refine ⟨4816002153324512523599507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210668102216341682399671 4816002153324512523599507)
                  ·
                    refine ⟨7224003229986768785399261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816002153324512523599507 7224003229986768785399261)
                    ·
                      refine ⟨2709001211245038294524723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224003229986768785399261 2709001211245038294524723)
                      ·
                        rfl

theorem cell23_5275761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_5275761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275761 prefixEnd_5275761 := by exact prefixLift 5275761
  have htrace : WordTrace (prefixWord ++ tailWord_5275761) baseStart_5275761 baseEnd_5275761 := by
    simpa [prefixWord, tailWord_5275761, baseEnd_5275761] using wordTrace_append hprefix tailTrace_5275761
  have hstable : (prefixWord ++ tailWord_5275761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275761).length < 2 ^ (prefixWord ++ tailWord_5275761).sum := by decide
  have hdescent : baseEnd_5275761 < baseStart_5275761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275794 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5275794 : Nat := 118140960795 + 5275794 * 2 ^ 59
def prefixEnd_5275794 : Nat := 4983230072969 + 3 ^ 40 * 5275794 * 2
def baseEnd_5275794 : Nat := 903006052035545555137357

theorem tailTrace_5275794 : CollatzResearch.WordTrace tailWord_5275794 prefixEnd_5275794 903006052035545555137357 := by
  unfold tailWord_5275794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48106003862176711681334609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128282676965804564483558957 48106003862176711681334609)
  ·
    refine ⟨36079502896632533761000957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48106003862176711681334609 36079502896632533761000957)
    ·
      refine ⟨13529813586237200160375359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36079502896632533761000957 13529813586237200160375359)
      ·
        refine ⟨20294720379355800240563039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13529813586237200160375359 20294720379355800240563039)
        ·
          refine ⟨30442080569033700360844559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20294720379355800240563039 30442080569033700360844559)
          ·
            refine ⟨45663120853550550541266839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30442080569033700360844559 45663120853550550541266839)
            ·
              refine ⟨68494681280325825811900259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45663120853550550541266839 68494681280325825811900259)
              ·
                refine ⟨102742021920488738717850389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68494681280325825811900259 102742021920488738717850389)
                ·
                  refine ⟨4816032277522909627399237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102742021920488738717850389 4816032277522909627399237)
                  ·
                    refine ⟨903006052035545555137357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816032277522909627399237 903006052035545555137357)
                    ·
                      rfl

theorem cell23_5275794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5275794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275794 prefixEnd_5275794 := by exact prefixLift 5275794
  have htrace : WordTrace (prefixWord ++ tailWord_5275794) baseStart_5275794 baseEnd_5275794 := by
    simpa [prefixWord, tailWord_5275794, baseEnd_5275794] using wordTrace_append hprefix tailTrace_5275794
  have hstable : (prefixWord ++ tailWord_5275794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275794).length < 2 ^ (prefixWord ++ tailWord_5275794).sum := by decide
  have hdescent : baseEnd_5275794 < baseStart_5275794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275797 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_5275797 : Nat := 118140960795 + 5275797 * 2 ^ 59
def prefixEnd_5275797 : Nat := 4983230072969 + 3 ^ 40 * 5275797 * 2
def baseEnd_5275797 : Nat := 2709019696548600153674557

theorem tailTrace_5275797 : CollatzResearch.WordTrace tailWord_5275797 prefixEnd_5275797 2709019696548600153674557 := by
  unfold tailWord_5275797
  simp only [CollatzResearch.WordTrace]
  refine ⟨192424124867695978237697645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128282749911797318825131763 192424124867695978237697645)
  ·
    refine ⟨72159046825385991839136617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192424124867695978237697645 72159046825385991839136617)
    ·
      refine ⟨54119285119039493879352463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72159046825385991839136617 54119285119039493879352463)
      ·
        refine ⟨81178927678559240819028695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54119285119039493879352463 81178927678559240819028695)
        ·
          refine ⟨121768391517838861228543043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81178927678559240819028695 121768391517838861228543043)
          ·
            refine ⟨182652587276758291842814565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121768391517838861228543043 182652587276758291842814565)
            ·
              refine ⟨34247360114392179720527731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182652587276758291842814565 34247360114392179720527731)
              ·
                refine ⟨51371040171588269580791597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34247360114392179720527731 51371040171588269580791597)
                ·
                  refine ⟨19264140064345601092796849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51371040171588269580791597 19264140064345601092796849)
                  ·
                    refine ⟨14448105048259200819597637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19264140064345601092796849 14448105048259200819597637)
                    ·
                      refine ⟨2709019696548600153674557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14448105048259200819597637 2709019696548600153674557)
                      ·
                        rfl

theorem cell23_5275797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_5275797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275797 prefixEnd_5275797 := by exact prefixLift 5275797
  have htrace : WordTrace (prefixWord ++ tailWord_5275797) baseStart_5275797 baseEnd_5275797 := by
    simpa [prefixWord, tailWord_5275797, baseEnd_5275797] using wordTrace_append hprefix tailTrace_5275797
  have hstable : (prefixWord ++ tailWord_5275797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275797).length < 2 ^ (prefixWord ++ tailWord_5275797).sum := by decide
  have hdescent : baseEnd_5275797 < baseStart_5275797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275804 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5275804 : Nat := 118140960795 + 5275804 * 2 ^ 59
def prefixEnd_5275804 : Nat := 4983230072969 + 3 ^ 40 * 5275804 * 2
def baseEnd_5275804 : Nat := 2709023290913181626287025

theorem tailTrace_5275804 : CollatzResearch.WordTrace tailWord_5275804 prefixEnd_5275804 2709023290913181626287025 := by
  unfold tailWord_5275804
  simp only [CollatzResearch.WordTrace]
  refine ⟨96212190089335309216601233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128282920119113745622134977 96212190089335309216601233)
  ·
    refine ⟨72159142567001481912450925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96212190089335309216601233 72159142567001481912450925)
    ·
      refine ⟨27059678462625555717169097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72159142567001481912450925 27059678462625555717169097)
      ·
        refine ⟨20294758846969166787876823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27059678462625555717169097 20294758846969166787876823)
        ·
          refine ⟨30442138270453750181815235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20294758846969166787876823 30442138270453750181815235)
          ·
            refine ⟨45663207405680625272722853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30442138270453750181815235 45663207405680625272722853)
            ·
              refine ⟨8561851388565117238635535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45663207405680625272722853 8561851388565117238635535)
              ·
                refine ⟨12842777082847675857953303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8561851388565117238635535 12842777082847675857953303)
                ·
                  refine ⟨19264165624271513786929955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12842777082847675857953303 19264165624271513786929955)
                  ·
                    refine ⟨28896248436407270680394933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19264165624271513786929955 28896248436407270680394933)
                    ·
                      refine ⟨2709023290913181626287025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28896248436407270680394933 2709023290913181626287025)
                      ·
                        rfl

theorem cell23_5275804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5275804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275804 prefixEnd_5275804 := by exact prefixLift 5275804
  have htrace : WordTrace (prefixWord ++ tailWord_5275804) baseStart_5275804 baseEnd_5275804 := by
    simpa [prefixWord, tailWord_5275804, baseEnd_5275804] using wordTrace_append hprefix tailTrace_5275804
  have hstable : (prefixWord ++ tailWord_5275804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275804).length < 2 ^ (prefixWord ++ tailWord_5275804).sum := by decide
  have hdescent : baseEnd_5275804 < baseStart_5275804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275807 : List Nat := [1, 1, 2, 6, 1, 1, 11]
def baseStart_5275807 : Nat := 118140960795 + 5275807 * 2 ^ 59
def prefixEnd_5275807 : Nat := 4983230072969 + 3 ^ 40 * 5275807 * 2
def baseEnd_5275807 : Nat := 33444751004384507587031

theorem tailTrace_5275807 : CollatzResearch.WordTrace tailWord_5275807 prefixEnd_5275807 33444751004384507587031 := by
  unfold tailWord_5275807
  simp only [CollatzResearch.WordTrace]
  refine ⟨192424489597659749945561675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128282993065106499963707783 192424489597659749945561675)
  ·
    refine ⟨288636734396489624918342513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192424489597659749945561675 288636734396489624918342513)
    ·
      refine ⟨216477550797367218688756885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288636734396489624918342513 216477550797367218688756885)
      ·
        refine ⟨10147385193626588376035479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 216477550797367218688756885 10147385193626588376035479)
        ·
          refine ⟨15221077790439882564053219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10147385193626588376035479 15221077790439882564053219)
          ·
            refine ⟨22831616685659823846079829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15221077790439882564053219 22831616685659823846079829)
            ·
              refine ⟨33444751004384507587031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22831616685659823846079829 33444751004384507587031)
              ·
                rfl

theorem cell23_5275807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 11].length) (baseStart_5275807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275807 prefixEnd_5275807 := by exact prefixLift 5275807
  have htrace : WordTrace (prefixWord ++ tailWord_5275807) baseStart_5275807 baseEnd_5275807 := by
    simpa [prefixWord, tailWord_5275807, baseEnd_5275807] using wordTrace_append hprefix tailTrace_5275807
  have hstable : (prefixWord ++ tailWord_5275807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275807).length < 2 ^ (prefixWord ++ tailWord_5275807).sum := by decide
  have hdescent : baseEnd_5275807 < baseStart_5275807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275869 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5275869 : Nat := 118140960795 + 5275869 * 2 ^ 59
def prefixEnd_5275869 : Nat := 4983230072969 + 3 ^ 40 * 5275869 * 2
def baseEnd_5275869 : Nat := 2709056667155723871974227

theorem tailTrace_5275869 : CollatzResearch.WordTrace tailWord_5275869 prefixEnd_5275869 2709056667155723871974227 := by
  unfold tailWord_5275869
  simp only [CollatzResearch.WordTrace]
  refine ⟨192426750923435134534318661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128284500615623423022879107 192426750923435134534318661)
  ·
    refine ⟨36080015798144087725184749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192426750923435134534318661 36080015798144087725184749)
    ·
      refine ⟨13530005924304032896944281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36080015798144087725184749 13530005924304032896944281)
      ·
        refine ⟨10147504443228024672708211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13530005924304032896944281 10147504443228024672708211)
        ·
          refine ⟨15221256664842037009062317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10147504443228024672708211 15221256664842037009062317)
          ·
            refine ⟨5707971249315763878398369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15221256664842037009062317 5707971249315763878398369)
            ·
              refine ⟨4280978436986822908798777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707971249315763878398369 4280978436986822908798777)
              ·
                refine ⟨3210733827740117181599083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280978436986822908798777 3210733827740117181599083)
                ·
                  refine ⟨4816100741610175772398625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210733827740117181599083 4816100741610175772398625)
                  ·
                    refine ⟨3612075556207631829298969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816100741610175772398625 3612075556207631829298969)
                    ·
                      refine ⟨2709056667155723871974227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612075556207631829298969 2709056667155723871974227)
                      ·
                        rfl

theorem cell23_5275869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5275869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275869 prefixEnd_5275869 := by exact prefixLift 5275869
  have htrace : WordTrace (prefixWord ++ tailWord_5275869) baseStart_5275869 baseEnd_5275869 := by
    simpa [prefixWord, tailWord_5275869, baseEnd_5275869] using wordTrace_append hprefix tailTrace_5275869
  have hstable : (prefixWord ++ tailWord_5275869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275869).length < 2 ^ (prefixWord ++ tailWord_5275869).sum := by decide
  have hdescent : baseEnd_5275869 < baseStart_5275869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275891 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 4, 2]
def baseStart_5275891 : Nat := 118140960795 + 5275891 * 2 ^ 59
def prefixEnd_5275891 : Nat := 4983230072969 + 3 ^ 40 * 5275891 * 2
def baseEnd_5275891 : Nat := 2709067963730122785899125

theorem tailTrace_5275891 : CollatzResearch.WordTrace tailWord_5275891 prefixEnd_5275891 2709067963730122785899125 := by
  unfold tailWord_5275891
  simp only [CollatzResearch.WordTrace]
  refine ⟨192427553329355432291619527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128285035552903621527746351 192427553329355432291619527)
  ·
    refine ⟨288641329994033148437429291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192427553329355432291619527 288641329994033148437429291)
    ·
      refine ⟨432961994991049722656143937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288641329994033148437429291 432961994991049722656143937)
      ·
        refine ⟨324721496243287291992107953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432961994991049722656143937 324721496243287291992107953)
        ·
          refine ⟨243541122182465468994080965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324721496243287291992107953 243541122182465468994080965)
          ·
            refine ⟨45663960409212275436390181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243541122182465468994080965 45663960409212275436390181)
            ·
              refine ⟨8561992576727301644323159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45663960409212275436390181 8561992576727301644323159)
              ·
                refine ⟨12842988865090952466484739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8561992576727301644323159 12842988865090952466484739)
                ·
                  refine ⟨19264483297636428699727109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12842988865090952466484739 19264483297636428699727109)
                  ·
                    refine ⟨3612090618306830381198833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19264483297636428699727109 3612090618306830381198833)
                    ·
                      refine ⟨2709067963730122785899125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612090618306830381198833 2709067963730122785899125)
                      ·
                        rfl

theorem cell23_5275891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4, 2].length) (baseStart_5275891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275891 prefixEnd_5275891 := by exact prefixLift 5275891
  have htrace : WordTrace (prefixWord ++ tailWord_5275891) baseStart_5275891 baseEnd_5275891 := by
    simpa [prefixWord, tailWord_5275891, baseEnd_5275891] using wordTrace_append hprefix tailTrace_5275891
  have hstable : (prefixWord ++ tailWord_5275891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275891).length < 2 ^ (prefixWord ++ tailWord_5275891).sum := by decide
  have hdescent : baseEnd_5275891 < baseStart_5275891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275894 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5275894 : Nat := 118140960795 + 5275894 * 2 ^ 59
def prefixEnd_5275894 : Nat := 4983230072969 + 3 ^ 40 * 5275894 * 2
def baseEnd_5275894 : Nat := 2709069504172086274161611

theorem tailTrace_5275894 : CollatzResearch.WordTrace tailWord_5275894 prefixEnd_5275894 2709069504172086274161611 := by
  unfold tailWord_5275894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026728921771535237748671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128285108498896375869319157 12026728921771535237748671)
  ·
    refine ⟨18040093382657302856623007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12026728921771535237748671 18040093382657302856623007)
    ·
      refine ⟨27060140073985954284934511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18040093382657302856623007 27060140073985954284934511)
      ·
        refine ⟨40590210110978931427401767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27060140073985954284934511 40590210110978931427401767)
        ·
          refine ⟨60885315166468397141102651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40590210110978931427401767 60885315166468397141102651)
          ·
            refine ⟨91327972749702595711653977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60885315166468397141102651 91327972749702595711653977)
            ·
              refine ⟨68495979562276946783740483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91327972749702595711653977 68495979562276946783740483)
              ·
                refine ⟨102743969343415420175610725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68495979562276946783740483 102743969343415420175610725)
                ·
                  refine ⟨19264494251890391282927011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102743969343415420175610725 19264494251890391282927011)
                  ·
                    refine ⟨28896741377835586924390517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19264494251890391282927011 28896741377835586924390517)
                    ·
                      refine ⟨2709069504172086274161611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28896741377835586924390517 2709069504172086274161611)
                      ·
                        rfl

theorem cell23_5275894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5275894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275894 prefixEnd_5275894 := by exact prefixLift 5275894
  have htrace : WordTrace (prefixWord ++ tailWord_5275894) baseStart_5275894 baseEnd_5275894 := by
    simpa [prefixWord, tailWord_5275894, baseEnd_5275894] using wordTrace_append hprefix tailTrace_5275894
  have hstable : (prefixWord ++ tailWord_5275894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275894).length < 2 ^ (prefixWord ++ tailWord_5275894).sum := by decide
  have hdescent : baseEnd_5275894 < baseStart_5275894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5275964 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_5275964 : Nat := 118140960795 + 5275964 * 2 ^ 59
def prefixEnd_5275964 : Nat := 4983230072969 + 3 ^ 40 * 5275964 * 2
def baseEnd_5275964 : Nat := 2709105447817901000286289

theorem tailTrace_5275964 : CollatzResearch.WordTrace tailWord_5275964 prefixEnd_5275964 2709105447817901000286289 := by
  unfold tailWord_5275964
  simp only [CollatzResearch.WordTrace]
  refine ⟨96215107929045482879513473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128286810572060643839351297 96215107929045482879513473)
  ·
    refine ⟨72161330946784112159635105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96215107929045482879513473 72161330946784112159635105)
    ·
      refine ⟨54120998210088084119726329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72161330946784112159635105 54120998210088084119726329)
      ·
        refine ⟨40590748657566063089794747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54120998210088084119726329 40590748657566063089794747)
        ·
          refine ⟨60886122986349094634692121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40590748657566063089794747 60886122986349094634692121)
          ·
            refine ⟨45664592239761820976019091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60886122986349094634692121 45664592239761820976019091)
            ·
              refine ⟨68496888359642731464028637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45664592239761820976019091 68496888359642731464028637)
              ·
                refine ⟨25686333134866024299010739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68496888359642731464028637 25686333134866024299010739)
                ·
                  refine ⟨38529499702299036448516109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25686333134866024299010739 38529499702299036448516109)
                  ·
                    refine ⟨14448562388362138668193541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38529499702299036448516109 14448562388362138668193541)
                    ·
                      refine ⟨2709105447817901000286289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14448562388362138668193541 2709105447817901000286289)
                      ·
                        rfl

theorem cell23_5275964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_5275964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5275964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5275964 prefixEnd_5275964 := by exact prefixLift 5275964
  have htrace : WordTrace (prefixWord ++ tailWord_5275964) baseStart_5275964 baseEnd_5275964 := by
    simpa [prefixWord, tailWord_5275964, baseEnd_5275964] using wordTrace_append hprefix tailTrace_5275964
  have hstable : (prefixWord ++ tailWord_5275964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5275964).length < 2 ^ (prefixWord ++ tailWord_5275964).sum := by decide
  have hdescent : baseEnd_5275964 < baseStart_5275964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5275964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276018 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5276018 : Nat := 118140960795 + 5276018 * 2 ^ 59
def prefixEnd_5276018 : Nat := 4983230072969 + 3 ^ 40 * 5276018 * 2
def baseEnd_5276018 : Nat := 2709133175773243789011041

theorem tailTrace_5276018 : CollatzResearch.WordTrace tailWord_5276018 prefixEnd_5276018 2709133175773243789011041 := by
  unfold tailWord_5276018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48108046349973833245373177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128288123599930221987661805 48108046349973833245373177)
  ·
    refine ⟨36081034762480374934029883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48108046349973833245373177 36081034762480374934029883)
    ·
      refine ⟨54121552143720562401044825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36081034762480374934029883 54121552143720562401044825)
      ·
        refine ⟨40591164107790421800783619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54121552143720562401044825 40591164107790421800783619)
        ·
          refine ⟨60886746161685632701175429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40591164107790421800783619 60886746161685632701175429)
          ·
            refine ⟨11416264905316056131470393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60886746161685632701175429 11416264905316056131470393)
            ·
              refine ⟨8562198678987042098602795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11416264905316056131470393 8562198678987042098602795)
              ·
                refine ⟨12843298018480563147904193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562198678987042098602795 12843298018480563147904193)
                ·
                  refine ⟨9632473513860422360928145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12843298018480563147904193 9632473513860422360928145)
                  ·
                    refine ⟨7224355135395316770696109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9632473513860422360928145 7224355135395316770696109)
                    ·
                      refine ⟨2709133175773243789011041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224355135395316770696109 2709133175773243789011041)
                      ·
                        rfl

theorem cell23_5276018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5276018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276018 prefixEnd_5276018 := by exact prefixLift 5276018
  have htrace : WordTrace (prefixWord ++ tailWord_5276018) baseStart_5276018 baseEnd_5276018 := by
    simpa [prefixWord, tailWord_5276018, baseEnd_5276018] using wordTrace_append hprefix tailTrace_5276018
  have hstable : (prefixWord ++ tailWord_5276018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276018).length < 2 ^ (prefixWord ++ tailWord_5276018).sum := by decide
  have hdescent : baseEnd_5276018 < baseStart_5276018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276031 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_5276031 : Nat := 118140960795 + 5276031 * 2 ^ 59
def prefixEnd_5276031 : Nat := 4983230072969 + 3 ^ 40 * 5276031 * 2
def baseEnd_5276031 : Nat := 2709139851021752238148481

theorem tailTrace_5276031 : CollatzResearch.WordTrace tailWord_5276031 prefixEnd_5276031 2709139851021752238148481 := by
  unfold tailWord_5276031
  simp only [CollatzResearch.WordTrace]
  refine ⟨192432659548848236201715947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128288439699232157467810631 192432659548848236201715947)
  ·
    refine ⟨288648989323272354302573921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192432659548848236201715947 288648989323272354302573921)
    ·
      refine ⟨216486741992454265726930441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288648989323272354302573921 216486741992454265726930441)
      ·
        refine ⟨162365056494340699295197831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216486741992454265726930441 162365056494340699295197831)
        ·
          refine ⟨243547584741511048942796747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162365056494340699295197831 243547584741511048942796747)
          ·
            refine ⟨365321377112266573414195121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243547584741511048942796747 365321377112266573414195121)
            ·
              refine ⟨273991032834199930060646341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365321377112266573414195121 273991032834199930060646341)
              ·
                refine ⟨51373318656412486886371189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273991032834199930060646341 51373318656412486886371189)
                ·
                  refine ⟨4816248624038670645597299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51373318656412486886371189 4816248624038670645597299)
                  ·
                    refine ⟨7224372936058005968395949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816248624038670645597299 7224372936058005968395949)
                    ·
                      refine ⟨2709139851021752238148481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224372936058005968395949 2709139851021752238148481)
                      ·
                        rfl

theorem cell23_5276031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_5276031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276031 prefixEnd_5276031 := by exact prefixLift 5276031
  have htrace : WordTrace (prefixWord ++ tailWord_5276031) baseStart_5276031 baseEnd_5276031 := by
    simpa [prefixWord, tailWord_5276031, baseEnd_5276031] using wordTrace_append hprefix tailTrace_5276031
  have hstable : (prefixWord ++ tailWord_5276031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276031).length < 2 ^ (prefixWord ++ tailWord_5276031).sum := by decide
  have hdescent : baseEnd_5276031 < baseStart_5276031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276042 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_5276042 : Nat := 118140960795 + 5276042 * 2 ^ 59
def prefixEnd_5276042 : Nat := 4983230072969 + 3 ^ 40 * 5276042 * 2
def baseEnd_5276042 : Nat := 903048499769650565036977

theorem tailTrace_5276042 : CollatzResearch.WordTrace tailWord_5276042 prefixEnd_5276042 903048499769650565036977 := by
  unfold tailWord_5276042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48108265187952096270091595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128288707167872256720244253 48108265187952096270091595)
  ·
    refine ⟨72162397781928144405137393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48108265187952096270091595 72162397781928144405137393)
    ·
      refine ⟨54121798336446108303853045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72162397781928144405137393 54121798336446108303853045)
      ·
        refine ⟨5073918594041822653486223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54121798336446108303853045 5073918594041822653486223)
        ·
          refine ⟨7610877891062733980229335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073918594041822653486223 7610877891062733980229335)
          ·
            refine ⟨11416316836594100970344003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7610877891062733980229335 11416316836594100970344003)
            ·
              refine ⟨17124475254891151455516005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11416316836594100970344003 17124475254891151455516005)
              ·
                refine ⟨3210839110292090897909251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17124475254891151455516005 3210839110292090897909251)
                ·
                  refine ⟨4816258665438136346863877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210839110292090897909251 4816258665438136346863877)
                  ·
                    refine ⟨903048499769650565036977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816258665438136346863877 903048499769650565036977)
                    ·
                      rfl

theorem cell23_5276042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_5276042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276042 prefixEnd_5276042 := by exact prefixLift 5276042
  have htrace : WordTrace (prefixWord ++ tailWord_5276042) baseStart_5276042 baseEnd_5276042 := by
    simpa [prefixWord, tailWord_5276042, baseEnd_5276042] using wordTrace_append hprefix tailTrace_5276042
  have hstable : (prefixWord ++ tailWord_5276042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276042).length < 2 ^ (prefixWord ++ tailWord_5276042).sum := by decide
  have hdescent : baseEnd_5276042 < baseStart_5276042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276081 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_5276081 : Nat := 118140960795 + 5276081 * 2 ^ 59
def prefixEnd_5276081 : Nat := 4983230072969 + 3 ^ 40 * 5276081 * 2
def baseEnd_5276081 : Nat := 903055175018159014174417

theorem tailTrace_5276081 : CollatzResearch.WordTrace tailWord_5276081 prefixEnd_5276081 903055175018159014174417 := by
  unfold tailWord_5276081
  simp only [CollatzResearch.WordTrace]
  refine ⟨192434483198667094741036097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128289655465778063160690731 192434483198667094741036097)
  ·
    refine ⟨144325862399000321055777073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192434483198667094741036097 144325862399000321055777073)
    ·
      refine ⟨108244396799250240791832805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144325862399000321055777073 108244396799250240791832805)
      ·
        refine ⟨20295824399859420148468651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108244396799250240791832805 20295824399859420148468651)
        ·
          refine ⟨30443736599789130222702977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20295824399859420148468651 30443736599789130222702977)
          ·
            refine ⟨22832802449841847667027233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30443736599789130222702977 22832802449841847667027233)
            ·
              refine ⟨17124601837381385750270425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22832802449841847667027233 17124601837381385750270425)
              ·
                refine ⟨12843451378036039312702819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17124601837381385750270425 12843451378036039312702819)
                ·
                  refine ⟨19265177067054058969054229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12843451378036039312702819 19265177067054058969054229)
                  ·
                    refine ⟨903055175018159014174417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19265177067054058969054229 903055175018159014174417)
                    ·
                      rfl

theorem cell23_5276081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_5276081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276081 prefixEnd_5276081 := by exact prefixLift 5276081
  have htrace : WordTrace (prefixWord ++ tailWord_5276081) baseStart_5276081 baseEnd_5276081 := by
    simpa [prefixWord, tailWord_5276081, baseEnd_5276081] using wordTrace_append hprefix tailTrace_5276081
  have hstable : (prefixWord ++ tailWord_5276081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276081).length < 2 ^ (prefixWord ++ tailWord_5276081).sum := by decide
  have hdescent : baseEnd_5276081 < baseStart_5276081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276088 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_5276088 : Nat := 118140960795 + 5276088 * 2 ^ 59
def prefixEnd_5276088 : Nat := 4983230072969 + 3 ^ 40 * 5276088 * 2
def baseEnd_5276088 : Nat := 2709169119419058515135719

theorem tailTrace_5276088 : CollatzResearch.WordTrace tailWord_5276088 prefixEnd_5276088 2709169119419058515135719 := by
  unfold tailWord_5276088
  simp only [CollatzResearch.WordTrace]
  refine ⟨96217369254820867468270459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128289825673094489957693945 96217369254820867468270459)
  ·
    refine ⟨144326053882231301202405689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96217369254820867468270459 144326053882231301202405689)
    ·
      refine ⟨108244540411673475901804267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144326053882231301202405689 108244540411673475901804267)
      ·
        refine ⟨162366810617510213852706401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108244540411673475901804267 162366810617510213852706401)
        ·
          refine ⟨121775107963132660389529801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162366810617510213852706401 121775107963132660389529801)
          ·
            refine ⟨91331330972349495292147351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121775107963132660389529801 91331330972349495292147351)
            ·
              refine ⟨136996996458524242938221027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91331330972349495292147351 136996996458524242938221027)
              ·
                refine ⟨205495494687786364407331541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136996996458524242938221027 205495494687786364407331541)
                ·
                  refine ⟨4816300656744992915796833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 205495494687786364407331541 4816300656744992915796833)
                  ·
                    refine ⟨3612225492558744686847625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816300656744992915796833 3612225492558744686847625)
                    ·
                      refine ⟨2709169119419058515135719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612225492558744686847625 2709169119419058515135719)
                      ·
                        rfl

theorem cell23_5276088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_5276088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276088 prefixEnd_5276088 := by exact prefixLift 5276088
  have htrace : WordTrace (prefixWord ++ tailWord_5276088) baseStart_5276088 baseEnd_5276088 := by
    simpa [prefixWord, tailWord_5276088, baseEnd_5276088] using wordTrace_append hprefix tailTrace_5276088
  have hstable : (prefixWord ++ tailWord_5276088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276088).length < 2 ^ (prefixWord ++ tailWord_5276088).sum := by decide
  have hdescent : baseEnd_5276088 < baseStart_5276088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276108 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5276108 : Nat := 118140960795 + 5276108 * 2 ^ 59
def prefixEnd_5276108 : Nat := 4983230072969 + 3 ^ 40 * 5276108 * 2
def baseEnd_5276108 : Nat := 2709179389032148436885627

theorem tailTrace_5276108 : CollatzResearch.WordTrace tailWord_5276108 prefixEnd_5276108 2709179389032148436885627 := by
  unfold tailWord_5276108
  simp only [CollatzResearch.WordTrace]
  refine ⟨96217733984784639176134489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128290311979712852234845985 96217733984784639176134489)
  ·
    refine ⟨72163300488588479382100867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96217733984784639176134489 72163300488588479382100867)
    ·
      refine ⟨108244950732882719073151301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72163300488588479382100867 108244950732882719073151301)
      ·
        refine ⟨20295928262415509826215869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108244950732882719073151301 20295928262415509826215869)
        ·
          refine ⟨7610973098405816184830951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20295928262415509826215869 7610973098405816184830951)
          ·
            refine ⟨11416459647608724277246427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7610973098405816184830951 11416459647608724277246427)
            ·
              refine ⟨17124689471413086415869641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11416459647608724277246427 17124689471413086415869641)
              ·
                refine ⟨12843517103559814811902231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17124689471413086415869641 12843517103559814811902231)
                ·
                  refine ⟨19265275655339722217853347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12843517103559814811902231 19265275655339722217853347)
                  ·
                    refine ⟨28897913483009583326780021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19265275655339722217853347 28897913483009583326780021)
                    ·
                      refine ⟨2709179389032148436885627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28897913483009583326780021 2709179389032148436885627)
                      ·
                        rfl

theorem cell23_5276108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5276108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276108 prefixEnd_5276108 := by exact prefixLift 5276108
  have htrace : WordTrace (prefixWord ++ tailWord_5276108) baseStart_5276108 baseEnd_5276108 := by
    simpa [prefixWord, tailWord_5276108, baseEnd_5276108] using wordTrace_append hprefix tailTrace_5276108
  have hstable : (prefixWord ++ tailWord_5276108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276108).length < 2 ^ (prefixWord ++ tailWord_5276108).sum := by decide
  have hdescent : baseEnd_5276108 < baseStart_5276108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276118 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5276118 : Nat := 118140960795 + 5276118 * 2 ^ 59
def prefixEnd_5276118 : Nat := 4983230072969 + 3 ^ 40 * 5276118 * 2
def baseEnd_5276118 : Nat := 2709184523838693397760581

theorem tailTrace_5276118 : CollatzResearch.WordTrace tailWord_5276118 prefixEnd_5276118 2709184523838693397760581 := by
  unfold tailWord_5276118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027239543720815628758313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128290555133022033373422005 12027239543720815628758313)
  ·
    refine ⟨9020429657790611721568735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12027239543720815628758313 9020429657790611721568735)
    ·
      refine ⟨13530644486685917582353103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9020429657790611721568735 13530644486685917582353103)
      ·
        refine ⟨20295966730028876373529655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530644486685917582353103 20295966730028876373529655)
        ·
          refine ⟨30443950095043314560294483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20295966730028876373529655 30443950095043314560294483)
          ·
            refine ⟨45665925142564971840441725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30443950095043314560294483 45665925142564971840441725)
            ·
              refine ⟨17124721928461864440165647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45665925142564971840441725 17124721928461864440165647)
              ·
                refine ⟨25687082892692796660248471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17124721928461864440165647 25687082892692796660248471)
                ·
                  refine ⟨38530624339039194990372707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25687082892692796660248471 38530624339039194990372707)
                  ·
                    refine ⟨57795936508558792485559061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38530624339039194990372707 57795936508558792485559061)
                    ·
                      refine ⟨2709184523838693397760581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57795936508558792485559061 2709184523838693397760581)
                      ·
                        rfl

theorem cell23_5276118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5276118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276118 prefixEnd_5276118 := by exact prefixLift 5276118
  have htrace : WordTrace (prefixWord ++ tailWord_5276118) baseStart_5276118 baseEnd_5276118 := by
    simpa [prefixWord, tailWord_5276118, baseEnd_5276118] using wordTrace_append hprefix tailTrace_5276118
  have hstable : (prefixWord ++ tailWord_5276118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276118).length < 2 ^ (prefixWord ++ tailWord_5276118).sum := by decide
  have hdescent : baseEnd_5276118 < baseStart_5276118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276125 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_5276125 : Nat := 118140960795 + 5276125 * 2 ^ 59
def prefixEnd_5276125 : Nat := 4983230072969 + 3 ^ 40 * 5276125 * 2
def baseEnd_5276125 : Nat := 2709188118203274870373049

theorem tailTrace_5276125 : CollatzResearch.WordTrace tailWord_5276125 prefixEnd_5276125 2709188118203274870373049 := by
  unfold tailWord_5276125
  simp only [CollatzResearch.WordTrace]
  refine ⟨192436088010507690255637829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128290725340338460170425219 192436088010507690255637829)
  ·
    refine ⟨36081766501970191922932093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192436088010507690255637829 36081766501970191922932093)
    ·
      refine ⟨13530662438238821971099535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36081766501970191922932093 13530662438238821971099535)
      ·
        refine ⟨20295993657358232956649303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530662438238821971099535 20295993657358232956649303)
        ·
          refine ⟨30443990486037349434973955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20295993657358232956649303 30443990486037349434973955)
          ·
            refine ⟨45665985729056024152460933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30443990486037349434973955 45665985729056024152460933)
            ·
              refine ⟨8562372324198004528586425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45665985729056024152460933 8562372324198004528586425)
              ·
                refine ⟨6421779243148503396439819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8562372324198004528586425 6421779243148503396439819)
                ·
                  refine ⟨9632668864722755094659729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6421779243148503396439819 9632668864722755094659729)
                  ·
                    refine ⟨7224501648542066320994797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9632668864722755094659729 7224501648542066320994797)
                    ·
                      refine ⟨2709188118203274870373049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224501648542066320994797 2709188118203274870373049)
                      ·
                        rfl

theorem cell23_5276125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_5276125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276125 prefixEnd_5276125 := by exact prefixLift 5276125
  have htrace : WordTrace (prefixWord ++ tailWord_5276125) baseStart_5276125 baseEnd_5276125 := by
    simpa [prefixWord, tailWord_5276125, baseEnd_5276125] using wordTrace_append hprefix tailTrace_5276125
  have hstable : (prefixWord ++ tailWord_5276125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276125).length < 2 ^ (prefixWord ++ tailWord_5276125).sum := by decide
  have hdescent : baseEnd_5276125 < baseStart_5276125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276166 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5276166 : Nat := 118140960795 + 5276166 * 2 ^ 59
def prefixEnd_5276166 : Nat := 4983230072969 + 3 ^ 40 * 5276166 * 2
def baseEnd_5276166 : Nat := 903069723636703069986787

theorem tailTrace_5276166 : CollatzResearch.WordTrace tailWord_5276166 prefixEnd_5276166 903069723636703069986787 := by
  unfold tailWord_5276166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013674481354973570558761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128291722268906102838586901 6013674481354973570558761)
  ·
    refine ⟨4510255861016230177919071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6013674481354973570558761 4510255861016230177919071)
    ·
      refine ⟨6765383791524345266878607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510255861016230177919071 6765383791524345266878607)
      ·
        refine ⟨10148075687286517900317911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6765383791524345266878607 10148075687286517900317911)
        ·
          refine ⟨15222113530929776850476867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148075687286517900317911 15222113530929776850476867)
          ·
            refine ⟨22833170296394665275715301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222113530929776850476867 22833170296394665275715301)
            ·
              refine ⟨4281219430573999739196619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22833170296394665275715301 4281219430573999739196619)
              ·
                refine ⟨6421829145860999608794929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281219430573999739196619 6421829145860999608794929)
                ·
                  refine ⟨4816371859395749706596197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6421829145860999608794929 4816371859395749706596197)
                  ·
                    refine ⟨903069723636703069986787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816371859395749706596197 903069723636703069986787)
                    ·
                      rfl

theorem cell23_5276166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5276166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276166 prefixEnd_5276166 := by exact prefixLift 5276166
  have htrace : WordTrace (prefixWord ++ tailWord_5276166) baseStart_5276166 baseEnd_5276166 := by
    simpa [prefixWord, tailWord_5276166, baseEnd_5276166] using wordTrace_append hprefix tailTrace_5276166
  have hstable : (prefixWord ++ tailWord_5276166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276166).length < 2 ^ (prefixWord ++ tailWord_5276166).sum := by decide
  have hdescent : baseEnd_5276166 < baseStart_5276166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276172 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_5276172 : Nat := 118140960795 + 5276172 * 2 ^ 59
def prefixEnd_5276172 : Nat := 4983230072969 + 3 ^ 40 * 5276172 * 2
def baseEnd_5276172 : Nat := 2709212251794036186485333

theorem tailTrace_5276172 : CollatzResearch.WordTrace tailWord_5276172 prefixEnd_5276172 2709212251794036186485333 := by
  unfold tailWord_5276172
  simp only [CollatzResearch.WordTrace]
  refine ⟨96218901120668708641299385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128291868160891611521732513 96218901120668708641299385)
  ·
    refine ⟨72164175840501531480974539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96218901120668708641299385 72164175840501531480974539)
    ·
      refine ⟨108246263760752297221461809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72164175840501531480974539 108246263760752297221461809)
      ·
        refine ⟨81184697820564222916096357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108246263760752297221461809 81184697820564222916096357)
        ·
          refine ⟨15222130841355791796768067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81184697820564222916096357 15222130841355791796768067)
          ·
            refine ⟨22833196262033687695152101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222130841355791796768067 22833196262033687695152101)
            ·
              refine ⟨4281224299131316442841019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22833196262033687695152101 4281224299131316442841019)
              ·
                refine ⟨6421836448696974664261529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281224299131316442841019 6421836448696974664261529)
                ·
                  refine ⟨4816377336522730998196147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6421836448696974664261529 4816377336522730998196147)
                  ·
                    refine ⟨7224566004784096497294221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816377336522730998196147 7224566004784096497294221)
                    ·
                      refine ⟨2709212251794036186485333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224566004784096497294221 2709212251794036186485333)
                      ·
                        rfl

theorem cell23_5276172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_5276172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276172 prefixEnd_5276172 := by exact prefixLift 5276172
  have htrace : WordTrace (prefixWord ++ tailWord_5276172) baseStart_5276172 baseEnd_5276172 := by
    simpa [prefixWord, tailWord_5276172, baseEnd_5276172] using wordTrace_append hprefix tailTrace_5276172
  have hstable : (prefixWord ++ tailWord_5276172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276172).length < 2 ^ (prefixWord ++ tailWord_5276172).sum := by decide
  have hdescent : baseEnd_5276172 < baseStart_5276172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276181 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_5276181 : Nat := 118140960795 + 5276181 * 2 ^ 59
def prefixEnd_5276181 : Nat := 4983230072969 + 3 ^ 40 * 5276181 * 2
def baseEnd_5276181 : Nat := 2709216873119926651272791

theorem tailTrace_5276181 : CollatzResearch.WordTrace tailWord_5276181 prefixEnd_5276181 2709216873119926651272791 := by
  unfold tailWord_5276181
  simp only [CollatzResearch.WordTrace]
  refine ⟨192438130498304811819676397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128292086998869874546450931 192438130498304811819676397)
  ·
    refine ⟨72164298936864304432378649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192438130498304811819676397 72164298936864304432378649)
    ·
      refine ⟨54123224202648228324283987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72164298936864304432378649 54123224202648228324283987)
      ·
        refine ⟨81184836303972342486425981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54123224202648228324283987 81184836303972342486425981)
        ·
          refine ⟨30444313613989628432409743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81184836303972342486425981 30444313613989628432409743)
          ·
            refine ⟨45666470420984442648614615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30444313613989628432409743 45666470420984442648614615)
            ·
              refine ⟨68499705631476663972921923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45666470420984442648614615 68499705631476663972921923)
              ·
                refine ⟨102749558447214995959382885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68499705631476663972921923 102749558447214995959382885)
                ·
                  refine ⟨19265542208852811742384291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102749558447214995959382885 19265542208852811742384291)
                  ·
                    refine ⟨28898313313279217613576437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19265542208852811742384291 28898313313279217613576437)
                    ·
                      refine ⟨2709216873119926651272791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28898313313279217613576437 2709216873119926651272791)
                      ·
                        rfl

theorem cell23_5276181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_5276181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276181 prefixEnd_5276181 := by exact prefixLift 5276181
  have htrace : WordTrace (prefixWord ++ tailWord_5276181) baseStart_5276181 baseEnd_5276181 := by
    simpa [prefixWord, tailWord_5276181, baseEnd_5276181] using wordTrace_append hprefix tailTrace_5276181
  have hstable : (prefixWord ++ tailWord_5276181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276181).length < 2 ^ (prefixWord ++ tailWord_5276181).sum := by decide
  have hdescent : baseEnd_5276181 < baseStart_5276181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276191 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5276191 : Nat := 118140960795 + 5276191 * 2 ^ 59
def prefixEnd_5276191 : Nat := 4983230072969 + 3 ^ 40 * 5276191 * 2
def baseEnd_5276191 : Nat := 2709222007926471612147745

theorem tailTrace_5276191 : CollatzResearch.WordTrace tailWord_5276191 prefixEnd_5276191 2709222007926471612147745 := by
  unfold tailWord_5276191
  simp only [CollatzResearch.WordTrace]
  refine ⟨192438495228268583527540427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128292330152179055685026951 192438495228268583527540427)
  ·
    refine ⟨288657742842402875291310641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192438495228268583527540427 288657742842402875291310641)
    ·
      refine ⟨216493307131802156468482981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288657742842402875291310641 216493307131802156468482981)
      ·
        refine ⟨40592495087212904337840559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216493307131802156468482981 40592495087212904337840559)
        ·
          refine ⟨60888742630819356506760839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40592495087212904337840559 60888742630819356506760839)
          ·
            refine ⟨91333113946229034760141259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60888742630819356506760839 91333113946229034760141259)
            ·
              refine ⟨136999670919343552140211889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91333113946229034760141259 136999670919343552140211889)
              ·
                refine ⟨102749753189507664105158917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136999670919343552140211889 102749753189507664105158917)
                ·
                  refine ⟨19265578723032687019717297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102749753189507664105158917 19265578723032687019717297)
                  ·
                    refine ⟨14449184042274515264787973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19265578723032687019717297 14449184042274515264787973)
                    ·
                      refine ⟨2709222007926471612147745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14449184042274515264787973 2709222007926471612147745)
                      ·
                        rfl

theorem cell23_5276191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5276191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276191 prefixEnd_5276191 := by exact prefixLift 5276191
  have htrace : WordTrace (prefixWord ++ tailWord_5276191) baseStart_5276191 baseEnd_5276191 := by
    simpa [prefixWord, tailWord_5276191, baseEnd_5276191] using wordTrace_append hprefix tailTrace_5276191
  have hstable : (prefixWord ++ tailWord_5276191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276191).length < 2 ^ (prefixWord ++ tailWord_5276191).sum := by decide
  have hdescent : baseEnd_5276191 < baseStart_5276191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276195 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 4, 2]
def baseStart_5276195 : Nat := 118140960795 + 5276195 * 2 ^ 59
def prefixEnd_5276195 : Nat := 4983230072969 + 3 ^ 40 * 5276195 * 2
def baseEnd_5276195 : Nat := 2709224061849089596497727

theorem tailTrace_5276195 : CollatzResearch.WordTrace tailWord_5276195 prefixEnd_5276195 2709224061849089596497727 := by
  unfold tailWord_5276195
  simp only [CollatzResearch.WordTrace]
  refine ⟨192438641120254092210686039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128292427413502728140457359 192438641120254092210686039)
  ·
    refine ⟨288657961680381138316029059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192438641120254092210686039 288657961680381138316029059)
    ·
      refine ⟨432986942520571707474043589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288657961680381138316029059 432986942520571707474043589)
      ·
        refine ⟨81185051722607195151383173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432986942520571707474043589 81185051722607195151383173)
        ·
          refine ⟨15222197197988849090884345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81185051722607195151383173 15222197197988849090884345)
          ·
            refine ⟨11416647898491636818163259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15222197197988849090884345 11416647898491636818163259)
            ·
              refine ⟨17124971847737455227244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11416647898491636818163259 17124971847737455227244889)
              ·
                refine ⟨12843728885803091420433667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17124971847737455227244889 12843728885803091420433667)
                ·
                  refine ⟨19265593328704637130650501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12843728885803091420433667 19265593328704637130650501)
                  ·
                    refine ⟨3612298749132119461996969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19265593328704637130650501 3612298749132119461996969)
                    ·
                      refine ⟨2709224061849089596497727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612298749132119461996969 2709224061849089596497727)
                      ·
                        rfl

theorem cell23_5276195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_5276195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276195 prefixEnd_5276195 := by exact prefixLift 5276195
  have htrace : WordTrace (prefixWord ++ tailWord_5276195) baseStart_5276195 baseEnd_5276195 := by
    simpa [prefixWord, tailWord_5276195, baseEnd_5276195] using wordTrace_append hprefix tailTrace_5276195
  have hstable : (prefixWord ++ tailWord_5276195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276195).length < 2 ^ (prefixWord ++ tailWord_5276195).sum := by decide
  have hdescent : baseEnd_5276195 < baseStart_5276195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276248 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_5276248 : Nat := 118140960795 + 5276248 * 2 ^ 59
def prefixEnd_5276248 : Nat := 4983230072969 + 3 ^ 40 * 5276248 * 2
def baseEnd_5276248 : Nat := 903083758774592629711661

theorem tailTrace_5276248 : CollatzResearch.WordTrace tailWord_5276248 prefixEnd_5276248 903083758774592629711661 := by
  unfold tailWord_5276248
  simp only [CollatzResearch.WordTrace]
  refine ⟨96220287094531041131182699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128293716126041388174910265 96220287094531041131182699)
  ·
    refine ⟨144330430641796561696774049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96220287094531041131182699 144330430641796561696774049)
    ·
      refine ⟨108247822981347421272580537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144330430641796561696774049 108247822981347421272580537)
      ·
        refine ⟨81185867236010565954435403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108247822981347421272580537 81185867236010565954435403)
        ·
          refine ⟨121778800854015848931653105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81185867236010565954435403 121778800854015848931653105)
          ·
            refine ⟨91334100640511886698739829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121778800854015848931653105 91334100640511886698739829)
            ·
              refine ⟨8562571935047989378006859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91334100640511886698739829 8562571935047989378006859)
              ·
                refine ⟨12843857902571984067010289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562571935047989378006859 12843857902571984067010289)
                ·
                  refine ⟨9632893426928988050257717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12843857902571984067010289 9632893426928988050257717)
                  ·
                    refine ⟨903083758774592629711661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9632893426928988050257717 903083758774592629711661)
                    ·
                      rfl

theorem cell23_5276248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_5276248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276248 prefixEnd_5276248 := by exact prefixLift 5276248
  have htrace : WordTrace (prefixWord ++ tailWord_5276248) baseStart_5276248 baseEnd_5276248 := by
    simpa [prefixWord, tailWord_5276248, baseEnd_5276248] using wordTrace_append hprefix tailTrace_5276248
  have hstable : (prefixWord ++ tailWord_5276248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276248).length < 2 ^ (prefixWord ++ tailWord_5276248).sum := by decide
  have hdescent : baseEnd_5276248 < baseStart_5276248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276252 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 5]
def baseStart_5276252 : Nat := 118140960795 + 5276252 * 2 ^ 59
def prefixEnd_5276252 : Nat := 4983230072969 + 3 ^ 40 * 5276252 * 2
def baseEnd_5276252 : Nat := 301028147805155097053885

theorem tailTrace_5276252 : CollatzResearch.WordTrace tailWord_5276252 prefixEnd_5276252 301028147805155097053885 := by
  unfold tailWord_5276252
  simp only [CollatzResearch.WordTrace]
  refine ⟨96220360040523795472755505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128293813387365060630340673 96220360040523795472755505)
  ·
    refine ⟨72165270030392846604566629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96220360040523795472755505 72165270030392846604566629)
    ·
      refine ⟨13530988130698658738356243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72165270030392846604566629 13530988130698658738356243)
      ·
        refine ⟨20296482196047988107534365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530988130698658738356243 20296482196047988107534365)
        ·
          refine ⟨7611180823517995540325387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20296482196047988107534365 7611180823517995540325387)
          ·
            refine ⟨11416771235276993310488081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611180823517995540325387 11416771235276993310488081)
            ·
              refine ⟨8562578426457744982866061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11416771235276993310488081 8562578426457744982866061)
              ·
                refine ⟨3210966909921654368574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8562578426457744982866061 3210966909921654368574773)
                ·
                  refine ⟨301028147805155097053885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210966909921654368574773 301028147805155097053885)
                  ·
                    rfl

theorem cell23_5276252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_5276252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276252 prefixEnd_5276252 := by exact prefixLift 5276252
  have htrace : WordTrace (prefixWord ++ tailWord_5276252) baseStart_5276252 baseEnd_5276252 := by
    simpa [prefixWord, tailWord_5276252, baseEnd_5276252] using wordTrace_append hprefix tailTrace_5276252
  have hstable : (prefixWord ++ tailWord_5276252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276252).length < 2 ^ (prefixWord ++ tailWord_5276252).sum := by decide
  have hdescent : baseEnd_5276252 < baseStart_5276252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276268 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_5276268 : Nat := 118140960795 + 5276268 * 2 ^ 59
def prefixEnd_5276268 : Nat := 4983230072969 + 3 ^ 40 * 5276268 * 2
def baseEnd_5276268 : Nat := 2709261545936867810884891

theorem tailTrace_5276268 : CollatzResearch.WordTrace tailWord_5276268 prefixEnd_5276268 2709261545936867810884891 := by
  unfold tailWord_5276268
  simp only [CollatzResearch.WordTrace]
  refine ⟨96220651824494812839046729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128294202432659750452062305 96220651824494812839046729)
  ·
    refine ⟨72165488868371109629285047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96220651824494812839046729 72165488868371109629285047)
    ·
      refine ⟨108248233302556664443927571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72165488868371109629285047 108248233302556664443927571)
      ·
        refine ⟨162372349953834996665891357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108248233302556664443927571 162372349953834996665891357)
        ·
          refine ⟨60889631232688123749709259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162372349953834996665891357 60889631232688123749709259)
          ·
            refine ⟨91334446849032185624563889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60889631232688123749709259 91334446849032185624563889)
            ·
              refine ⟨68500835136774139218422917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91334446849032185624563889 68500835136774139218422917)
              ·
                refine ⟨12843906588145151103454297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68500835136774139218422917 12843906588145151103454297)
                ·
                  refine ⟨9632929941108863327590723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12843906588145151103454297 9632929941108863327590723)
                  ·
                    refine ⟨14449394911663294991386085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9632929941108863327590723 14449394911663294991386085)
                    ·
                      refine ⟨2709261545936867810884891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14449394911663294991386085 2709261545936867810884891)
                      ·
                        rfl

theorem cell23_5276268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_5276268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276268 prefixEnd_5276268 := by exact prefixLift 5276268
  have htrace : WordTrace (prefixWord ++ tailWord_5276268) baseStart_5276268 baseEnd_5276268 := by
    simpa [prefixWord, tailWord_5276268, baseEnd_5276268] using wordTrace_append hprefix tailTrace_5276268
  have hstable : (prefixWord ++ tailWord_5276268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276268).length < 2 ^ (prefixWord ++ tailWord_5276268).sum := by decide
  have hdescent : baseEnd_5276268 < baseStart_5276268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276271 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_5276271 : Nat := 118140960795 + 5276271 * 2 ^ 59
def prefixEnd_5276271 : Nat := 4983230072969 + 3 ^ 40 * 5276271 * 2
def baseEnd_5276271 : Nat := 2709263086378831299147377

theorem tailTrace_5276271 : CollatzResearch.WordTrace tailWord_5276271 prefixEnd_5276271 2709263086378831299147377 := by
  unfold tailWord_5276271
  simp only [CollatzResearch.WordTrace]
  refine ⟨192441413067978757190452667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128294275378652504793635111 192441413067978757190452667)
  ·
    refine ⟨288662119601968135785679001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192441413067978757190452667 288662119601968135785679001)
    ·
      refine ⟨216496589701476101839259251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288662119601968135785679001 216496589701476101839259251)
      ·
        refine ⟨324744884552214152758888877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216496589701476101839259251 324744884552214152758888877)
        ·
          refine ⟨121779331707080307284583329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324744884552214152758888877 121779331707080307284583329)
          ·
            refine ⟨91334498780310230463437497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121779331707080307284583329 91334498780310230463437497)
            ·
              refine ⟨68500874085232672847578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91334498780310230463437497 68500874085232672847578123)
              ·
                refine ⟨102751311127849009271367185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68500874085232672847578123 102751311127849009271367185)
                ·
                  refine ⟨77063483345886756953525389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102751311127849009271367185 77063483345886756953525389)
                  ·
                    refine ⟨28898806254707533857572021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77063483345886756953525389 28898806254707533857572021)
                    ·
                      refine ⟨2709263086378831299147377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28898806254707533857572021 2709263086378831299147377)
                      ·
                        rfl

theorem cell23_5276271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_5276271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276271 prefixEnd_5276271 := by exact prefixLift 5276271
  have htrace : WordTrace (prefixWord ++ tailWord_5276271) baseStart_5276271 baseEnd_5276271 := by
    simpa [prefixWord, tailWord_5276271, baseEnd_5276271] using wordTrace_append hprefix tailTrace_5276271
  have hstable : (prefixWord ++ tailWord_5276271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276271).length < 2 ^ (prefixWord ++ tailWord_5276271).sum := by decide
  have hdescent : baseEnd_5276271 < baseStart_5276271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276288 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_5276288 : Nat := 118140960795 + 5276288 * 2 ^ 59
def prefixEnd_5276288 : Nat := 4983230072969 + 3 ^ 40 * 5276288 * 2
def baseEnd_5276288 : Nat := 2709271815549957732634799

theorem tailTrace_5276288 : CollatzResearch.WordTrace tailWord_5276288 prefixEnd_5276288 2709271815549957732634799 := by
  unfold tailWord_5276288
  simp only [CollatzResearch.WordTrace]
  refine ⟨96221016554458584546910759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128294688739278112729214345 96221016554458584546910759)
  ·
    refine ⟨144331524831687876820366139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96221016554458584546910759 144331524831687876820366139)
    ·
      refine ⟨216497287247531815230549209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144331524831687876820366139 216497287247531815230549209)
      ·
        refine ⟨162372965435648861422911907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216497287247531815230549209 162372965435648861422911907)
        ·
          refine ⟨243559448153473292134367861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162372965435648861422911907 243559448153473292134367861)
          ·
            refine ⟨22833698264388121137596987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243559448153473292134367861 22833698264388121137596987)
            ·
              refine ⟨34250547396582181706395481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22833698264388121137596987 34250547396582181706395481)
              ·
                refine ⟨25687910547436636279796611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34250547396582181706395481 25687910547436636279796611)
                ·
                  refine ⟨38531865821154954419694917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25687910547436636279796611 38531865821154954419694917)
                  ·
                    refine ⟨7224724841466553953692797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38531865821154954419694917 7224724841466553953692797)
                    ·
                      refine ⟨2709271815549957732634799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224724841466553953692797 2709271815549957732634799)
                      ·
                        rfl

theorem cell23_5276288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_5276288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276288 prefixEnd_5276288 := by exact prefixLift 5276288
  have htrace : WordTrace (prefixWord ++ tailWord_5276288) baseStart_5276288 baseEnd_5276288 := by
    simpa [prefixWord, tailWord_5276288, baseEnd_5276288] using wordTrace_append hprefix tailTrace_5276288
  have hstable : (prefixWord ++ tailWord_5276288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276288).length < 2 ^ (prefixWord ++ tailWord_5276288).sum := by decide
  have hdescent : baseEnd_5276288 < baseStart_5276288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276338 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_5276338 : Nat := 118140960795 + 5276338 * 2 ^ 59
def prefixEnd_5276338 : Nat := 4983230072969 + 3 ^ 40 * 5276338 * 2
def baseEnd_5276338 : Nat := 903099163194227512336523

theorem tailTrace_5276338 : CollatzResearch.WordTrace tailWord_5276338 prefixEnd_5276338 903099163194227512336523 := by
  unfold tailWord_5276338
  simp only [CollatzResearch.WordTrace]
  refine ⟨48110964189684006908285417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128295904505824018422094445 48110964189684006908285417)
  ·
    refine ⟨36083223142263005181214063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48110964189684006908285417 36083223142263005181214063)
    ·
      refine ⟨54124834713394507771821095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36083223142263005181214063 54124834713394507771821095)
      ·
        refine ⟨81187252070091761657731643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54124834713394507771821095 81187252070091761657731643)
        ·
          refine ⟨121780878105137642486597465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81187252070091761657731643 121780878105137642486597465)
          ·
            refine ⟨91335658578853231864948099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121780878105137642486597465 91335658578853231864948099)
            ·
              refine ⟨137003487868279847797422149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91335658578853231864948099 137003487868279847797422149)
              ·
                refine ⟨25688153975302471462016653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137003487868279847797422149 25688153975302471462016653)
                ·
                  refine ⟨9633057740738426798256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25688153975302471462016653 9633057740738426798256245)
                  ·
                    refine ⟨903099163194227512336523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9633057740738426798256245 903099163194227512336523)
                    ·
                      rfl

theorem cell23_5276338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_5276338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276338 prefixEnd_5276338 := by exact prefixLift 5276338
  have htrace : WordTrace (prefixWord ++ tailWord_5276338) baseStart_5276338 baseEnd_5276338 := by
    simpa [prefixWord, tailWord_5276338, baseEnd_5276338] using wordTrace_append hprefix tailTrace_5276338
  have hstable : (prefixWord ++ tailWord_5276338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276338).length < 2 ^ (prefixWord ++ tailWord_5276338).sum := by decide
  have hdescent : baseEnd_5276338 < baseStart_5276338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276345 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5276345 : Nat := 118140960795 + 5276345 * 2 ^ 59
def prefixEnd_5276345 : Nat := 4983230072969 + 3 ^ 40 * 5276345 * 2
def baseEnd_5276345 : Nat := 2709301083947264009622037

theorem tailTrace_5276345 : CollatzResearch.WordTrace tailWord_5276345 prefixEnd_5276345 2709301083947264009622037 := by
  unfold tailWord_5276345
  simp only [CollatzResearch.WordTrace]
  refine ⟨192444112069710667828646489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128296074713140445219097659 192444112069710667828646489)
  ·
    refine ⟨144333084052283000871484867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192444112069710667828646489 144333084052283000871484867)
    ·
      refine ⟨216499626078424501307227301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144333084052283000871484867 216499626078424501307227301)
      ·
        refine ⟨40593679889704593995105119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216499626078424501307227301 40593679889704593995105119)
        ·
          refine ⟨60890519834556890992657679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40593679889704593995105119 60890519834556890992657679)
          ·
            refine ⟨91335779751835336488986519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60890519834556890992657679 91335779751835336488986519)
            ·
              refine ⟨137003669627753004733479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91335779751835336488986519 137003669627753004733479779)
              ·
                refine ⟨205505504441629507100219669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137003669627753004733479779 205505504441629507100219669)
                ·
                  refine ⟨9633070520701383145322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205505504441629507100219669 9633070520701383145322797)
                  ·
                    refine ⟨3612401445263018679496049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9633070520701383145322797 3612401445263018679496049)
                    ·
                      refine ⟨2709301083947264009622037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612401445263018679496049 2709301083947264009622037)
                      ·
                        rfl

theorem cell23_5276345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5276345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276345 prefixEnd_5276345 := by exact prefixLift 5276345
  have htrace : WordTrace (prefixWord ++ tailWord_5276345) baseStart_5276345 baseEnd_5276345 := by
    simpa [prefixWord, tailWord_5276345, baseEnd_5276345] using wordTrace_append hprefix tailTrace_5276345
  have hstable : (prefixWord ++ tailWord_5276345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276345).length < 2 ^ (prefixWord ++ tailWord_5276345).sum := by decide
  have hdescent : baseEnd_5276345 < baseStart_5276345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276362 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_5276362 : Nat := 118140960795 + 5276362 * 2 ^ 59
def prefixEnd_5276362 : Nat := 4983230072969 + 3 ^ 40 * 5276362 * 2
def baseEnd_5276362 : Nat := 2709309813118390443109459

theorem tailTrace_5276362 : CollatzResearch.WordTrace tailWord_5276362 prefixEnd_5276362 2709309813118390443109459 := by
  unfold tailWord_5276362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111183027662269933003835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128296488073766053154676893 48111183027662269933003835)
  ·
    refine ⟨72166774541493404899505753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111183027662269933003835 72166774541493404899505753)
    ·
      refine ⟨54125080906120053674629315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72166774541493404899505753 54125080906120053674629315)
      ·
        refine ⟨81187621359180080511943973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54125080906120053674629315 81187621359180080511943973)
        ·
          refine ⟨15222679004846265095989495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81187621359180080511943973 15222679004846265095989495)
          ·
            refine ⟨22834018507269397643984243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222679004846265095989495 22834018507269397643984243)
            ·
              refine ⟨34251027760904096465976365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22834018507269397643984243 34251027760904096465976365)
              ·
                refine ⟨12844135410339036174741137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34251027760904096465976365 12844135410339036174741137)
                ·
                  refine ⟨9633101557754277131055853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12844135410339036174741137 9633101557754277131055853)
                  ·
                    refine ⟨3612413084157853924145945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9633101557754277131055853 3612413084157853924145945)
                    ·
                      refine ⟨2709309813118390443109459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612413084157853924145945 2709309813118390443109459)
                      ·
                        rfl

theorem cell23_5276362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_5276362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276362 prefixEnd_5276362 := by exact prefixLift 5276362
  have htrace : WordTrace (prefixWord ++ tailWord_5276362) baseStart_5276362 baseEnd_5276362 := by
    simpa [prefixWord, tailWord_5276362, baseEnd_5276362] using wordTrace_append hprefix tailTrace_5276362
  have hstable : (prefixWord ++ tailWord_5276362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276362).length < 2 ^ (prefixWord ++ tailWord_5276362).sum := by decide
  have hdescent : baseEnd_5276362 < baseStart_5276362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276402 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_5276402 : Nat := 118140960795 + 5276402 * 2 ^ 59
def prefixEnd_5276402 : Nat := 4983230072969 + 3 ^ 40 * 5276402 * 2
def baseEnd_5276402 : Nat := 903110117448190095536425

theorem tailTrace_5276402 : CollatzResearch.WordTrace tailWord_5276402 prefixEnd_5276402 903110117448190095536425 := by
  unfold tailWord_5276402
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111547757626041640867865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128297460687002777708980973 48111547757626041640867865)
  ·
    refine ⟨36083660818219531230650899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48111547757626041640867865 36083660818219531230650899)
    ·
      refine ⟨54125491227329296845976349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36083660818219531230650899 54125491227329296845976349)
      ·
        refine ⟨20297059210248486317241131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54125491227329296845976349 20297059210248486317241131)
        ·
          refine ⟨30445588815372729475861697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20297059210248486317241131 30445588815372729475861697)
          ·
            refine ⟨22834191611529547106896273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30445588815372729475861697 22834191611529547106896273)
            ·
              refine ⟨17125643708647160330172205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22834191611529547106896273 17125643708647160330172205)
              ·
                refine ⟨6422116390742685123814577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17125643708647160330172205 6422116390742685123814577)
                ·
                  refine ⟨4816587293057013842860933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422116390742685123814577 4816587293057013842860933)
                  ·
                    refine ⟨903110117448190095536425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816587293057013842860933 903110117448190095536425)
                    ·
                      rfl

theorem cell23_5276402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_5276402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276402 prefixEnd_5276402 := by exact prefixLift 5276402
  have htrace : WordTrace (prefixWord ++ tailWord_5276402) baseStart_5276402 baseEnd_5276402 := by
    simpa [prefixWord, tailWord_5276402, baseEnd_5276402] using wordTrace_append hprefix tailTrace_5276402
  have hstable : (prefixWord ++ tailWord_5276402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276402).length < 2 ^ (prefixWord ++ tailWord_5276402).sum := by decide
  have hdescent : baseEnd_5276402 < baseStart_5276402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276425 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_5276425 : Nat := 118140960795 + 5276425 * 2 ^ 59
def prefixEnd_5276425 : Nat := 4983230072969 + 3 ^ 40 * 5276425 * 2
def baseEnd_5276425 : Nat := 2709342162399623696621669

theorem tailTrace_5276425 : CollatzResearch.WordTrace tailWord_5276425 prefixEnd_5276425 2709342162399623696621669 := by
  unfold tailWord_5276425
  simp only [CollatzResearch.WordTrace]
  refine ⟨192447029909420841491558729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128298019939613894327705819 192447029909420841491558729)
  ·
    refine ⟨144335272432065631118669047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192447029909420841491558729 144335272432065631118669047)
    ·
      refine ⟨216502908648098446678003571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144335272432065631118669047 216502908648098446678003571)
      ·
        refine ⟨324754362972147670017005357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216502908648098446678003571 324754362972147670017005357)
        ·
          refine ⟨121782886114555376256377009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324754362972147670017005357 121782886114555376256377009)
          ·
            refine ⟨91337164585916532192282757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121782886114555376256377009 91337164585916532192282757)
            ·
              refine ⟨17125718359859349786053017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91337164585916532192282757 17125718359859349786053017)
              ·
                refine ⟨12844288769894512339539763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17125718359859349786053017 12844288769894512339539763)
                ·
                  refine ⟨19266433154841768509309645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12844288769894512339539763 19266433154841768509309645)
                  ·
                    refine ⟨7224912433065663190991117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19266433154841768509309645 7224912433065663190991117)
                    ·
                      refine ⟨2709342162399623696621669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224912433065663190991117 2709342162399623696621669)
                      ·
                        rfl

theorem cell23_5276425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_5276425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276425 prefixEnd_5276425 := by exact prefixLift 5276425
  have htrace : WordTrace (prefixWord ++ tailWord_5276425) baseStart_5276425 baseEnd_5276425 := by
    simpa [prefixWord, tailWord_5276425, baseEnd_5276425] using wordTrace_append hprefix tailTrace_5276425
  have hstable : (prefixWord ++ tailWord_5276425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276425).length < 2 ^ (prefixWord ++ tailWord_5276425).sum := by decide
  have hdescent : baseEnd_5276425 < baseStart_5276425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276426 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5276426 : Nat := 118140960795 + 5276426 * 2 ^ 59
def prefixEnd_5276426 : Nat := 4983230072969 + 3 ^ 40 * 5276426 * 2
def baseEnd_5276426 : Nat := 2709342675880278192709165

theorem tailTrace_5276426 : CollatzResearch.WordTrace tailWord_5276426 prefixEnd_5276426 2709342675880278192709165 := by
  unfold tailWord_5276426
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111766595604304665586283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128298044254944812441563421 48111766595604304665586283)
  ·
    refine ⟨72167649893406456998379425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111766595604304665586283 72167649893406456998379425)
    ·
      refine ⟨54125737420054842748784569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72167649893406456998379425 54125737420054842748784569)
      ·
        refine ⟨40594303065041132061588427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54125737420054842748784569 40594303065041132061588427)
        ·
          refine ⟨60891454597561698092382641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40594303065041132061588427 60891454597561698092382641)
          ·
            refine ⟨45668590948171273569286981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60891454597561698092382641 45668590948171273569286981)
            ·
              refine ⟨8562860802782113794241309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45668590948171273569286981 8562860802782113794241309)
              ·
                refine ⟨3211072801043292672840491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8562860802782113794241309 3211072801043292672840491)
                ·
                  refine ⟨4816609201564939009260737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211072801043292672840491 4816609201564939009260737)
                  ·
                    refine ⟨3612456901173704256945553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816609201564939009260737 3612456901173704256945553)
                    ·
                      refine ⟨2709342675880278192709165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612456901173704256945553 2709342675880278192709165)
                      ·
                        rfl

theorem cell23_5276426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5276426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276426 prefixEnd_5276426 := by exact prefixLift 5276426
  have htrace : WordTrace (prefixWord ++ tailWord_5276426) baseStart_5276426 baseEnd_5276426 := by
    simpa [prefixWord, tailWord_5276426, baseEnd_5276426] using wordTrace_append hprefix tailTrace_5276426
  have hstable : (prefixWord ++ tailWord_5276426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276426).length < 2 ^ (prefixWord ++ tailWord_5276426).sum := by decide
  have hdescent : baseEnd_5276426 < baseStart_5276426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276442 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_5276442 : Nat := 118140960795 + 5276442 * 2 ^ 59
def prefixEnd_5276442 : Nat := 4983230072969 + 3 ^ 40 * 5276442 * 2
def baseEnd_5276442 : Nat := 2709350891570750130109091

theorem tailTrace_5276442 : CollatzResearch.WordTrace tailWord_5276442 prefixEnd_5276442 2709350891570750130109091 := by
  unfold tailWord_5276442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111912487589813348731895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128298433300239502263285053 48111912487589813348731895)
  ·
    refine ⟨72167868731384720023097843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111912487589813348731895 72167868731384720023097843)
    ·
      refine ⟨108251803097077080034646765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72167868731384720023097843 108251803097077080034646765)
      ·
        refine ⟨40594426161403905012992537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108251803097077080034646765 40594426161403905012992537)
        ·
          refine ⟨30445819621052928759744403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40594426161403905012992537 30445819621052928759744403)
          ·
            refine ⟨45668729431579393139616605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30445819621052928759744403 45668729431579393139616605)
            ·
              refine ⟨17125773536842272427356227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45668729431579393139616605 17125773536842272427356227)
              ·
                refine ⟨25688660305263408641034341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17125773536842272427356227 25688660305263408641034341)
                ·
                  refine ⟨4816623807236889120193939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25688660305263408641034341 4816623807236889120193939)
                  ·
                    refine ⟨7224935710855333680290909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816623807236889120193939 7224935710855333680290909)
                    ·
                      refine ⟨2709350891570750130109091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7224935710855333680290909 2709350891570750130109091)
                      ·
                        rfl

theorem cell23_5276442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_5276442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276442 prefixEnd_5276442 := by exact prefixLift 5276442
  have htrace : WordTrace (prefixWord ++ tailWord_5276442) baseStart_5276442 baseEnd_5276442 := by
    simpa [prefixWord, tailWord_5276442, baseEnd_5276442] using wordTrace_append hprefix tailTrace_5276442
  have hstable : (prefixWord ++ tailWord_5276442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276442).length < 2 ^ (prefixWord ++ tailWord_5276442).sum := by decide
  have hdescent : baseEnd_5276442 < baseStart_5276442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276469 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_5276469 : Nat := 118140960795 + 5276469 * 2 ^ 59
def prefixEnd_5276469 : Nat := 4983230072969 + 3 ^ 40 * 5276469 * 2
def baseEnd_5276469 : Nat := 2709364755548421524471467

theorem tailTrace_5276469 : CollatzResearch.WordTrace tailWord_5276469 prefixEnd_5276469 2709364755548421524471467 := by
  unfold tailWord_5276469
  simp only [CollatzResearch.WordTrace]
  refine ⟨192448634721261437006160461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128299089814174291337440307 192448634721261437006160461)
  ·
    refine ⟨72168238020473038877310173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192448634721261437006160461 72168238020473038877310173)
    ·
      refine ⟨27063089257677389578991315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72168238020473038877310173 27063089257677389578991315)
      ·
        refine ⟨40594633886516084368486973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27063089257677389578991315 40594633886516084368486973)
        ·
          refine ⟨15222987707443531638182615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40594633886516084368486973 15222987707443531638182615)
          ·
            refine ⟨22834481561165297457273923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222987707443531638182615 22834481561165297457273923)
            ·
              refine ⟨34251722341747946185910885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22834481561165297457273923 34251722341747946185910885)
              ·
                refine ⟨6422197939077739909858291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34251722341747946185910885 6422197939077739909858291)
                ·
                  refine ⟨9633296908616609864787437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422197939077739909858291 9633296908616609864787437)
                  ·
                    refine ⟨3612486340731228699295289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9633296908616609864787437 3612486340731228699295289)
                    ·
                      refine ⟨2709364755548421524471467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612486340731228699295289 2709364755548421524471467)
                      ·
                        rfl

theorem cell23_5276469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_5276469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276469 prefixEnd_5276469 := by exact prefixLift 5276469
  have htrace : WordTrace (prefixWord ++ tailWord_5276469) baseStart_5276469 baseEnd_5276469 := by
    simpa [prefixWord, tailWord_5276469, baseEnd_5276469] using wordTrace_append hprefix tailTrace_5276469
  have hstable : (prefixWord ++ tailWord_5276469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276469).length < 2 ^ (prefixWord ++ tailWord_5276469).sum := by decide
  have hdescent : baseEnd_5276469 < baseStart_5276469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276505 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 7]
def baseStart_5276505 : Nat := 118140960795 + 5276505 * 2 ^ 59
def prefixEnd_5276505 : Nat := 4983230072969 + 3 ^ 40 * 5276505 * 2
def baseEnd_5276505 : Nat := 301042582316887042624589

theorem tailTrace_5276505 : CollatzResearch.WordTrace tailWord_5276505 prefixEnd_5276505 301042582316887042624589 := by
  unfold tailWord_5276505
  simp only [CollatzResearch.WordTrace]
  refine ⟨192449947749131015154470969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128299965166087343436313979 192449947749131015154470969)
  ·
    refine ⟨144337460811848261365853227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192449947749131015154470969 144337460811848261365853227)
    ·
      refine ⟨216506191217772392048779841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144337460811848261365853227 216506191217772392048779841)
      ·
        refine ⟨162379643413329294036584881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216506191217772392048779841 162379643413329294036584881)
        ·
          refine ⟨121784732559996970527438661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162379643413329294036584881 121784732559996970527438661)
          ·
            refine ⟨22834637354999431973894749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121784732559996970527438661 22834637354999431973894749)
            ·
              refine ⟨8562989008124786990210531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22834637354999431973894749 8562989008124786990210531)
              ·
                refine ⟨12844483512187180485315797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562989008124786990210531 12844483512187180485315797)
                ·
                  refine ⟨301042582316887042624589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12844483512187180485315797 301042582316887042624589)
                  ·
                    rfl

theorem cell23_5276505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_5276505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276505 prefixEnd_5276505 := by exact prefixLift 5276505
  have htrace : WordTrace (prefixWord ++ tailWord_5276505) baseStart_5276505 baseEnd_5276505 := by
    simpa [prefixWord, tailWord_5276505, baseEnd_5276505] using wordTrace_append hprefix tailTrace_5276505
  have hstable : (prefixWord ++ tailWord_5276505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276505).length < 2 ^ (prefixWord ++ tailWord_5276505).sum := by decide
  have hdescent : baseEnd_5276505 < baseStart_5276505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276516 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_5276516 : Nat := 118140960795 + 5276516 * 2 ^ 59
def prefixEnd_5276516 : Nat := 4983230072969 + 3 ^ 40 * 5276516 * 2
def baseEnd_5276516 : Nat := 2709388889139182840583751

theorem tailTrace_5276516 : CollatzResearch.WordTrace tailWord_5276516 prefixEnd_5276516 2709388889139182840583751 := by
  unfold tailWord_5276516
  simp only [CollatzResearch.WordTrace]
  refine ⟨96225174476045582016560701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128300232634727442688747601 96225174476045582016560701)
  ·
    refine ⟨36084440428517093256210263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96225174476045582016560701 36084440428517093256210263)
    ·
      refine ⟨54126660642775639884315395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36084440428517093256210263 54126660642775639884315395)
      ·
        refine ⟨81189990964163459826473093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54126660642775639884315395 81189990964163459826473093)
        ·
          refine ⟨15223123305780648717463705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81189990964163459826473093 15223123305780648717463705)
          ·
            refine ⟨11417342479335486538097779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15223123305780648717463705 11417342479335486538097779)
            ·
              refine ⟨17126013719003229807146669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11417342479335486538097779 17126013719003229807146669)
              ·
                refine ⟨6422255144626211177680001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17126013719003229807146669 6422255144626211177680001)
                ·
                  refine ⟨4816691358469658383260001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422255144626211177680001 4816691358469658383260001)
                  ·
                    refine ⟨3612518518852243787445001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816691358469658383260001 3612518518852243787445001)
                    ·
                      refine ⟨2709388889139182840583751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612518518852243787445001 2709388889139182840583751)
                      ·
                        rfl

theorem cell23_5276516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_5276516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276516 prefixEnd_5276516 := by exact prefixLift 5276516
  have htrace : WordTrace (prefixWord ++ tailWord_5276516) baseStart_5276516 baseEnd_5276516 := by
    simpa [prefixWord, tailWord_5276516, baseEnd_5276516] using wordTrace_append hprefix tailTrace_5276516
  have hstable : (prefixWord ++ tailWord_5276516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276516).length < 2 ^ (prefixWord ++ tailWord_5276516).sum := by decide
  have hdescent : baseEnd_5276516 < baseStart_5276516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276552 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5276552 : Nat := 118140960795 + 5276552 * 2 ^ 59
def prefixEnd_5276552 : Nat := 4983230072969 + 3 ^ 40 * 5276552 * 2
def baseEnd_5276552 : Nat := 903135791480914899911195

theorem tailTrace_5276552 : CollatzResearch.WordTrace tailWord_5276552 prefixEnd_5276552 903135791480914899911195 := by
  unfold tailWord_5276552
  simp only [CollatzResearch.WordTrace]
  refine ⟨96225830989980371090715955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128301107986640494787621273 96225830989980371090715955)
  ·
    refine ⟨144338746484970556636073933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96225830989980371090715955 144338746484970556636073933)
    ·
      refine ⟨54127029931863958738527725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144338746484970556636073933 54127029931863958738527725)
      ·
        refine ⟨20297636224448984526947897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54127029931863958738527725 20297636224448984526947897)
        ·
          refine ⟨15223227168336738395210923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20297636224448984526947897 15223227168336738395210923)
          ·
            refine ⟨22834840752505107592816385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223227168336738395210923 22834840752505107592816385)
            ·
              refine ⟨17126130564378830694612289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22834840752505107592816385 17126130564378830694612289)
              ·
                refine ⟨12844597923284123020959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17126130564378830694612289 12844597923284123020959217)
                ·
                  refine ⟨9633448442463092265719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12844597923284123020959217 9633448442463092265719413)
                  ·
                    refine ⟨903135791480914899911195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9633448442463092265719413 903135791480914899911195)
                    ·
                      rfl

theorem cell23_5276552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5276552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276552 prefixEnd_5276552 := by exact prefixLift 5276552
  have htrace : WordTrace (prefixWord ++ tailWord_5276552) baseStart_5276552 baseEnd_5276552 := by
    simpa [prefixWord, tailWord_5276552, baseEnd_5276552] using wordTrace_append hprefix tailTrace_5276552
  have hstable : (prefixWord ++ tailWord_5276552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276552).length < 2 ^ (prefixWord ++ tailWord_5276552).sum := by decide
  have hdescent : baseEnd_5276552 < baseStart_5276552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276566 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5276566 : Nat := 118140960795 + 5276566 * 2 ^ 59
def prefixEnd_5276566 : Nat := 4983230072969 + 3 ^ 40 * 5276566 * 2
def baseEnd_5276566 : Nat := 2709414563171907644958521

theorem tailTrace_5276566 : CollatzResearch.WordTrace tailWord_5276566 prefixEnd_5276566 2709414563171907644958521 := by
  unfold tailWord_5276566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028260787619376410777597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128301448401273348381627701 12028260787619376410777597)
  ·
    refine ⟨4510597795357266154041599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12028260787619376410777597 4510597795357266154041599)
    ·
      refine ⟨6765896693035899231062399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510597795357266154041599 6765896693035899231062399)
      ·
        refine ⟨10148845039553848846593599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6765896693035899231062399 10148845039553848846593599)
        ·
          refine ⟨15223267559330773269890399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148845039553848846593599 15223267559330773269890399)
          ·
            refine ⟨22834901338996159904835599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223267559330773269890399 22834901338996159904835599)
            ·
              refine ⟨34252352008494239857253399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22834901338996159904835599 34252352008494239857253399)
              ·
                refine ⟨51378528012741359785880099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34252352008494239857253399 51378528012741359785880099)
                ·
                  refine ⟨77067792019112039678820149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51378528012741359785880099 77067792019112039678820149)
                  ·
                    refine ⟨7225105501791753719889389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77067792019112039678820149 7225105501791753719889389)
                    ·
                      refine ⟨2709414563171907644958521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7225105501791753719889389 2709414563171907644958521)
                      ·
                        rfl

theorem cell23_5276566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5276566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276566 prefixEnd_5276566 := by exact prefixLift 5276566
  have htrace : WordTrace (prefixWord ++ tailWord_5276566) baseStart_5276566 baseEnd_5276566 := by
    simpa [prefixWord, tailWord_5276566, baseEnd_5276566] using wordTrace_append hprefix tailTrace_5276566
  have hstable : (prefixWord ++ tailWord_5276566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276566).length < 2 ^ (prefixWord ++ tailWord_5276566).sum := by decide
  have hdescent : baseEnd_5276566 < baseStart_5276566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276599 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 1, 4]
def baseStart_5276599 : Nat := 118140960795 + 5276599 * 2 ^ 59
def prefixEnd_5276599 : Nat := 4983230072969 + 3 ^ 40 * 5276599 * 2
def baseEnd_5276599 : Nat := 903143836011168671948623

theorem tailTrace_5276599 : CollatzResearch.WordTrace tailWord_5276599 prefixEnd_5276599 903143836011168671948623 := by
  unfold tailWord_5276599
  simp only [CollatzResearch.WordTrace]
  refine ⟨192453376210790469208392851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128302250807193646138928567 192453376210790469208392851)
  ·
    refine ⟨288680064316185703812589277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192453376210790469208392851 288680064316185703812589277)
    ·
      refine ⟨108255024118569638929720979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288680064316185703812589277 108255024118569638929720979)
      ·
        refine ⟨162382536177854458394581469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108255024118569638929720979 162382536177854458394581469)
        ·
          refine ⟨60893451066695421897968051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162382536177854458394581469 60893451066695421897968051)
          ·
            refine ⟨91340176600043132846952077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60893451066695421897968051 91340176600043132846952077)
            ·
              refine ⟨34252566225016174817607029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91340176600043132846952077 34252566225016174817607029)
              ·
                refine ⟨3211178083595266389150659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34252566225016174817607029 3211178083595266389150659)
                ·
                  refine ⟨4816767125392899583725989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211178083595266389150659 4816767125392899583725989)
                  ·
                    refine ⟨903143836011168671948623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816767125392899583725989 903143836011168671948623)
                    ·
                      rfl

theorem cell23_5276599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_5276599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276599 prefixEnd_5276599 := by exact prefixLift 5276599
  have htrace : WordTrace (prefixWord ++ tailWord_5276599) baseStart_5276599 baseEnd_5276599 := by
    simpa [prefixWord, tailWord_5276599, baseEnd_5276599] using wordTrace_append hprefix tailTrace_5276599
  have hstable : (prefixWord ++ tailWord_5276599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276599).length < 2 ^ (prefixWord ++ tailWord_5276599).sum := by decide
  have hdescent : baseEnd_5276599 < baseStart_5276599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276615 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_5276615 : Nat := 118140960795 + 5276615 * 2 ^ 59
def prefixEnd_5276615 : Nat := 4983230072969 + 3 ^ 40 * 5276615 * 2
def baseEnd_5276615 : Nat := 2709439723723977953245795

theorem tailTrace_5276615 : CollatzResearch.WordTrace tailWord_5276615 prefixEnd_5276615 2709439723723977953245795 := by
  unfold tailWord_5276615
  simp only [CollatzResearch.WordTrace]
  refine ⟨192453959778732503940975299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128302639852488335960650199 192453959778732503940975299)
  ·
    refine ⟨288680939668098755911462949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192453959778732503940975299 288680939668098755911462949)
    ·
      refine ⟨54127676187768516733399303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288680939668098755911462949 54127676187768516733399303)
      ·
        refine ⟨81191514281652775100098955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54127676187768516733399303 81191514281652775100098955)
        ·
          refine ⟨121787271422479162650148433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81191514281652775100098955 121787271422479162650148433)
          ·
            refine ⟨91340453566859371987611325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121787271422479162650148433 91340453566859371987611325)
            ·
              refine ⟨34252670087572264495354247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91340453566859371987611325 34252670087572264495354247)
              ·
                refine ⟨51379005131358396743031371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34252670087572264495354247 51379005131358396743031371)
                ·
                  refine ⟨77068507697037595114547057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51379005131358396743031371 77068507697037595114547057)
                  ·
                    refine ⟨57801380772778196335910293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77068507697037595114547057 57801380772778196335910293)
                    ·
                      refine ⟨2709439723723977953245795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57801380772778196335910293 2709439723723977953245795)
                      ·
                        rfl

theorem cell23_5276615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_5276615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276615 prefixEnd_5276615 := by exact prefixLift 5276615
  have htrace : WordTrace (prefixWord ++ tailWord_5276615) baseStart_5276615 baseEnd_5276615 := by
    simpa [prefixWord, tailWord_5276615, baseEnd_5276615] using wordTrace_append hprefix tailTrace_5276615
  have hstable : (prefixWord ++ tailWord_5276615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276615).length < 2 ^ (prefixWord ++ tailWord_5276615).sum := by decide
  have hdescent : baseEnd_5276615 < baseStart_5276615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276696 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5276696 : Nat := 118140960795 + 5276696 * 2 ^ 59
def prefixEnd_5276696 : Nat := 4983230072969 + 3 ^ 40 * 5276696 * 2
def baseEnd_5276696 : Nat := 2709481315656992136332923

theorem tailTrace_5276696 : CollatzResearch.WordTrace tailWord_5276696 prefixEnd_5276696 2709481315656992136332923 := by
  unfold tailWord_5276696
  simp only [CollatzResearch.WordTrace]
  refine ⟨96228457045719527387336971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128304609394292703183115961 96228457045719527387336971)
  ·
    refine ⟨144342685568579291081005457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96228457045719527387336971 144342685568579291081005457)
    ·
      refine ⟨108257014176434468310754093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144342685568579291081005457 108257014176434468310754093)
      ·
        refine ⟨40596380316162925616532785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108257014176434468310754093 40596380316162925616532785)
        ·
          refine ⟨30447285237122194212399589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40596380316162925616532785 30447285237122194212399589)
          ·
            refine ⟨5708865981960411414824923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30447285237122194212399589 5708865981960411414824923)
            ·
              refine ⟨8563298972940617122237385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708865981960411414824923 8563298972940617122237385)
              ·
                refine ⟨6422474229705462841678039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563298972940617122237385 6422474229705462841678039)
                ·
                  refine ⟨9633711344558194262517059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422474229705462841678039 9633711344558194262517059)
                  ·
                    refine ⟨14450567016837291393775589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9633711344558194262517059 14450567016837291393775589)
                    ·
                      refine ⟨2709481315656992136332923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14450567016837291393775589 2709481315656992136332923)
                      ·
                        rfl

theorem cell23_5276696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5276696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276696 prefixEnd_5276696 := by exact prefixLift 5276696
  have htrace : WordTrace (prefixWord ++ tailWord_5276696) baseStart_5276696 baseEnd_5276696 := by
    simpa [prefixWord, tailWord_5276696, baseEnd_5276696] using wordTrace_append hprefix tailTrace_5276696
  have hstable : (prefixWord ++ tailWord_5276696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276696).length < 2 ^ (prefixWord ++ tailWord_5276696).sum := by decide
  have hdescent : baseEnd_5276696 < baseStart_5276696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276716 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_5276716 : Nat := 118140960795 + 5276716 * 2 ^ 59
def prefixEnd_5276716 : Nat := 4983230072969 + 3 ^ 40 * 5276716 * 2
def baseEnd_5276716 : Nat := 2709491585270082058082831

theorem tailTrace_5276716 : CollatzResearch.WordTrace tailWord_5276716 prefixEnd_5276716 2709491585270082058082831 := by
  unfold tailWord_5276716
  simp only [CollatzResearch.WordTrace]
  refine ⟨96228821775683299095201001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128305095700911065460268001 96228821775683299095201001)
  ·
    refine ⟨72171616331762474321400751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96228821775683299095201001 72171616331762474321400751)
    ·
      refine ⟨108257424497643711482101127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72171616331762474321400751 108257424497643711482101127)
      ·
        refine ⟨162386136746465567223151691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108257424497643711482101127 162386136746465567223151691)
        ·
          refine ⟨243579205119698350834727537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162386136746465567223151691 243579205119698350834727537)
          ·
            refine ⟨182684403839773763126045653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243579205119698350834727537 182684403839773763126045653)
            ·
              refine ⟨4281665714994697573266695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182684403839773763126045653 4281665714994697573266695)
              ·
                refine ⟨6422498572492046359900043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281665714994697573266695 6422498572492046359900043)
                ·
                  refine ⟨9633747858738069539850065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422498572492046359900043 9633747858738069539850065)
                  ·
                    refine ⟨7225310894053552154887549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9633747858738069539850065 7225310894053552154887549)
                    ·
                      refine ⟨2709491585270082058082831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7225310894053552154887549 2709491585270082058082831)
                      ·
                        rfl

theorem cell23_5276716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_5276716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276716 prefixEnd_5276716 := by exact prefixLift 5276716
  have htrace : WordTrace (prefixWord ++ tailWord_5276716) baseStart_5276716 baseEnd_5276716 := by
    simpa [prefixWord, tailWord_5276716, baseEnd_5276716] using wordTrace_append hprefix tailTrace_5276716
  have hstable : (prefixWord ++ tailWord_5276716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276716).length < 2 ^ (prefixWord ++ tailWord_5276716).sum := by decide
  have hdescent : baseEnd_5276716 < baseStart_5276716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276730 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_5276730 : Nat := 118140960795 + 5276730 * 2 ^ 59
def prefixEnd_5276730 : Nat := 4983230072969 + 3 ^ 40 * 5276730 * 2
def baseEnd_5276730 : Nat := 2709498773999245003307767

theorem tailTrace_5276730 : CollatzResearch.WordTrace tailWord_5276730 prefixEnd_5276730 2709498773999245003307767 := by
  unfold tailWord_5276730
  simp only [CollatzResearch.WordTrace]
  refine ⟨48114538543328969645352911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128305436115543919054274429 48114538543328969645352911)
  ·
    refine ⟨72171807814993454468029367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48114538543328969645352911 72171807814993454468029367)
    ·
      refine ⟨108257711722490181702044051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72171807814993454468029367 108257711722490181702044051)
      ·
        refine ⟨162386567583735272553066077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108257711722490181702044051 162386567583735272553066077)
        ·
          refine ⟨60894962843900727207399779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162386567583735272553066077 60894962843900727207399779)
          ·
            refine ⟨91342444265851090811099669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60894962843900727207399779 91342444265851090811099669)
            ·
              refine ⟨4281677074961769881770297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91342444265851090811099669 4281677074961769881770297)
              ·
                refine ⟨3211257806221327411327723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4281677074961769881770297 3211257806221327411327723)
                ·
                  refine ⟨4816886709331991116991585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211257806221327411327723 4816886709331991116991585)
                  ·
                    refine ⟨3612665031998993337743689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816886709331991116991585 3612665031998993337743689)
                    ·
                      refine ⟨2709498773999245003307767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612665031998993337743689 2709498773999245003307767)
                      ·
                        rfl

theorem cell23_5276730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_5276730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276730 prefixEnd_5276730 := by exact prefixLift 5276730
  have htrace : WordTrace (prefixWord ++ tailWord_5276730) baseStart_5276730 baseEnd_5276730 := by
    simpa [prefixWord, tailWord_5276730, baseEnd_5276730] using wordTrace_append hprefix tailTrace_5276730
  have hstable : (prefixWord ++ tailWord_5276730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276730).length < 2 ^ (prefixWord ++ tailWord_5276730).sum := by decide
  have hdescent : baseEnd_5276730 < baseStart_5276730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276732 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_5276732 : Nat := 118140960795 + 5276732 * 2 ^ 59
def prefixEnd_5276732 : Nat := 4983230072969 + 3 ^ 40 * 5276732 * 2
def baseEnd_5276732 : Nat := 903166600320184665160919

theorem tailTrace_5276732 : CollatzResearch.WordTrace tailWord_5276732 prefixEnd_5276732 903166600320184665160919 := by
  unfold tailWord_5276732
  simp only [CollatzResearch.WordTrace]
  refine ⟨96229113559654316461492225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128305484746205755281989633 96229113559654316461492225)
  ·
    refine ⟨72171835169740737346119169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96229113559654316461492225 72171835169740737346119169)
    ·
      refine ⟨54128876377305553009589377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72171835169740737346119169 54128876377305553009589377)
      ·
        refine ⟨40596657282979164757192033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54128876377305553009589377 40596657282979164757192033)
        ·
          refine ⟨30447492962234373567894025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40596657282979164757192033 30447492962234373567894025)
          ·
            refine ⟨22835619721675780175920519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30447492962234373567894025 22835619721675780175920519)
            ·
              refine ⟨34253429582513670263880779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22835619721675780175920519 34253429582513670263880779)
              ·
                refine ⟨51380144373770505395821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34253429582513670263880779 51380144373770505395821169)
                ·
                  refine ⟨38535108280327879046865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51380144373770505395821169 38535108280327879046865877)
                  ·
                    refine ⟨903166600320184665160919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38535108280327879046865877 903166600320184665160919)
                    ·
                      rfl

theorem cell23_5276732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_5276732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276732 prefixEnd_5276732 := by exact prefixLift 5276732
  have htrace : WordTrace (prefixWord ++ tailWord_5276732) baseStart_5276732 baseEnd_5276732 := by
    simpa [prefixWord, tailWord_5276732, baseEnd_5276732] using wordTrace_append hprefix tailTrace_5276732
  have hstable : (prefixWord ++ tailWord_5276732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276732).length < 2 ^ (prefixWord ++ tailWord_5276732).sum := by decide
  have hdescent : baseEnd_5276732 < baseStart_5276732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276739 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 5, 3, 2]
def baseStart_5276739 : Nat := 118140960795 + 5276739 * 2 ^ 59
def prefixEnd_5276739 : Nat := 4983230072969 + 3 ^ 40 * 5276739 * 2
def baseEnd_5276739 : Nat := 2709503395325135468095225

theorem tailTrace_5276739 : CollatzResearch.WordTrace tailWord_5276739 prefixEnd_5276739 2709503395325135468095225 := by
  unfold tailWord_5276739
  simp only [CollatzResearch.WordTrace]
  refine ⟨192458482430283273118489271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128305654953522182078992847 192458482430283273118489271)
  ·
    refine ⟨288687723645424909677733907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192458482430283273118489271 288687723645424909677733907)
    ·
      refine ⟨433031585468137364516600861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288687723645424909677733907 433031585468137364516600861)
      ·
        refine ⟨162386844550551511693725323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433031585468137364516600861 162386844550551511693725323)
        ·
          refine ⟨243580266825827267540587985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162386844550551511693725323 243580266825827267540587985)
          ·
            refine ⟨182685200119370450655440989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243580266825827267540587985 182685200119370450655440989)
            ·
              refine ⟨68506950044763918995790371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182685200119370450655440989 68506950044763918995790371)
              ·
                refine ⟨102760425067145878493685557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68506950044763918995790371 102760425067145878493685557)
                ·
                  refine ⟨9633789850044926108783021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102760425067145878493685557 9633789850044926108783021)
                  ·
                    refine ⟨3612671193766847290793633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9633789850044926108783021 3612671193766847290793633)
                    ·
                      refine ⟨2709503395325135468095225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612671193766847290793633 2709503395325135468095225)
                      ·
                        rfl

theorem cell23_5276739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_5276739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276739 prefixEnd_5276739 := by exact prefixLift 5276739
  have htrace : WordTrace (prefixWord ++ tailWord_5276739) baseStart_5276739 baseEnd_5276739 := by
    simpa [prefixWord, tailWord_5276739, baseEnd_5276739] using wordTrace_append hprefix tailTrace_5276739
  have hstable : (prefixWord ++ tailWord_5276739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276739).length < 2 ^ (prefixWord ++ tailWord_5276739).sum := by decide
  have hdescent : baseEnd_5276739 < baseStart_5276739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276746 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_5276746 : Nat := 118140960795 + 5276746 * 2 ^ 59
def prefixEnd_5276746 : Nat := 4983230072969 + 3 ^ 40 * 5276746 * 2
def baseEnd_5276746 : Nat := 2709506989689716940707693

theorem tailTrace_5276746 : CollatzResearch.WordTrace tailWord_5276746 prefixEnd_5276746 2709506989689716940707693 := by
  unfold tailWord_5276746
  simp only [CollatzResearch.WordTrace]
  refine ⟨48114684435314478328498523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128305825160838608875996061 48114684435314478328498523)
  ·
    refine ⟨72172026652971717492747785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48114684435314478328498523 72172026652971717492747785)
    ·
      refine ⟨54129019989728788119560839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72172026652971717492747785 54129019989728788119560839)
      ·
        refine ⟨81193529984593182179341259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54129019989728788119560839 81193529984593182179341259)
        ·
          refine ⟨121790294976889773269011889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81193529984593182179341259 121790294976889773269011889)
          ·
            refine ⟨91342721232667329951758917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121790294976889773269011889 91342721232667329951758917)
            ·
              refine ⟨17126760231125124365954797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91342721232667329951758917 17126760231125124365954797)
              ·
                refine ⟨6422535086671921637233049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17126760231125124365954797 6422535086671921637233049)
                ·
                  refine ⟨4816901315003941227924787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422535086671921637233049 4816901315003941227924787)
                  ·
                    refine ⟨7225351972505911841887181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816901315003941227924787 7225351972505911841887181)
                    ·
                      refine ⟨2709506989689716940707693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7225351972505911841887181 2709506989689716940707693)
                      ·
                        rfl

theorem cell23_5276746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_5276746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276746 prefixEnd_5276746 := by exact prefixLift 5276746
  have htrace : WordTrace (prefixWord ++ tailWord_5276746) baseStart_5276746 baseEnd_5276746 := by
    simpa [prefixWord, tailWord_5276746, baseEnd_5276746] using wordTrace_append hprefix tailTrace_5276746
  have hstable : (prefixWord ++ tailWord_5276746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276746).length < 2 ^ (prefixWord ++ tailWord_5276746).sum := by decide
  have hdescent : baseEnd_5276746 < baseStart_5276746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276756 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_5276756 : Nat := 118140960795 + 5276756 * 2 ^ 59
def prefixEnd_5276756 : Nat := 4983230072969 + 3 ^ 40 * 5276756 * 2
def baseEnd_5276756 : Nat := 2709512124496261901582647

theorem tailTrace_5276756 : CollatzResearch.WordTrace tailWord_5276756 prefixEnd_5276756 2709512124496261901582647 := by
  unfold tailWord_5276756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96229551235610842510929061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128306068314147790014572081 96229551235610842510929061)
  ·
    refine ⟨18043040856677032970799199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96229551235610842510929061 18043040856677032970799199)
    ·
      refine ⟨27064561285015549456198799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18043040856677032970799199 27064561285015549456198799)
      ·
        refine ⟨40596841927523324184298199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064561285015549456198799 40596841927523324184298199)
        ·
          refine ⟨60895262891284986276447299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40596841927523324184298199 60895262891284986276447299)
          ·
            refine ⟨91342894336927479414670949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60895262891284986276447299 91342894336927479414670949)
            ·
              refine ⟨17126792688173902390250803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91342894336927479414670949 17126792688173902390250803)
              ·
                refine ⟨25690189032260853585376205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17126792688173902390250803 25690189032260853585376205)
                ·
                  refine ⟨9633820887097820094516077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25690189032260853585376205 9633820887097820094516077)
                  ·
                    refine ⟨3612682832661682535443529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9633820887097820094516077 3612682832661682535443529)
                    ·
                      refine ⟨2709512124496261901582647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612682832661682535443529 2709512124496261901582647)
                      ·
                        rfl

theorem cell23_5276756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_5276756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276756 prefixEnd_5276756 := by exact prefixLift 5276756
  have htrace : WordTrace (prefixWord ++ tailWord_5276756) baseStart_5276756 baseEnd_5276756 := by
    simpa [prefixWord, tailWord_5276756, baseEnd_5276756] using wordTrace_append hprefix tailTrace_5276756
  have hstable : (prefixWord ++ tailWord_5276756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276756).length < 2 ^ (prefixWord ++ tailWord_5276756).sum := by decide
  have hdescent : baseEnd_5276756 < baseStart_5276756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276772 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_5276772 : Nat := 118140960795 + 5276772 * 2 ^ 59
def prefixEnd_5276772 : Nat := 4983230072969 + 3 ^ 40 * 5276772 * 2
def baseEnd_5276772 : Nat := 2709520340186733838982573

theorem tailTrace_5276772 : CollatzResearch.WordTrace tailWord_5276772 prefixEnd_5276772 2709520340186733838982573 := by
  unfold tailWord_5276772
  simp only [CollatzResearch.WordTrace]
  refine ⟨96229843019581859877220285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128306457359442479836293713 96229843019581859877220285)
  ·
    refine ⟨36086191132343197453957607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96229843019581859877220285 36086191132343197453957607)
    ·
      refine ⟨54129286698514796180936411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36086191132343197453957607 54129286698514796180936411)
      ·
        refine ⟨81193930047772194271404617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54129286698514796180936411 81193930047772194271404617)
        ·
          refine ⟨60895447535829145703553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81193930047772194271404617 60895447535829145703553463)
          ·
            refine ⟨91343171303743718555330195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60895447535829145703553463 91343171303743718555330195)
            ·
              refine ⟨137014756955615577832995293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91343171303743718555330195 137014756955615577832995293)
              ·
                refine ⟨51380533858355841687373235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137014756955615577832995293 51380533858355841687373235)
                ·
                  refine ⟨77070800787533762531059853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51380533858355841687373235 77070800787533762531059853)
                  ·
                    refine ⟨28901550295325160949147445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77070800787533762531059853 28901550295325160949147445)
                    ·
                      refine ⟨2709520340186733838982573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28901550295325160949147445 2709520340186733838982573)
                      ·
                        rfl

theorem cell23_5276772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_5276772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276772 prefixEnd_5276772 := by exact prefixLift 5276772
  have htrace : WordTrace (prefixWord ++ tailWord_5276772) baseStart_5276772 baseEnd_5276772 := by
    simpa [prefixWord, tailWord_5276772, baseEnd_5276772] using wordTrace_append hprefix tailTrace_5276772
  have hstable : (prefixWord ++ tailWord_5276772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276772).length < 2 ^ (prefixWord ++ tailWord_5276772).sum := by decide
  have hdescent : baseEnd_5276772 < baseStart_5276772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276792 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 7]
def baseStart_5276792 : Nat := 118140960795 + 5276792 * 2 ^ 59
def prefixEnd_5276792 : Nat := 4983230072969 + 3 ^ 40 * 5276792 * 2
def baseEnd_5276792 : Nat := 301058956644424862303609

theorem tailTrace_5276792 : CollatzResearch.WordTrace tailWord_5276792 prefixEnd_5276792 301058956644424862303609 := by
  unfold tailWord_5276792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96230207749545631585084315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128306943666060842113445753 96230207749545631585084315)
  ·
    refine ⟨144345311624318447377626473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96230207749545631585084315 144345311624318447377626473)
    ·
      refine ⟨108258983718238835533219855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144345311624318447377626473 108258983718238835533219855)
      ·
        refine ⟨162388475577358253299829783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108258983718238835533219855 162388475577358253299829783)
        ·
          refine ⟨243582713366037379949744675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162388475577358253299829783 243582713366037379949744675)
          ·
            refine ⟨365374070049056069924617013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243582713366037379949744675 365374070049056069924617013)
            ·
              refine ⟨34253819067099006555432845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365374070049056069924617013 34253819067099006555432845)
              ·
                refine ⟨12845182150162127458287317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34253819067099006555432845 12845182150162127458287317)
                ·
                  refine ⟨301058956644424862303609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12845182150162127458287317 301058956644424862303609)
                  ·
                    rfl

theorem cell23_5276792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_5276792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276792 prefixEnd_5276792 := by exact prefixLift 5276792
  have htrace : WordTrace (prefixWord ++ tailWord_5276792) baseStart_5276792 baseEnd_5276792 := by
    simpa [prefixWord, tailWord_5276792, baseEnd_5276792] using wordTrace_append hprefix tailTrace_5276792
  have hstable : (prefixWord ++ tailWord_5276792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276792).length < 2 ^ (prefixWord ++ tailWord_5276792).sum := by decide
  have hdescent : baseEnd_5276792 < baseStart_5276792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276849 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5276849 : Nat := 118140960795 + 5276849 * 2 ^ 59
def prefixEnd_5276849 : Nat := 4983230072969 + 3 ^ 40 * 5276849 * 2
def baseEnd_5276849 : Nat := 2709559878197130037719719

theorem tailTrace_5276849 : CollatzResearch.WordTrace tailWord_5276849 prefixEnd_5276849 2709559878197130037719719 := by
  unfold tailWord_5276849
  simp only [CollatzResearch.WordTrace]
  refine ⟨192462494459884761904993601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128308329639923174603329067 192462494459884761904993601)
  ·
    refine ⟨144346870844913571428745201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192462494459884761904993601 144346870844913571428745201)
    ·
      refine ⟨108260153133685178571558901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144346870844913571428745201 108260153133685178571558901)
      ·
        refine ⟨10149389356282985491083647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108260153133685178571558901 10149389356282985491083647)
        ·
          refine ⟨15224084034424478236625471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149389356282985491083647 15224084034424478236625471)
          ·
            refine ⟨22836126051636717354938207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15224084034424478236625471 22836126051636717354938207)
            ·
              refine ⟨34254189077455076032407311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22836126051636717354938207 34254189077455076032407311)
              ·
                refine ⟨51381283616182614048610967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34254189077455076032407311 51381283616182614048610967)
                ·
                  refine ⟨77071925424273921072916451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51381283616182614048610967 77071925424273921072916451)
                  ·
                    refine ⟨115607888136410881609374677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77071925424273921072916451 115607888136410881609374677)
                    ·
                      refine ⟨2709559878197130037719719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115607888136410881609374677 2709559878197130037719719)
                      ·
                        rfl

theorem cell23_5276849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5276849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276849 prefixEnd_5276849 := by exact prefixLift 5276849
  have htrace : WordTrace (prefixWord ++ tailWord_5276849) baseStart_5276849 baseEnd_5276849 := by
    simpa [prefixWord, tailWord_5276849, baseEnd_5276849] using wordTrace_append hprefix tailTrace_5276849
  have hstable : (prefixWord ++ tailWord_5276849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276849).length < 2 ^ (prefixWord ++ tailWord_5276849).sum := by decide
  have hdescent : baseEnd_5276849 < baseStart_5276849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276854 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5276854 : Nat := 118140960795 + 5276854 * 2 ^ 59
def prefixEnd_5276854 : Nat := 4983230072969 + 3 ^ 40 * 5276854 * 2
def baseEnd_5276854 : Nat := 2709562445600402518157197

theorem tailTrace_5276854 : CollatzResearch.WordTrace tailWord_5276854 prefixEnd_5276854 2709562445600402518157197 := by
  unfold tailWord_5276854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028917301554165484932851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128308451216577765172617077 12028917301554165484932851)
  ·
    refine ⟨18043375952331248227399277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12028917301554165484932851 18043375952331248227399277)
    ·
      refine ⟨6766265982124218085274729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18043375952331248227399277 6766265982124218085274729)
      ·
        refine ⟨5074699486593163563956047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6766265982124218085274729 5074699486593163563956047)
        ·
          refine ⟨7612049229889745345934071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074699486593163563956047 7612049229889745345934071)
          ·
            refine ⟨11418073844834618018901107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612049229889745345934071 11418073844834618018901107)
            ·
              refine ⟨17127110767251927028351661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11418073844834618018901107 17127110767251927028351661)
              ·
                refine ⟨6422666537719472635631873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17127110767251927028351661 6422666537719472635631873)
                ·
                  refine ⟨4816999903289604476723905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422666537719472635631873 4816999903289604476723905)
                  ·
                    refine ⟨3612749927467203357542929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4816999903289604476723905 3612749927467203357542929)
                    ·
                      refine ⟨2709562445600402518157197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612749927467203357542929 2709562445600402518157197)
                      ·
                        rfl

theorem cell23_5276854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5276854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276854 prefixEnd_5276854 := by exact prefixLift 5276854
  have htrace : WordTrace (prefixWord ++ tailWord_5276854) baseStart_5276854 baseEnd_5276854 := by
    simpa [prefixWord, tailWord_5276854, baseEnd_5276854] using wordTrace_append hprefix tailTrace_5276854
  have hstable : (prefixWord ++ tailWord_5276854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276854).length < 2 ^ (prefixWord ++ tailWord_5276854).sum := by decide
  have hdescent : baseEnd_5276854 < baseStart_5276854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276869 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_5276869 : Nat := 118140960795 + 5276869 * 2 ^ 59
def prefixEnd_5276869 : Nat := 4983230072969 + 3 ^ 40 * 5276869 * 2
def baseEnd_5276869 : Nat := 903190049270073319823209

theorem tailTrace_5276869 : CollatzResearch.WordTrace tailWord_5276869 prefixEnd_5276869 903190049270073319823209 := by
  unfold tailWord_5276869
  simp only [CollatzResearch.WordTrace]
  refine ⟨192463223919812305320721661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128308815946541536880481107 192463223919812305320721661)
  ·
    refine ⟨72173708969929614495270623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192463223919812305320721661 72173708969929614495270623)
    ·
      refine ⟨108260563454894421742905935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72173708969929614495270623 108260563454894421742905935)
      ·
        refine ⟨162390845182341632614358903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108260563454894421742905935 162390845182341632614358903)
        ·
          refine ⟨243586267773512448921538355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162390845182341632614358903 243586267773512448921538355)
          ·
            refine ⟨365379401660268673382307533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243586267773512448921538355 365379401660268673382307533)
            ·
              refine ⟨137017275622600752518365325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365379401660268673382307533 137017275622600752518365325)
              ·
                refine ⟨51381478358475282194386997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137017275622600752518365325 51381478358475282194386997)
                ·
                  refine ⟨4817013596107057705723781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51381478358475282194386997 4817013596107057705723781)
                  ·
                    refine ⟨903190049270073319823209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817013596107057705723781 903190049270073319823209)
                    ·
                      rfl

theorem cell23_5276869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_5276869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276869 prefixEnd_5276869 := by exact prefixLift 5276869
  have htrace : WordTrace (prefixWord ++ tailWord_5276869) baseStart_5276869 baseEnd_5276869 := by
    simpa [prefixWord, tailWord_5276869, baseEnd_5276869] using wordTrace_append hprefix tailTrace_5276869
  have hstable : (prefixWord ++ tailWord_5276869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276869).length < 2 ^ (prefixWord ++ tailWord_5276869).sum := by decide
  have hdescent : baseEnd_5276869 < baseStart_5276869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276896 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_5276896 : Nat := 118140960795 + 5276896 * 2 ^ 59
def prefixEnd_5276896 : Nat := 4983230072969 + 3 ^ 40 * 5276896 * 2
def baseEnd_5276896 : Nat := 2709584011787891353832003

theorem tailTrace_5276896 : CollatzResearch.WordTrace tailWord_5276896 prefixEnd_5276896 2709584011787891353832003 := by
  unfold tailWord_5276896
  simp only [CollatzResearch.WordTrace]
  refine ⟨96232104345357244465977271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128309472460476325954636361 96232104345357244465977271)
  ·
    refine ⟨144348156518035866698965907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96232104345357244465977271 144348156518035866698965907)
    ·
      refine ⟨216522234777053800048448861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144348156518035866698965907 216522234777053800048448861)
      ·
        refine ⟨81195838041395175018168323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216522234777053800048448861 81195838041395175018168323)
        ·
          refine ⟨121793757062092762527252485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81195838041395175018168323 121793757062092762527252485)
          ·
            refine ⟨22836329449142392973859841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121793757062092762527252485 22836329449142392973859841)
            ·
              refine ⟨17127247086856794730394881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22836329449142392973859841 17127247086856794730394881)
              ·
                refine ⟨12845435315142596047796161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17127247086856794730394881 12845435315142596047796161)
                ·
                  refine ⟨9634076486356947035847121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12845435315142596047796161 9634076486356947035847121)
                  ·
                    refine ⟨7225557364767710276885341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9634076486356947035847121 7225557364767710276885341)
                    ·
                      refine ⟨2709584011787891353832003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7225557364767710276885341 2709584011787891353832003)
                      ·
                        rfl

theorem cell23_5276896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_5276896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276896 prefixEnd_5276896 := by exact prefixLift 5276896
  have htrace : WordTrace (prefixWord ++ tailWord_5276896) baseStart_5276896 baseEnd_5276896 := by
    simpa [prefixWord, tailWord_5276896, baseEnd_5276896] using wordTrace_append hprefix tailTrace_5276896
  have hstable : (prefixWord ++ tailWord_5276896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276896).length < 2 ^ (prefixWord ++ tailWord_5276896).sum := by decide
  have hdescent : baseEnd_5276896 < baseStart_5276896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276960 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5276960 : Nat := 118140960795 + 5276960 * 2 ^ 59
def prefixEnd_5276960 : Nat := 4983230072969 + 3 ^ 40 * 5276960 * 2
def baseEnd_5276960 : Nat := 2709616874549779103431709

theorem tailTrace_5276960 : CollatzResearch.WordTrace tailWord_5276960 prefixEnd_5276960 2709616874549779103431709 := by
  unfold tailWord_5276960
  simp only [CollatzResearch.WordTrace]
  refine ⟨96233271481241313931142167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128311028641655085241522889 96233271481241313931142167)
  ·
    refine ⟨144349907221861970896713251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96233271481241313931142167 144349907221861970896713251)
    ·
      refine ⟨216524860832792956345069877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144349907221861970896713251 216524860832792956345069877)
      ·
        refine ⟨20299205703074339657350301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216524860832792956345069877 20299205703074339657350301)
        ·
          refine ⟨7612202138652877371506363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20299205703074339657350301 7612202138652877371506363)
          ·
            refine ⟨11418303207979316057259545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612202138652877371506363 11418303207979316057259545)
            ·
              refine ⟨8563727405984487042944659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11418303207979316057259545 8563727405984487042944659)
              ·
                refine ⟨12845591108976730564416989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563727405984487042944659 12845591108976730564416989)
                ·
                  refine ⟨4817096665866273961656371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12845591108976730564416989 4817096665866273961656371)
                  ·
                    refine ⟨7225644998799410942484557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817096665866273961656371 7225644998799410942484557)
                    ·
                      refine ⟨2709616874549779103431709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7225644998799410942484557 2709616874549779103431709)
                      ·
                        rfl

theorem cell23_5276960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5276960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276960 prefixEnd_5276960 := by exact prefixLift 5276960
  have htrace : WordTrace (prefixWord ++ tailWord_5276960) baseStart_5276960 baseEnd_5276960 := by
    simpa [prefixWord, tailWord_5276960, baseEnd_5276960] using wordTrace_append hprefix tailTrace_5276960
  have hstable : (prefixWord ++ tailWord_5276960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276960).length < 2 ^ (prefixWord ++ tailWord_5276960).sum := by decide
  have hdescent : baseEnd_5276960 < baseStart_5276960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5276993 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5276993 : Nat := 118140960795 + 5276993 * 2 ^ 59
def prefixEnd_5276993 : Nat := 4983230072969 + 3 ^ 40 * 5276993 * 2
def baseEnd_5276993 : Nat := 903211273137125824773019

theorem tailTrace_5276993 : CollatzResearch.WordTrace tailWord_5276993 prefixEnd_5276993 903211273137125824773019 := by
  unfold tailWord_5276993
  simp only [CollatzResearch.WordTrace]
  refine ⟨192467746571363074498235633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128311831047575382998823755 192467746571363074498235633)
  ·
    refine ⟨144350809928522305873676725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192467746571363074498235633 144350809928522305873676725)
    ·
      refine ⟨13532888430798966175657193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144350809928522305873676725 13532888430798966175657193)
      ·
        refine ⟨10149666323099224631742895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13532888430798966175657193 10149666323099224631742895)
        ·
          refine ⟨15224499484648836947614343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149666323099224631742895 15224499484648836947614343)
          ·
            refine ⟨22836749226973255421421515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15224499484648836947614343 22836749226973255421421515)
            ·
              refine ⟨34255123840459883132132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22836749226973255421421515 34255123840459883132132273)
              ·
                refine ⟨25691342880344912349099205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34255123840459883132132273 25691342880344912349099205)
                ·
                  refine ⟨4817126790064671065456101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25691342880344912349099205 4817126790064671065456101)
                  ·
                    refine ⟨903211273137125824773019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817126790064671065456101 903211273137125824773019)
                    ·
                      rfl

theorem cell23_5276993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5276993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5276993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5276993 prefixEnd_5276993 := by exact prefixLift 5276993
  have htrace : WordTrace (prefixWord ++ tailWord_5276993) baseStart_5276993 baseEnd_5276993 := by
    simpa [prefixWord, tailWord_5276993, baseEnd_5276993] using wordTrace_append hprefix tailTrace_5276993
  have hstable : (prefixWord ++ tailWord_5276993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5276993).length < 2 ^ (prefixWord ++ tailWord_5276993).sum := by decide
  have hdescent : baseEnd_5276993 < baseStart_5276993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5276993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277026 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5277026 : Nat := 118140960795 + 5277026 * 2 ^ 59
def prefixEnd_5277026 : Nat := 4983230072969 + 3 ^ 40 * 5277026 * 2
def baseEnd_5277026 : Nat := 2709650764272975845206405

theorem tailTrace_5277026 : CollatzResearch.WordTrace tailWord_5277026 prefixEnd_5277026 2709650764272975845206405 := by
  unfold tailWord_5277026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117237545060880283546733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128312633453495680756124621 48117237545060880283546733)
  ·
    refine ⟨18043964079397830106330025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48117237545060880283546733 18043964079397830106330025)
    ·
      refine ⟨13532973059548372579747519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18043964079397830106330025 13532973059548372579747519)
      ·
        refine ⟨20299459589322558869621279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13532973059548372579747519 20299459589322558869621279)
        ·
          refine ⟨30449189383983838304431919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20299459589322558869621279 30449189383983838304431919)
          ·
            refine ⟨45673784075975757456647879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30449189383983838304431919 45673784075975757456647879)
            ·
              refine ⟨68510676113963636184971819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45673784075975757456647879 68510676113963636184971819)
              ·
                refine ⟨102766014170945454277457729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68510676113963636184971819 102766014170945454277457729)
                ·
                  refine ⟨77074510628209090708093297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102766014170945454277457729 77074510628209090708093297)
                  ·
                    refine ⟨57805882971156818031069973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77074510628209090708093297 57805882971156818031069973)
                    ·
                      refine ⟨2709650764272975845206405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57805882971156818031069973 2709650764272975845206405)
                      ·
                        rfl

theorem cell23_5277026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5277026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277026 prefixEnd_5277026 := by exact prefixLift 5277026
  have htrace : WordTrace (prefixWord ++ tailWord_5277026) baseStart_5277026 baseEnd_5277026 := by
    simpa [prefixWord, tailWord_5277026, baseEnd_5277026] using wordTrace_append hprefix tailTrace_5277026
  have hstable : (prefixWord ++ tailWord_5277026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277026).length < 2 ^ (prefixWord ++ tailWord_5277026).sum := by decide
  have hdescent : baseEnd_5277026 < baseStart_5277026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277054 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5277054 : Nat := 118140960795 + 5277054 * 2 ^ 59
def prefixEnd_5277054 : Nat := 4983230072969 + 3 ^ 40 * 5277054 * 2
def baseEnd_5277054 : Nat := 2709665141731301735656277

theorem tailTrace_5277054 : CollatzResearch.WordTrace tailWord_5277054 prefixEnd_5277054 2709665141731301735656277 := by
  unfold tailWord_5277054
  simp only [CollatzResearch.WordTrace]
  refine ⟨24058746428017760239525777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128313314282761387944137477 24058746428017760239525777)
  ·
    refine ⟨18044059821013320179644333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24058746428017760239525777 18044059821013320179644333)
    ·
      refine ⟨6766522432879995067366625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18044059821013320179644333 6766522432879995067366625)
      ·
        refine ⟨5074891824659996300524969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6766522432879995067366625 5074891824659996300524969)
        ·
          refine ⟨3806168868494997225393727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074891824659996300524969 3806168868494997225393727)
          ·
            refine ⟨5709253302742495838090591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806168868494997225393727 5709253302742495838090591)
            ·
              refine ⟨8563879954113743757135887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709253302742495838090591 8563879954113743757135887)
              ·
                refine ⟨12845819931170615635703831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563879954113743757135887 12845819931170615635703831)
                ·
                  refine ⟨19268729896755923453555747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12845819931170615635703831 19268729896755923453555747)
                  ·
                    refine ⟨28903094845133885180333621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19268729896755923453555747 28903094845133885180333621)
                    ·
                      refine ⟨2709665141731301735656277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28903094845133885180333621 2709665141731301735656277)
                      ·
                        rfl

theorem cell23_5277054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5277054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277054 prefixEnd_5277054 := by exact prefixLift 5277054
  have htrace : WordTrace (prefixWord ++ tailWord_5277054) baseStart_5277054 baseEnd_5277054 := by
    simpa [prefixWord, tailWord_5277054, baseEnd_5277054] using wordTrace_append hprefix tailTrace_5277054
  have hstable : (prefixWord ++ tailWord_5277054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277054).length < 2 ^ (prefixWord ++ tailWord_5277054).sum := by decide
  have hdescent : baseEnd_5277054 < baseStart_5277054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277090 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5277090 : Nat := 118140960795 + 5277090 * 2 ^ 59
def prefixEnd_5277090 : Nat := 4983230072969 + 3 ^ 40 * 5277090 * 2
def baseEnd_5277090 : Nat := 2709683627034863594806111

theorem tailTrace_5277090 : CollatzResearch.WordTrace tailWord_5277090 prefixEnd_5277090 2709683627034863594806111 := by
  unfold tailWord_5277090
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117821113002915016129181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128314189634674440043011149 48117821113002915016129181)
  ·
    refine ⟨18044182917376093131048443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48117821113002915016129181 18044182917376093131048443)
    ·
      refine ⟨27066274376064139696572665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044182917376093131048443 27066274376064139696572665)
      ·
        refine ⟨20299705782048104772429499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27066274376064139696572665 20299705782048104772429499)
        ·
          refine ⟨30449558673072157158644249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20299705782048104772429499 30449558673072157158644249)
          ·
            refine ⟨22837169004804117868983187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30449558673072157158644249 22837169004804117868983187)
            ·
              refine ⟨34255753507206176803474781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22837169004804117868983187 34255753507206176803474781)
              ·
                refine ⟨12845907565202316301303043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34255753507206176803474781 12845907565202316301303043)
                ·
                  refine ⟨19268861347803474451954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12845907565202316301303043 19268861347803474451954565)
                  ·
                    refine ⟨3612911502713151459741481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19268861347803474451954565 3612911502713151459741481)
                    ·
                      refine ⟨2709683627034863594806111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612911502713151459741481 2709683627034863594806111)
                      ·
                        rfl

theorem cell23_5277090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5277090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277090 prefixEnd_5277090 := by exact prefixLift 5277090
  have htrace : WordTrace (prefixWord ++ tailWord_5277090) baseStart_5277090 baseEnd_5277090 := by
    simpa [prefixWord, tailWord_5277090, baseEnd_5277090] using wordTrace_append hprefix tailTrace_5277090
  have hstable : (prefixWord ++ tailWord_5277090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277090).length < 2 ^ (prefixWord ++ tailWord_5277090).sum := by decide
  have hdescent : baseEnd_5277090 < baseStart_5277090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277124 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5277124 : Nat := 118140960795 + 5277124 * 2 ^ 59
def prefixEnd_5277124 : Nat := 4983230072969 + 3 ^ 40 * 5277124 * 2
def baseEnd_5277124 : Nat := 2709701085377116461780955

theorem tailTrace_5277124 : CollatzResearch.WordTrace tailWord_5277124 prefixEnd_5277124 2709701085377116461780955 := by
  unfold tailWord_5277124
  simp only [CollatzResearch.WordTrace]
  refine ⟨96236262266944241935627213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128315016355925655914169617 96236262266944241935627213)
  ·
    refine ⟨36088598350104090725860205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96236262266944241935627213 36088598350104090725860205)
    ·
      refine ⟨13533224381289034022197577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36088598350104090725860205 13533224381289034022197577)
      ·
        refine ⟨10149918285966775516648183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13533224381289034022197577 10149918285966775516648183)
        ·
          refine ⟨15224877428950163274972275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149918285966775516648183 15224877428950163274972275)
          ·
            refine ⟨22837316143425244912458413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15224877428950163274972275 22837316143425244912458413)
            ·
              refine ⟨8563993553784466842171905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22837316143425244912458413 8563993553784466842171905)
              ·
                refine ⟨6422995165338350131628929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563993553784466842171905 6422995165338350131628929)
                ·
                  refine ⟨4817246374003762598721697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422995165338350131628929 4817246374003762598721697)
                  ·
                    refine ⟨3612934780502821949041273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4817246374003762598721697 3612934780502821949041273)
                    ·
                      refine ⟨2709701085377116461780955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612934780502821949041273 2709701085377116461780955)
                      ·
                        rfl

theorem cell23_5277124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5277124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277124 prefixEnd_5277124 := by exact prefixLift 5277124
  have htrace : WordTrace (prefixWord ++ tailWord_5277124) baseStart_5277124 baseEnd_5277124 := by
    simpa [prefixWord, tailWord_5277124, baseEnd_5277124] using wordTrace_append hprefix tailTrace_5277124
  have hstable : (prefixWord ++ tailWord_5277124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277124).length < 2 ^ (prefixWord ++ tailWord_5277124).sum := by decide
  have hdescent : baseEnd_5277124 < baseStart_5277124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 4, 2]
def baseStart_5277163 : Nat := 118140960795 + 5277163 * 2 ^ 59
def prefixEnd_5277163 : Nat := 4983230072969 + 3 ^ 40 * 5277163 * 2
def baseEnd_5277163 : Nat := 2709721111122641809193275

theorem tailTrace_5277163 : CollatzResearch.WordTrace tailWord_5277163 prefixEnd_5277163 2709721111122641809193275 := by
  unfold tailWord_5277163
  simp only [CollatzResearch.WordTrace]
  refine ⟨192473946980747193531924143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128315964653831462354616095 192473946980747193531924143)
  ·
    refine ⟨288710920471120790297886215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192473946980747193531924143 288710920471120790297886215)
    ·
      refine ⟨433066380706681185446829323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288710920471120790297886215 433066380706681185446829323)
      ·
        refine ⟨649599571060021778170243985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433066380706681185446829323 649599571060021778170243985)
        ·
          refine ⟨487199678295016333627682989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649599571060021778170243985 487199678295016333627682989)
          ·
            refine ⟨182699879360631125110381121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487199678295016333627682989 182699879360631125110381121)
            ·
              refine ⟨137024909520473343832785841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182699879360631125110381121 137024909520473343832785841)
              ·
                refine ⟨102768682140355007874589381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137024909520473343832785841 102768682140355007874589381)
                ·
                  refine ⟨19269127901316563976485509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102768682140355007874589381 19269127901316563976485509)
                  ·
                    refine ⟨3612961481496855745591033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19269127901316563976485509 3612961481496855745591033)
                    ·
                      refine ⟨2709721111122641809193275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3612961481496855745591033 2709721111122641809193275)
                      ·
                        rfl

theorem cell23_5277163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4, 2].length) (baseStart_5277163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277163 prefixEnd_5277163 := by exact prefixLift 5277163
  have htrace : WordTrace (prefixWord ++ tailWord_5277163) baseStart_5277163 baseEnd_5277163 := by
    simpa [prefixWord, tailWord_5277163, baseEnd_5277163] using wordTrace_append hprefix tailTrace_5277163
  have hstable : (prefixWord ++ tailWord_5277163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277163).length < 2 ^ (prefixWord ++ tailWord_5277163).sum := by decide
  have hdescent : baseEnd_5277163 < baseStart_5277163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277203 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 6]
def baseStart_5277203 : Nat := 118140960795 + 5277203 * 2 ^ 59
def prefixEnd_5277203 : Nat := 4983230072969 + 3 ^ 40 * 5277203 * 2
def baseEnd_5277203 : Nat := 301082405594313516965899

theorem tailTrace_5277203 : CollatzResearch.WordTrace tailWord_5277203 prefixEnd_5277203 301082405594313516965899 := by
  unfold tailWord_5277203
  simp only [CollatzResearch.WordTrace]
  refine ⟨192475405900602280363380263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128316937267068186908920175 192475405900602280363380263)
  ·
    refine ⟨288713108850903420545070395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192475405900602280363380263 288713108850903420545070395)
    ·
      refine ⟨433069663276355130817605593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288713108850903420545070395 433069663276355130817605593)
      ·
        refine ⟨324802247457266348113204195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433069663276355130817605593 324802247457266348113204195)
        ·
          refine ⟨487203371185899522169806293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324802247457266348113204195 487203371185899522169806293)
          ·
            refine ⟨11418829012169520050854835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 487203371185899522169806293 11418829012169520050854835)
            ·
              refine ⟨17128243518254280076282253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11418829012169520050854835 17128243518254280076282253)
              ·
                refine ⟨6423091319345355028605845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17128243518254280076282253 6423091319345355028605845)
                ·
                  refine ⟨301082405594313516965899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6423091319345355028605845 301082405594313516965899)
                  ·
                    rfl

theorem cell23_5277203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 6].length) (baseStart_5277203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277203 prefixEnd_5277203 := by exact prefixLift 5277203
  have htrace : WordTrace (prefixWord ++ tailWord_5277203) baseStart_5277203 baseEnd_5277203 := by
    simpa [prefixWord, tailWord_5277203, baseEnd_5277203] using wordTrace_append hprefix tailTrace_5277203
  have hstable : (prefixWord ++ tailWord_5277203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277203).length < 2 ^ (prefixWord ++ tailWord_5277203).sum := by decide
  have hdescent : baseEnd_5277203 < baseStart_5277203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277253 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_5277253 : Nat := 118140960795 + 5277253 * 2 ^ 59
def prefixEnd_5277253 : Nat := 4983230072969 + 3 ^ 40 * 5277253 * 2
def baseEnd_5277253 : Nat := 2709767324381546457067861

theorem tailTrace_5277253 : CollatzResearch.WordTrace tailWord_5277253 prefixEnd_5277253 2709767324381546457067861 := by
  unfold tailWord_5277253
  simp only [CollatzResearch.WordTrace]
  refine ⟨192477229550421138902700413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128318153033614092601800275 192477229550421138902700413)
  ·
    refine ⟨72178961081407927088512655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192477229550421138902700413 72178961081407927088512655)
    ·
      refine ⟨108268441622111890632768983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72178961081407927088512655 108268441622111890632768983)
      ·
        refine ⟨162402662433167835949153475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108268441622111890632768983 162402662433167835949153475)
        ·
          refine ⟨243603993649751753923730213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162402662433167835949153475 243603993649751753923730213)
          ·
            refine ⟨45675748809328453860699415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243603993649751753923730213 45675748809328453860699415)
            ·
              refine ⟨68513623213992680791049123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45675748809328453860699415 68513623213992680791049123)
              ·
                refine ⟨102770434820989021186573685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68513623213992680791049123 102770434820989021186573685)
                ·
                  refine ⟨9634728264467720736241283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102770434820989021186573685 9634728264467720736241283)
                  ·
                    refine ⟨14452092396701581104361925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9634728264467720736241283 14452092396701581104361925)
                    ·
                      refine ⟨2709767324381546457067861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14452092396701581104361925 2709767324381546457067861)
                      ·
                        rfl

theorem cell23_5277253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_5277253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277253 prefixEnd_5277253 := by exact prefixLift 5277253
  have htrace : WordTrace (prefixWord ++ tailWord_5277253) baseStart_5277253 baseEnd_5277253 := by
    simpa [prefixWord, tailWord_5277253, baseEnd_5277253] using wordTrace_append hprefix tailTrace_5277253
  have hstable : (prefixWord ++ tailWord_5277253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277253).length < 2 ^ (prefixWord ++ tailWord_5277253).sum := by decide
  have hdescent : baseEnd_5277253 < baseStart_5277253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277263 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 6, 4]
def baseStart_5277263 : Nat := 118140960795 + 5277263 * 2 ^ 59
def prefixEnd_5277263 : Nat := 4983230072969 + 3 ^ 40 * 5277263 * 2
def baseEnd_5277263 : Nat := 903257486396030472647605

theorem tailTrace_5277263 : CollatzResearch.WordTrace tailWord_5277263 prefixEnd_5277263 903257486396030472647605 := by
  unfold tailWord_5277263
  simp only [CollatzResearch.WordTrace]
  refine ⟨192477594280384910610564443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128318396186923273740376295 192477594280384910610564443)
  ·
    refine ⟨288716391420577365915846665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192477594280384910610564443 288716391420577365915846665)
    ·
      refine ⟨216537293565433024436884999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288716391420577365915846665 216537293565433024436884999)
      ·
        refine ⟨324805940348149536655327499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216537293565433024436884999 324805940348149536655327499)
        ·
          refine ⟨487208910522224304982991249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324805940348149536655327499 487208910522224304982991249)
          ·
            refine ⟨365406682891668228737243437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487208910522224304982991249 365406682891668228737243437)
            ·
              refine ⟨137027506084375585776466289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365406682891668228737243437 137027506084375585776466289)
              ·
                refine ⟨102770629563281689332349717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137027506084375585776466289 102770629563281689332349717)
                ·
                  refine ⟨4817373260778829187453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102770629563281689332349717 4817373260778829187453893)
                  ·
                    refine ⟨903257486396030472647605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817373260778829187453893 903257486396030472647605)
                    ·
                      rfl

theorem cell23_5277263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_5277263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277263 prefixEnd_5277263 := by exact prefixLift 5277263
  have htrace : WordTrace (prefixWord ++ tailWord_5277263) baseStart_5277263 baseEnd_5277263 := by
    simpa [prefixWord, tailWord_5277263, baseEnd_5277263] using wordTrace_append hprefix tailTrace_5277263
  have hstable : (prefixWord ++ tailWord_5277263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277263).length < 2 ^ (prefixWord ++ tailWord_5277263).sum := by decide
  have hdescent : baseEnd_5277263 < baseStart_5277263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277287 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_5277287 : Nat := 118140960795 + 5277287 * 2 ^ 59
def prefixEnd_5277287 : Nat := 4983230072969 + 3 ^ 40 * 5277287 * 2
def baseEnd_5277287 : Nat := 2709784782723799324042705

theorem tailTrace_5277287 : CollatzResearch.WordTrace tailWord_5277287 prefixEnd_5277287 2709784782723799324042705 := by
  unfold tailWord_5277287
  simp only [CollatzResearch.WordTrace]
  refine ⟨192478469632297962709438115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128318979754865308472958743 192478469632297962709438115)
  ·
    refine ⟨288717704448446944064157173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192478469632297962709438115 288717704448446944064157173)
    ·
      refine ⟨27067284792041901006014735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288717704448446944064157173 27067284792041901006014735)
      ·
        refine ⟨40600927188062851509022103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27067284792041901006014735 40600927188062851509022103)
        ·
          refine ⟨60901390782094277263533155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40600927188062851509022103 60901390782094277263533155)
          ·
            refine ⟨91352086173141415895299733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60901390782094277263533155 91352086173141415895299733)
            ·
              refine ⟨4282129039366003870092175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91352086173141415895299733 4282129039366003870092175)
              ·
                refine ⟨6423193559049005805138263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282129039366003870092175 6423193559049005805138263)
                ·
                  refine ⟨9634790338573508707707395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423193559049005805138263 9634790338573508707707395)
                  ·
                    refine ⟨14452185507860263061561093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9634790338573508707707395 14452185507860263061561093)
                    ·
                      refine ⟨2709784782723799324042705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14452185507860263061561093 2709784782723799324042705)
                      ·
                        rfl

theorem cell23_5277287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_5277287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277287 prefixEnd_5277287 := by exact prefixLift 5277287
  have htrace : WordTrace (prefixWord ++ tailWord_5277287) baseStart_5277287 baseEnd_5277287 := by
    simpa [prefixWord, tailWord_5277287, baseEnd_5277287] using wordTrace_append hprefix tailTrace_5277287
  have hstable : (prefixWord ++ tailWord_5277287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277287).length < 2 ^ (prefixWord ++ tailWord_5277287).sum := by decide
  have hdescent : baseEnd_5277287 < baseStart_5277287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277347 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 1, 3, 2]
def baseStart_5277347 : Nat := 118140960795 + 5277347 * 2 ^ 59
def prefixEnd_5277347 : Nat := 4983230072969 + 3 ^ 40 * 5277347 * 2
def baseEnd_5277347 : Nat := 2709815591563069089292429

theorem tailTrace_5277347 : CollatzResearch.WordTrace tailWord_5277347 prefixEnd_5277347 2709815591563069089292429 := by
  unfold tailWord_5277347
  simp only [CollatzResearch.WordTrace]
  refine ⟨192480658012080592956622295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128320438674720395304414863 192480658012080592956622295)
  ·
    refine ⟨288720987018120889434933443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192480658012080592956622295 288720987018120889434933443)
    ·
      refine ⟨433081480527181334152400165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288720987018120889434933443 433081480527181334152400165)
      ·
        refine ⟨81202777598846500153575031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433081480527181334152400165 81202777598846500153575031)
        ·
          refine ⟨121804166398269750230362547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81202777598846500153575031 121804166398269750230362547)
          ·
            refine ⟨182706249597404625345543821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121804166398269750230362547 182706249597404625345543821)
            ·
              refine ⟨68514843599026734504578933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182706249597404625345543821 68514843599026734504578933)
              ·
                refine ⟨6423266587408756359804275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68514843599026734504578933 6423266587408756359804275)
                ·
                  refine ⟨9634899881113134539706413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423266587408756359804275 9634899881113134539706413)
                  ·
                    refine ⟨3613087455417425452389905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9634899881113134539706413 3613087455417425452389905)
                    ·
                      refine ⟨2709815591563069089292429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613087455417425452389905 2709815591563069089292429)
                      ·
                        rfl

theorem cell23_5277347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_5277347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277347 prefixEnd_5277347 := by exact prefixLift 5277347
  have htrace : WordTrace (prefixWord ++ tailWord_5277347) baseStart_5277347 baseEnd_5277347 := by
    simpa [prefixWord, tailWord_5277347, baseEnd_5277347] using wordTrace_append hprefix tailTrace_5277347
  have hstable : (prefixWord ++ tailWord_5277347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277347).length < 2 ^ (prefixWord ++ tailWord_5277347).sum := by decide
  have hdescent : baseEnd_5277347 < baseStart_5277347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277363 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_5277363 : Nat := 118140960795 + 5277363 * 2 ^ 59
def prefixEnd_5277363 : Nat := 4983230072969 + 3 ^ 40 * 5277363 * 2
def baseEnd_5277363 : Nat := 2709823807253541026692355

theorem tailTrace_5277363 : CollatzResearch.WordTrace tailWord_5277363 prefixEnd_5277363 2709823807253541026692355 := by
  unfold tailWord_5277363
  simp only [CollatzResearch.WordTrace]
  refine ⟨192481241580022627689204743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128320827720015085126136495 192481241580022627689204743)
  ·
    refine ⟨288721862370033941533807115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192481241580022627689204743 288721862370033941533807115)
    ·
      refine ⟨433082793555050912300710673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288721862370033941533807115 433082793555050912300710673)
      ·
        refine ⟨324812095166288184225533005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433082793555050912300710673 324812095166288184225533005)
        ·
          refine ⟨121804535687358069084574877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324812095166288184225533005 121804535687358069084574877)
          ·
            refine ⟨45676700882759275906715579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121804535687358069084574877 45676700882759275906715579)
            ·
              refine ⟨68515051324138913860073369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45676700882759275906715579 68515051324138913860073369)
              ·
                refine ⟨51386288493104185395055027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68515051324138913860073369 51386288493104185395055027)
                ·
                  refine ⟨77079432739656278092582541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51386288493104185395055027 77079432739656278092582541)
                  ·
                    refine ⟨28904787277371104284718453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77079432739656278092582541 28904787277371104284718453)
                    ·
                      refine ⟨2709823807253541026692355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28904787277371104284718453 2709823807253541026692355)
                      ·
                        rfl

theorem cell23_5277363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_5277363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277363 prefixEnd_5277363 := by exact prefixLift 5277363
  have htrace : WordTrace (prefixWord ++ tailWord_5277363) baseStart_5277363 baseEnd_5277363 := by
    simpa [prefixWord, tailWord_5277363, baseEnd_5277363] using wordTrace_append hprefix tailTrace_5277363
  have hstable : (prefixWord ++ tailWord_5277363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277363).length < 2 ^ (prefixWord ++ tailWord_5277363).sum := by decide
  have hdescent : baseEnd_5277363 < baseStart_5277363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277380 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5277380 : Nat := 118140960795 + 5277380 * 2 ^ 59
def prefixEnd_5277380 : Nat := 4983230072969 + 3 ^ 40 * 5277380 * 2
def baseEnd_5277380 : Nat := 2709832536424667460179777

theorem tailTrace_5277380 : CollatzResearch.WordTrace tailWord_5277380 prefixEnd_5277380 2709832536424667460179777 := by
  unfold tailWord_5277380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96240930810480519796286797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128321241080640693061715729 96240930810480519796286797)
  ·
    refine ⟨36090349053930194923607549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96240930810480519796286797 36090349053930194923607549)
    ·
      refine ⟨13533880895223823096352831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36090349053930194923607549 13533880895223823096352831)
      ·
        refine ⟨20300821342835734644529247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13533880895223823096352831 20300821342835734644529247)
        ·
          refine ⟨30451232014253601966793871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20300821342835734644529247 30451232014253601966793871)
          ·
            refine ⟨45676848021380402950190807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30451232014253601966793871 45676848021380402950190807)
            ·
              refine ⟨68515272032070604425286211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45676848021380402950190807 68515272032070604425286211)
              ·
                refine ⟨102772908048105906637929317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68515272032070604425286211 102772908048105906637929317)
                ·
                  refine ⟨19269920259019857494611747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102772908048105906637929317 19269920259019857494611747)
                  ·
                    refine ⟨28904880388529786241917621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19269920259019857494611747 28904880388529786241917621)
                    ·
                      refine ⟨2709832536424667460179777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28904880388529786241917621 2709832536424667460179777)
                      ·
                        rfl

theorem cell23_5277380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5277380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277380 prefixEnd_5277380 := by exact prefixLift 5277380
  have htrace : WordTrace (prefixWord ++ tailWord_5277380) baseStart_5277380 baseEnd_5277380 := by
    simpa [prefixWord, tailWord_5277380, baseEnd_5277380] using wordTrace_append hprefix tailTrace_5277380
  have hstable : (prefixWord ++ tailWord_5277380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277380).length < 2 ^ (prefixWord ++ tailWord_5277380).sum := by decide
  have hdescent : baseEnd_5277380 < baseStart_5277380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277383 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 9]
def baseStart_5277383 : Nat := 118140960795 + 5277383 * 2 ^ 59
def prefixEnd_5277383 : Nat := 4983230072969 + 3 ^ 40 * 5277383 * 2
def baseEnd_5277383 : Nat := 301092675207403438715807

theorem tailTrace_5277383 : CollatzResearch.WordTrace tailWord_5277383 prefixEnd_5277383 301092675207403438715807 := by
  unfold tailWord_5277383
  simp only [CollatzResearch.WordTrace]
  refine ⟨192481971039950171104932803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128321314026633447403288535 192481971039950171104932803)
  ·
    refine ⟨288722956559925256657399205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192481971039950171104932803 288722956559925256657399205)
    ·
      refine ⟨54135554354985985623262351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288722956559925256657399205 54135554354985985623262351)
      ·
        refine ⟨81203331532478978434893527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54135554354985985623262351 81203331532478978434893527)
        ·
          refine ⟨121804997298718467652340291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81203331532478978434893527 121804997298718467652340291)
          ·
            refine ⟨182707495948077701478510437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121804997298718467652340291 182707495948077701478510437)
            ·
              refine ⟨34257655490264569027220707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182707495948077701478510437 34257655490264569027220707)
              ·
                refine ⟨51386483235396853540831061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34257655490264569027220707 51386483235396853540831061)
                ·
                  refine ⟨301092675207403438715807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51386483235396853540831061 301092675207403438715807)
                  ·
                    rfl

theorem cell23_5277383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 9].length) (baseStart_5277383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277383 prefixEnd_5277383 := by exact prefixLift 5277383
  have htrace : WordTrace (prefixWord ++ tailWord_5277383) baseStart_5277383 baseEnd_5277383 := by
    simpa [prefixWord, tailWord_5277383, baseEnd_5277383] using wordTrace_append hprefix tailTrace_5277383
  have hstable : (prefixWord ++ tailWord_5277383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277383).length < 2 ^ (prefixWord ++ tailWord_5277383).sum := by decide
  have hdescent : baseEnd_5277383 < baseStart_5277383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277394 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5277394 : Nat := 118140960795 + 5277394 * 2 ^ 59
def prefixEnd_5277394 : Nat := 4983230072969 + 3 ^ 40 * 5277394 * 2
def baseEnd_5277394 : Nat := 2709839725153830405404713

theorem tailTrace_5277394 : CollatzResearch.WordTrace tailWord_5277394 prefixEnd_5277394 2709839725153830405404713 := by
  unfold tailWord_5277394
  simp only [CollatzResearch.WordTrace]
  refine ⟨48120593060727579995895809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128321581495273546655722157 48120593060727579995895809)
  ·
    refine ⟨36090444795545684996921857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48120593060727579995895809 36090444795545684996921857)
    ·
      refine ⟨27067833596659263747691393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36090444795545684996921857 27067833596659263747691393)
      ·
        refine ⟨20300875197494447810768545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27067833596659263747691393 20300875197494447810768545)
        ·
          refine ⟨15225656398120835858076409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20300875197494447810768545 15225656398120835858076409)
          ·
            refine ⟨11419242298590626893557307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15225656398120835858076409 11419242298590626893557307)
            ·
              refine ⟨17128863447885940340335961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419242298590626893557307 17128863447885940340335961)
              ·
                refine ⟨12846647585914455255251971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17128863447885940340335961 12846647585914455255251971)
                ·
                  refine ⟨19269971378871682882877957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12846647585914455255251971 19269971378871682882877957)
                  ·
                    refine ⟨3613119633538440540539617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19269971378871682882877957 3613119633538440540539617)
                    ·
                      refine ⟨2709839725153830405404713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613119633538440540539617 2709839725153830405404713)
                      ·
                        rfl

theorem cell23_5277394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5277394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277394 prefixEnd_5277394 := by exact prefixLift 5277394
  have htrace : WordTrace (prefixWord ++ tailWord_5277394) baseStart_5277394 baseEnd_5277394 := by
    simpa [prefixWord, tailWord_5277394, baseEnd_5277394] using wordTrace_append hprefix tailTrace_5277394
  have hstable : (prefixWord ++ tailWord_5277394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277394).length < 2 ^ (prefixWord ++ tailWord_5277394).sum := by decide
  have hdescent : baseEnd_5277394 < baseStart_5277394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277428 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5277428 : Nat := 118140960795 + 5277428 * 2 ^ 59
def prefixEnd_5277428 : Nat := 4983230072969 + 3 ^ 40 * 5277428 * 2
def baseEnd_5277428 : Nat := 2709857183496083272379557

theorem tailTrace_5277428 : CollatzResearch.WordTrace tailWord_5277428 prefixEnd_5277428 2709857183496083272379557 := by
  unfold tailWord_5277428
  simp only [CollatzResearch.WordTrace]
  refine ⟨96241806162393571895160469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128322408216524762526880625 96241806162393571895160469)
  ·
    refine ⟨4511334663862198682585647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96241806162393571895160469 4511334663862198682585647)
    ·
      refine ⟨6767001995793298023878471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511334663862198682585647 6767001995793298023878471)
      ·
        refine ⟨10150502993689947035817707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6767001995793298023878471 10150502993689947035817707)
        ·
          refine ⟨15225754490534920553726561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10150502993689947035817707 15225754490534920553726561)
          ·
            refine ⟨11419315867901190415294921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15225754490534920553726561 11419315867901190415294921)
            ·
              refine ⟨8564486900925892811471191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11419315867901190415294921 8564486900925892811471191)
              ·
                refine ⟨12846730351388839217206787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564486900925892811471191 12846730351388839217206787)
                ·
                  refine ⟨19270095527083258825810181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12846730351388839217206787 19270095527083258825810181)
                  ·
                    refine ⟨3613142911328111029839409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19270095527083258825810181 3613142911328111029839409)
                    ·
                      refine ⟨2709857183496083272379557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613142911328111029839409 2709857183496083272379557)
                      ·
                        rfl

theorem cell23_5277428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5277428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277428 prefixEnd_5277428 := by exact prefixLift 5277428
  have htrace : WordTrace (prefixWord ++ tailWord_5277428) baseStart_5277428 baseEnd_5277428 := by
    simpa [prefixWord, tailWord_5277428, baseEnd_5277428] using wordTrace_append hprefix tailTrace_5277428
  have hstable : (prefixWord ++ tailWord_5277428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277428).length < 2 ^ (prefixWord ++ tailWord_5277428).sum := by decide
  have hdescent : baseEnd_5277428 < baseStart_5277428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277447 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 7]
def baseStart_5277447 : Nat := 118140960795 + 5277447 * 2 ^ 59
def prefixEnd_5277447 : Nat := 4983230072969 + 3 ^ 40 * 5277447 * 2
def baseEnd_5277447 : Nat := 903288979876172899347323

theorem tailTrace_5277447 : CollatzResearch.WordTrace tailWord_5277447 prefixEnd_5277447 903288979876172899347323 := by
  unfold tailWord_5277447
  simp only [CollatzResearch.WordTrace]
  refine ⟨192484305311718310035262595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128322870207812206690175063 192484305311718310035262595)
  ·
    refine ⟨288726457967577465052893893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192484305311718310035262595 288726457967577465052893893)
    ·
      refine ⟨54136210868920774697417605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288726457967577465052893893 54136210868920774697417605)
      ·
        refine ⟨10150539537922645255765801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54136210868920774697417605 10150539537922645255765801)
        ·
          refine ⟨7612904653441983941824351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10150539537922645255765801 7612904653441983941824351)
          ·
            refine ⟨11419356980162975912736527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612904653441983941824351 11419356980162975912736527)
            ·
              refine ⟨17129035470244463869104791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419356980162975912736527 17129035470244463869104791)
              ·
                refine ⟨25693553205366695803657187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17129035470244463869104791 25693553205366695803657187)
                ·
                  refine ⟨38540329808050043705485781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25693553205366695803657187 38540329808050043705485781)
                  ·
                    refine ⟨903288979876172899347323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38540329808050043705485781 903288979876172899347323)
                    ·
                      rfl

theorem cell23_5277447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_5277447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277447 prefixEnd_5277447 := by exact prefixLift 5277447
  have htrace : WordTrace (prefixWord ++ tailWord_5277447) baseStart_5277447 baseEnd_5277447 := by
    simpa [prefixWord, tailWord_5277447, baseEnd_5277447] using wordTrace_append hprefix tailTrace_5277447
  have hstable : (prefixWord ++ tailWord_5277447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277447).length < 2 ^ (prefixWord ++ tailWord_5277447).sum := by decide
  have hdescent : baseEnd_5277447 < baseStart_5277447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277477 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_5277477 : Nat := 118140960795 + 5277477 * 2 ^ 59
def prefixEnd_5277477 : Nat := 4983230072969 + 3 ^ 40 * 5277477 * 2
def baseEnd_5277477 : Nat := 903294114682717860222277

theorem tailTrace_5277477 : CollatzResearch.WordTrace tailWord_5277477 prefixEnd_5277477 903294114682717860222277 := by
  unfold tailWord_5277477
  simp only [CollatzResearch.WordTrace]
  refine ⟨192485399501609625158854685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128323599667739750105903123 192485399501609625158854685)
  ·
    refine ⟨72182024813103609434570507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192485399501609625158854685 72182024813103609434570507)
    ·
      refine ⟨108273037219655414151855761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72182024813103609434570507 108273037219655414151855761)
      ·
        refine ⟨81204777914741560613891821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108273037219655414151855761 81204777914741560613891821)
        ·
          refine ⟨30451791718028085230209433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81204777914741560613891821 30451791718028085230209433)
          ·
            refine ⟨22838843788521063922657075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30451791718028085230209433 22838843788521063922657075)
            ·
              refine ⟨34258265682781595883985613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22838843788521063922657075 34258265682781595883985613)
              ·
                refine ⟨12846849631043098456494605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34258265682781595883985613 12846849631043098456494605)
                ·
                  refine ⟨4817568611641161921185477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12846849631043098456494605 4817568611641161921185477)
                  ·
                    refine ⟨903294114682717860222277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817568611641161921185477 903294114682717860222277)
                    ·
                      rfl

theorem cell23_5277477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_5277477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277477 prefixEnd_5277477 := by exact prefixLift 5277477
  have htrace : WordTrace (prefixWord ++ tailWord_5277477) baseStart_5277477 baseEnd_5277477 := by
    simpa [prefixWord, tailWord_5277477, baseEnd_5277477] using wordTrace_append hprefix tailTrace_5277477
  have hstable : (prefixWord ++ tailWord_5277477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277477).length < 2 ^ (prefixWord ++ tailWord_5277477).sum := by decide
  have hdescent : baseEnd_5277477 < baseStart_5277477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277520 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_5277520 : Nat := 118140960795 + 5277520 * 2 ^ 59
def prefixEnd_5277520 : Nat := 4983230072969 + 3 ^ 40 * 5277520 * 2
def baseEnd_5277520 : Nat := 903301474572098970809711

theorem tailTrace_5277520 : CollatzResearch.WordTrace tailWord_5277520 prefixEnd_5277520 903301474572098970809711 := by
  unfold tailWord_5277520
  simp only [CollatzResearch.WordTrace]
  refine ⟨96243483920226921751335007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128324645226969229001780009 96243483920226921751335007)
  ·
    refine ⟨144365225880340382627002511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96243483920226921751335007 144365225880340382627002511)
    ·
      refine ⟨216547838820510573940503767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144365225880340382627002511 216547838820510573940503767)
      ·
        refine ⟨324821758230765860910755651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216547838820510573940503767 324821758230765860910755651)
        ·
          refine ⟨487232637346148791366133477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324821758230765860910755651 487232637346148791366133477)
          ·
            refine ⟨91356119502402898381150027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487232637346148791366133477 91356119502402898381150027)
            ·
              refine ⟨137034179253604347571725041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91356119502402898381150027 137034179253604347571725041)
              ·
                refine ⟨102775634440203260678793781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137034179253604347571725041 102775634440203260678793781)
                ·
                  refine ⟨9635215728769055688636917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102775634440203260678793781 9635215728769055688636917)
                  ·
                    refine ⟨903301474572098970809711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9635215728769055688636917 903301474572098970809711)
                    ·
                      rfl

theorem cell23_5277520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_5277520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277520 prefixEnd_5277520 := by exact prefixLift 5277520
  have htrace : WordTrace (prefixWord ++ tailWord_5277520) baseStart_5277520 baseEnd_5277520 := by
    simpa [prefixWord, tailWord_5277520, baseEnd_5277520] using wordTrace_append hprefix tailTrace_5277520
  have hstable : (prefixWord ++ tailWord_5277520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277520).length < 2 ^ (prefixWord ++ tailWord_5277520).sum := by decide
  have hdescent : baseEnd_5277520 < baseStart_5277520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277544 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5277544 : Nat := 118140960795 + 5277544 * 2 ^ 59
def prefixEnd_5277544 : Nat := 4983230072969 + 3 ^ 40 * 5277544 * 2
def baseEnd_5277544 : Nat := 2709916747252004818529023

theorem tailTrace_5277544 : CollatzResearch.WordTrace tailWord_5277544 prefixEnd_5277544 2709916747252004818529023 := by
  unfold tailWord_5277544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96243921596183447800771843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128325228794911263734362457 96243921596183447800771843)
  ·
    refine ⟨144365882394275171701157765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96243921596183447800771843 144365882394275171701157765)
    ·
      refine ⟨27068602948926594693967081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144365882394275171701157765 27068602948926594693967081)
      ·
        refine ⟨20301452211694946020475311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27068602948926594693967081 20301452211694946020475311)
        ·
          refine ⟨30452178317542419030712967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20301452211694946020475311 30452178317542419030712967)
          ·
            refine ⟨45678267476313628546069451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30452178317542419030712967 45678267476313628546069451)
            ·
              refine ⟨68517401214470442819104177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45678267476313628546069451 68517401214470442819104177)
              ·
                refine ⟨51388050910852832114328133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68517401214470442819104177 51388050910852832114328133)
                ·
                  refine ⟨9635259545784906021436525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51388050910852832114328133 9635259545784906021436525)
                  ·
                    refine ⟨3613222329669339758038697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9635259545784906021436525 3613222329669339758038697)
                    ·
                      refine ⟨2709916747252004818529023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613222329669339758038697 2709916747252004818529023)
                      ·
                        rfl

theorem cell23_5277544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5277544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277544 prefixEnd_5277544 := by exact prefixLift 5277544
  have htrace : WordTrace (prefixWord ++ tailWord_5277544) baseStart_5277544 baseEnd_5277544 := by
    simpa [prefixWord, tailWord_5277544, baseEnd_5277544] using wordTrace_append hprefix tailTrace_5277544
  have hstable : (prefixWord ++ tailWord_5277544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277544).length < 2 ^ (prefixWord ++ tailWord_5277544).sum := by decide
  have hdescent : baseEnd_5277544 < baseStart_5277544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277594 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5277594 : Nat := 118140960795 + 5277594 * 2 ^ 59
def prefixEnd_5277594 : Nat := 4983230072969 + 3 ^ 40 * 5277594 * 2
def baseEnd_5277594 : Nat := 2709942421284729622903793

theorem tailTrace_5277594 : CollatzResearch.WordTrace tailWord_5277594 prefixEnd_5277594 2709942421284729622903793 := by
  unfold tailWord_5277594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48122416710546438535215959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128326444561457169427242557 48122416710546438535215959)
  ·
    refine ⟨72183625065819657802823939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48122416710546438535215959 72183625065819657802823939)
    ·
      refine ⟨108275437598729486704235909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72183625065819657802823939 108275437598729486704235909)
      ·
        refine ⟨20301644549761778757044233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108275437598729486704235909 20301644549761778757044233)
        ·
          refine ⟨15226233412321334067783175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20301644549761778757044233 15226233412321334067783175)
          ·
            refine ⟨22839350118482001101674763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226233412321334067783175 22839350118482001101674763)
            ·
              refine ⟨34259025177723001652512145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22839350118482001101674763 34259025177723001652512145)
              ·
                refine ⟨25694268883292251239384109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34259025177723001652512145 25694268883292251239384109)
                ·
                  refine ⟨9635350831234594214769041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25694268883292251239384109 9635350831234594214769041)
                  ·
                    refine ⟨7226513123425945661076781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9635350831234594214769041 7226513123425945661076781)
                    ·
                      refine ⟨2709942421284729622903793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7226513123425945661076781 2709942421284729622903793)
                      ·
                        rfl

theorem cell23_5277594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5277594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277594 prefixEnd_5277594 := by exact prefixLift 5277594
  have htrace : WordTrace (prefixWord ++ tailWord_5277594) baseStart_5277594 baseEnd_5277594 := by
    simpa [prefixWord, tailWord_5277594, baseEnd_5277594] using wordTrace_append hprefix tailTrace_5277594
  have hstable : (prefixWord ++ tailWord_5277594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277594).length < 2 ^ (prefixWord ++ tailWord_5277594).sum := by decide
  have hdescent : baseEnd_5277594 < baseStart_5277594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277597 : List Nat := [1, 4, 2, 1, 2, 2, 3, 8]
def baseStart_5277597 : Nat := 118140960795 + 5277597 * 2 ^ 59
def prefixEnd_5277597 : Nat := 4983230072969 + 3 ^ 40 * 5277597 * 2
def baseEnd_5277597 : Nat := 100368294878766411524677

theorem tailTrace_5277597 : CollatzResearch.WordTrace tailWord_5277597 prefixEnd_5277597 100368294878766411524677 := by
  unfold tailWord_5277597
  simp only [CollatzResearch.WordTrace]
  refine ⟨192489776261174885653223045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128326517507449923768815363 192489776261174885653223045)
  ·
    refine ⟨36091833048970291059979321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192489776261174885653223045 36091833048970291059979321)
    ·
      refine ⟨27068874786727718294984491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36091833048970291059979321 27068874786727718294984491)
      ·
        refine ⟨40603312180091577442476737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27068874786727718294984491 40603312180091577442476737)
        ·
          refine ⟨30452484135068683081857553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40603312180091577442476737 30452484135068683081857553)
          ·
            refine ⟨22839363101301512311393165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30452484135068683081857553 22839363101301512311393165)
            ·
              refine ⟨8564761162988067116772437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22839363101301512311393165 8564761162988067116772437)
              ·
                refine ⟨100368294878766411524677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8564761162988067116772437 100368294878766411524677)
                ·
                  rfl

theorem cell23_5277597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 8].length) (baseStart_5277597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277597 prefixEnd_5277597 := by exact prefixLift 5277597
  have htrace : WordTrace (prefixWord ++ tailWord_5277597) baseStart_5277597 baseEnd_5277597 := by
    simpa [prefixWord, tailWord_5277597, baseEnd_5277597] using wordTrace_append hprefix tailTrace_5277597
  have hstable : (prefixWord ++ tailWord_5277597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277597).length < 2 ^ (prefixWord ++ tailWord_5277597).sum := by decide
  have hdescent : baseEnd_5277597 < baseStart_5277597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277604 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_5277604 : Nat := 118140960795 + 5277604 * 2 ^ 59
def prefixEnd_5277604 : Nat := 4983230072969 + 3 ^ 40 * 5277604 * 2
def baseEnd_5277604 : Nat := 2709947556091274583778747

theorem tailTrace_5277604 : CollatzResearch.WordTrace tailWord_5277604 prefixEnd_5277604 2709947556091274583778747 := by
  unfold tailWord_5277604
  simp only [CollatzResearch.WordTrace]
  refine ⟨96245015786074762924363933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128326687714766350565818577 96245015786074762924363933)
  ·
    refine ⟨36091880919778036096636475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96245015786074762924363933 36091880919778036096636475)
    ·
      refine ⟨54137821379667054144954713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36091880919778036096636475 54137821379667054144954713)
      ·
        refine ⟨40603366034750290608716035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54137821379667054144954713 40603366034750290608716035)
        ·
          refine ⟨60905049052125435913074053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40603366034750290608716035 60905049052125435913074053)
          ·
            refine ⟨11419696697273519233701385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60905049052125435913074053 11419696697273519233701385)
            ·
              refine ⟨8564772522955139425276039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11419696697273519233701385 8564772522955139425276039)
              ·
                refine ⟨12847158784432709137914059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564772522955139425276039 12847158784432709137914059)
                ·
                  refine ⟨19270738176649063706871089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12847158784432709137914059 19270738176649063706871089)
                  ·
                    refine ⟨14453053632486797780153317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19270738176649063706871089 14453053632486797780153317)
                    ·
                      refine ⟨2709947556091274583778747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14453053632486797780153317 2709947556091274583778747)
                      ·
                        rfl

theorem cell23_5277604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_5277604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277604 prefixEnd_5277604 := by exact prefixLift 5277604
  have htrace : WordTrace (prefixWord ++ tailWord_5277604) baseStart_5277604 baseEnd_5277604 := by
    simpa [prefixWord, tailWord_5277604, baseEnd_5277604] using wordTrace_append hprefix tailTrace_5277604
  have hstable : (prefixWord ++ tailWord_5277604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277604).length < 2 ^ (prefixWord ++ tailWord_5277604).sum := by decide
  have hdescent : baseEnd_5277604 < baseStart_5277604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277624 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_5277624 : Nat := 118140960795 + 5277624 * 2 ^ 59
def prefixEnd_5277624 : Nat := 4983230072969 + 3 ^ 40 * 5277624 * 2
def baseEnd_5277624 : Nat := 2709957825704364505528655

theorem tailTrace_5277624 : CollatzResearch.WordTrace tailWord_5277624 prefixEnd_5277624 2709957825704364505528655 := by
  unfold tailWord_5277624
  simp only [CollatzResearch.WordTrace]
  refine ⟨96245380516038534632227963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128327174021384712842970617 96245380516038534632227963)
  ·
    refine ⟨144368070774057801948341945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96245380516038534632227963 144368070774057801948341945)
    ·
      refine ⟨108276053080543351461256459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144368070774057801948341945 108276053080543351461256459)
      ·
        refine ⟨162414079620815027191884689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108276053080543351461256459 162414079620815027191884689)
        ·
          refine ⟨121810559715611270393913517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162414079620815027191884689 121810559715611270393913517)
          ·
            refine ⟨45678959893354226397717569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121810559715611270393913517 45678959893354226397717569)
            ·
              refine ⟨34259219920015669798288177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45678959893354226397717569 34259219920015669798288177)
              ·
                refine ⟨25694414940011752348716133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34259219920015669798288177 25694414940011752348716133)
                ·
                  refine ⟨4817702801252203565384275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25694414940011752348716133 4817702801252203565384275)
                  ·
                    refine ⟨7226554201878305348076413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817702801252203565384275 7226554201878305348076413)
                    ·
                      refine ⟨2709957825704364505528655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7226554201878305348076413 2709957825704364505528655)
                      ·
                        rfl

theorem cell23_5277624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_5277624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277624 prefixEnd_5277624 := by exact prefixLift 5277624
  have htrace : WordTrace (prefixWord ++ tailWord_5277624) baseStart_5277624 baseEnd_5277624 := by
    simpa [prefixWord, tailWord_5277624, baseEnd_5277624] using wordTrace_append hprefix tailTrace_5277624
  have hstable : (prefixWord ++ tailWord_5277624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277624).length < 2 ^ (prefixWord ++ tailWord_5277624).sum := by decide
  have hdescent : baseEnd_5277624 < baseStart_5277624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277628 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5277628 : Nat := 118140960795 + 5277628 * 2 ^ 59
def prefixEnd_5277628 : Nat := 4983230072969 + 3 ^ 40 * 5277628 * 2
def baseEnd_5277628 : Nat := 2709959879626982489878637

theorem tailTrace_5277628 : CollatzResearch.WordTrace tailWord_5277628 prefixEnd_5277628 2709959879626982489878637 := by
  unfold tailWord_5277628
  simp only [CollatzResearch.WordTrace]
  refine ⟨96245453462031288973800769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128327271282708385298401025 96245453462031288973800769)
  ·
    refine ⟨72184090096523466730350577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96245453462031288973800769 72184090096523466730350577)
    ·
      refine ⟨54138067572392600047762933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72184090096523466730350577 54138067572392600047762933)
      ·
        refine ⟨5075443834911806254477775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54138067572392600047762933 5075443834911806254477775)
        ·
          refine ⟨7613165752367709381716663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075443834911806254477775 7613165752367709381716663)
          ·
            refine ⟨11419748628551564072574995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613165752367709381716663 11419748628551564072574995)
            ·
              refine ⟨17129622942827346108862493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419748628551564072574995 17129622942827346108862493)
              ·
                refine ⟨6423608603560254790823435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17129622942827346108862493 6423608603560254790823435)
                ·
                  refine ⟨9635412905340382186235153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423608603560254790823435 9635412905340382186235153)
                  ·
                    refine ⟨7226559679005286639676365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9635412905340382186235153 7226559679005286639676365)
                    ·
                      refine ⟨2709959879626982489878637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7226559679005286639676365 2709959879626982489878637)
                      ·
                        rfl

theorem cell23_5277628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5277628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277628 prefixEnd_5277628 := by exact prefixLift 5277628
  have htrace : WordTrace (prefixWord ++ tailWord_5277628) baseStart_5277628 baseEnd_5277628 := by
    simpa [prefixWord, tailWord_5277628, baseEnd_5277628] using wordTrace_append hprefix tailTrace_5277628
  have hstable : (prefixWord ++ tailWord_5277628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277628).length < 2 ^ (prefixWord ++ tailWord_5277628).sum := by decide
  have hdescent : baseEnd_5277628 < baseStart_5277628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277658 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_5277658 : Nat := 118140960795 + 5277658 * 2 ^ 59
def prefixEnd_5277658 : Nat := 4983230072969 + 3 ^ 40 * 5277658 * 2
def baseEnd_5277658 : Nat := 2709975284046617372503499

theorem tailTrace_5277658 : CollatzResearch.WordTrace tailWord_5277658 prefixEnd_5277658 2709975284046617372503499 := by
  unfold tailWord_5277658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48123000278488473267798407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128328000742635928714129085 48123000278488473267798407)
  ·
    refine ⟨72184500417732709901697611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48123000278488473267798407 72184500417732709901697611)
    ·
      refine ⟨108276750626599064852546417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72184500417732709901697611 108276750626599064852546417)
      ·
        refine ⟨81207562969949298639409813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108276750626599064852546417 81207562969949298639409813)
        ·
          refine ⟨3806604514216373373722335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81207562969949298639409813 3806604514216373373722335)
          ·
            refine ⟨5709906771324560060583503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806604514216373373722335 5709906771324560060583503)
            ·
              refine ⟨8564860156986840090875255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709906771324560060583503 8564860156986840090875255)
              ·
                refine ⟨12847290235480260136312883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564860156986840090875255 12847290235480260136312883)
                ·
                  refine ⟨19270935353220390204469325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12847290235480260136312883 19270935353220390204469325)
                  ·
                    refine ⟨7226600757457646326675997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19270935353220390204469325 7226600757457646326675997)
                    ·
                      refine ⟨2709975284046617372503499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7226600757457646326675997 2709975284046617372503499)
                      ·
                        rfl

theorem cell23_5277658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_5277658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277658 prefixEnd_5277658 := by exact prefixLift 5277658
  have htrace : WordTrace (prefixWord ++ tailWord_5277658) baseStart_5277658 baseEnd_5277658 := by
    simpa [prefixWord, tailWord_5277658, baseEnd_5277658] using wordTrace_append hprefix tailTrace_5277658
  have hstable : (prefixWord ++ tailWord_5277658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277658).length < 2 ^ (prefixWord ++ tailWord_5277658).sum := by decide
  have hdescent : baseEnd_5277658 < baseStart_5277658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277697 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5277697 : Nat := 118140960795 + 5277697 * 2 ^ 59
def prefixEnd_5277697 : Nat := 4983230072969 + 3 ^ 40 * 5277697 * 2
def baseEnd_5277697 : Nat := 2709995309792142719915819

theorem tailTrace_5277697 : CollatzResearch.WordTrace tailWord_5277697 prefixEnd_5277697 2709995309792142719915819 := by
  unfold tailWord_5277697
  simp only [CollatzResearch.WordTrace]
  refine ⟨192493423560812602731863345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128328949040541735154575563 192493423560812602731863345)
  ·
    refine ⟨144370067670609452048897509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192493423560812602731863345 144370067670609452048897509)
    ·
      refine ⟨27069387688239272259168283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144370067670609452048897509 27069387688239272259168283)
      ·
        refine ⟨40604081532358908388752425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27069387688239272259168283 40604081532358908388752425)
        ·
          refine ⟨30453061149269181291564319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40604081532358908388752425 30453061149269181291564319)
          ·
            refine ⟨45679591723903771937346479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30453061149269181291564319 45679591723903771937346479)
            ·
              refine ⟨68519387585855657906019719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45679591723903771937346479 68519387585855657906019719)
              ·
                refine ⟨102779081378783486859029579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68519387585855657906019719 102779081378783486859029579)
                ·
                  refine ⟨154168622068175230288544369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102779081378783486859029579 154168622068175230288544369)
                  ·
                    refine ⟨115626466551131422716408277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154168622068175230288544369 115626466551131422716408277)
                    ·
                      refine ⟨2709995309792142719915819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115626466551131422716408277 2709995309792142719915819)
                      ·
                        rfl

theorem cell23_5277697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5277697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277697 prefixEnd_5277697 := by exact prefixLift 5277697
  have htrace : WordTrace (prefixWord ++ tailWord_5277697) baseStart_5277697 baseEnd_5277697 := by
    simpa [prefixWord, tailWord_5277697, baseEnd_5277697] using wordTrace_append hprefix tailTrace_5277697
  have hstable : (prefixWord ++ tailWord_5277697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277697).length < 2 ^ (prefixWord ++ tailWord_5277697).sum := by decide
  have hdescent : baseEnd_5277697 < baseStart_5277697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277727 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5277727 : Nat := 118140960795 + 5277727 * 2 ^ 59
def prefixEnd_5277727 : Nat := 4983230072969 + 3 ^ 40 * 5277727 * 2
def baseEnd_5277727 : Nat := 2710010714211777602540681

theorem tailTrace_5277727 : CollatzResearch.WordTrace tailWord_5277727 prefixEnd_5277727 2710010714211777602540681 := by
  unfold tailWord_5277727
  simp only [CollatzResearch.WordTrace]
  refine ⟨192494517750703917855455435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128329678500469278570303623 192494517750703917855455435)
  ·
    refine ⟨288741776626055876783183153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192494517750703917855455435 288741776626055876783183153)
    ·
      refine ⟨216556332469541907587387365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288741776626055876783183153 216556332469541907587387365)
      ·
        refine ⟨40604312338039107672635131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216556332469541907587387365 40604312338039107672635131)
        ·
          refine ⟨60906468507058661508952697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40604312338039107672635131 60906468507058661508952697)
          ·
            refine ⟨45679851380293996131714523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60906468507058661508952697 45679851380293996131714523)
            ·
              refine ⟨68519777070440994197571785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45679851380293996131714523 68519777070440994197571785)
              ·
                refine ⟨51389832802830745648178839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68519777070440994197571785 51389832802830745648178839)
                ·
                  refine ⟨77084749204246118472268259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51389832802830745648178839 77084749204246118472268259)
                  ·
                    refine ⟨115627123806369177708402389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77084749204246118472268259 115627123806369177708402389)
                    ·
                      refine ⟨2710010714211777602540681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115627123806369177708402389 2710010714211777602540681)
                      ·
                        rfl

theorem cell23_5277727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5277727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277727 prefixEnd_5277727 := by exact prefixLift 5277727
  have htrace : WordTrace (prefixWord ++ tailWord_5277727) baseStart_5277727 baseEnd_5277727 := by
    simpa [prefixWord, tailWord_5277727, baseEnd_5277727] using wordTrace_append hprefix tailTrace_5277727
  have hstable : (prefixWord ++ tailWord_5277727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277727).length < 2 ^ (prefixWord ++ tailWord_5277727).sum := by decide
  have hdescent : baseEnd_5277727 < baseStart_5277727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277737 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_5277737 : Nat := 118140960795 + 5277737 * 2 ^ 59
def prefixEnd_5277737 : Nat := 4983230072969 + 3 ^ 40 * 5277737 * 2
def baseEnd_5277737 : Nat := 2710015849018322563415635

theorem tailTrace_5277737 : CollatzResearch.WordTrace tailWord_5277737 prefixEnd_5277737 2710015849018322563415635 := by
  unfold tailWord_5277737
  simp only [CollatzResearch.WordTrace]
  refine ⟨192494882480667689563319465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128329921653778459708879643 192494882480667689563319465)
  ·
    refine ⟨144371161860500767172489599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192494882480667689563319465 144371161860500767172489599)
    ·
      refine ⟨216556742790751150758734399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144371161860500767172489599 216556742790751150758734399)
      ·
        refine ⟨324835114186126726138101599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216556742790751150758734399 324835114186126726138101599)
        ·
          refine ⟨487252671279190089207152399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324835114186126726138101599 487252671279190089207152399)
          ·
            refine ⟨730879006918785133810728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487252671279190089207152399 730879006918785133810728599)
            ·
              refine ⟨1096318510378177700716092899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730879006918785133810728599 1096318510378177700716092899)
              ·
                refine ⟨1644477765567266551074139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096318510378177700716092899 1644477765567266551074139349)
                ·
                  refine ⟨38542447630482809790800141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1644477765567266551074139349 38542447630482809790800141)
                  ·
                    refine ⟨14453417861431053671550053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38542447630482809790800141 14453417861431053671550053)
                    ·
                      refine ⟨2710015849018322563415635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14453417861431053671550053 2710015849018322563415635)
                      ·
                        rfl

theorem cell23_5277737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_5277737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277737 prefixEnd_5277737 := by exact prefixLift 5277737
  have htrace : WordTrace (prefixWord ++ tailWord_5277737) baseStart_5277737 baseEnd_5277737 := by
    simpa [prefixWord, tailWord_5277737, baseEnd_5277737] using wordTrace_append hprefix tailTrace_5277737
  have hstable : (prefixWord ++ tailWord_5277737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277737).length < 2 ^ (prefixWord ++ tailWord_5277737).sum := by decide
  have hdescent : baseEnd_5277737 < baseStart_5277737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277777 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 10]
def baseStart_5277777 : Nat := 118140960795 + 5277777 * 2 ^ 59
def prefixEnd_5277777 : Nat := 4983230072969 + 3 ^ 40 * 5277777 * 2
def baseEnd_5277777 : Nat := 301115154249389156323939

theorem tailTrace_5277777 : CollatzResearch.WordTrace tailWord_5277777 prefixEnd_5277777 301115154249389156323939 := by
  unfold tailWord_5277777
  simp only [CollatzResearch.WordTrace]
  refine ⟨192496341400522776394775585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128330894267015184263183723 192496341400522776394775585)
  ·
    refine ⟨144372256050392082296081689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192496341400522776394775585 144372256050392082296081689)
    ·
      refine ⟨108279192037794061722061267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144372256050392082296081689 108279192037794061722061267)
      ·
        refine ⟨162418788056691092583091901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108279192037794061722061267 162418788056691092583091901)
        ·
          refine ⟨60907045521259159718659463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162418788056691092583091901 60907045521259159718659463)
          ·
            refine ⟨91360568281888739577989195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60907045521259159718659463 91360568281888739577989195)
            ·
              refine ⟨137040852422833109366983793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91360568281888739577989195 137040852422833109366983793)
              ·
                refine ⟨102780639317124832025237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137040852422833109366983793 102780639317124832025237845)
                ·
                  refine ⟨301115154249389156323939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102780639317124832025237845 301115154249389156323939)
                  ·
                    rfl

theorem cell23_5277777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_5277777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277777 prefixEnd_5277777 := by exact prefixLift 5277777
  have htrace : WordTrace (prefixWord ++ tailWord_5277777) baseStart_5277777 baseEnd_5277777 := by
    simpa [prefixWord, tailWord_5277777, baseEnd_5277777] using wordTrace_append hprefix tailTrace_5277777
  have hstable : (prefixWord ++ tailWord_5277777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277777).length < 2 ^ (prefixWord ++ tailWord_5277777).sum := by decide
  have hdescent : baseEnd_5277777 < baseStart_5277777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277781 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_5277781 : Nat := 118140960795 + 5277781 * 2 ^ 59
def prefixEnd_5277781 : Nat := 4983230072969 + 3 ^ 40 * 5277781 * 2
def baseEnd_5277781 : Nat := 903346147389040130421811

theorem tailTrace_5277781 : CollatzResearch.WordTrace tailWord_5277781 prefixEnd_5277781 903346147389040130421811 := by
  unfold tailWord_5277781
  simp only [CollatzResearch.WordTrace]
  refine ⟨192496487292508285077921197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128330991528338856718614131 192496487292508285077921197)
  ·
    refine ⟨72186182734690606904220449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192496487292508285077921197 72186182734690606904220449)
    ·
      refine ⟨54139637051017955178165337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72186182734690606904220449 54139637051017955178165337)
      ·
        refine ⟨40604727788263466383624003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54139637051017955178165337 40604727788263466383624003)
        ·
          refine ⟨60907091682395199575436005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40604727788263466383624003 60907091682395199575436005)
          ·
            refine ⟨11420079690449099920394251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60907091682395199575436005 11420079690449099920394251)
            ·
              refine ⟨17130119535673649880591377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420079690449099920394251 17130119535673649880591377)
              ·
                refine ⟨12847589651755237410443533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17130119535673649880591377 12847589651755237410443533)
                ·
                  refine ⟨4817846119408214028916325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12847589651755237410443533 4817846119408214028916325)
                  ·
                    refine ⟨903346147389040130421811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817846119408214028916325 903346147389040130421811)
                    ·
                      rfl

theorem cell23_5277781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_5277781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277781 prefixEnd_5277781 := by exact prefixLift 5277781
  have htrace : WordTrace (prefixWord ++ tailWord_5277781) baseStart_5277781 baseEnd_5277781 := by
    simpa [prefixWord, tailWord_5277781, baseEnd_5277781] using wordTrace_append hprefix tailTrace_5277781
  have hstable : (prefixWord ++ tailWord_5277781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277781).length < 2 ^ (prefixWord ++ tailWord_5277781).sum := by decide
  have hdescent : baseEnd_5277781 < baseStart_5277781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277788 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5277788 : Nat := 118140960795 + 5277788 * 2 ^ 59
def prefixEnd_5277788 : Nat := 4983230072969 + 3 ^ 40 * 5277788 * 2
def baseEnd_5277788 : Nat := 2710042036531701863877901

theorem tailTrace_5277788 : CollatzResearch.WordTrace tailWord_5277788 prefixEnd_5277788 2710042036531701863877901 := by
  unfold tailWord_5277788
  simp only [CollatzResearch.WordTrace]
  refine ⟨96248371301741462636713009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128331161735655283515617345 96248371301741462636713009)
  ·
    refine ⟨72186278476306096977534757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96248371301741462636713009 72186278476306096977534757)
    ·
      refine ⟨13534927214307393183287767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72186278476306096977534757 13534927214307393183287767)
      ·
        refine ⟨20302390821461089774931651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534927214307393183287767 20302390821461089774931651)
        ·
          refine ⟨30453586232191634662397477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20302390821461089774931651 30453586232191634662397477)
          ·
            refine ⟨5710047418535931499199527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30453586232191634662397477 5710047418535931499199527)
            ·
              refine ⟨8565071127803897248799291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710047418535931499199527 8565071127803897248799291)
              ·
                refine ⟨12847606691705845873198937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565071127803897248799291 12847606691705845873198937)
                ·
                  refine ⟨9635705018779384404899203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12847606691705845873198937 9635705018779384404899203)
                  ·
                    refine ⟨14453557528169076607348805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9635705018779384404899203 14453557528169076607348805)
                    ·
                      refine ⟨2710042036531701863877901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14453557528169076607348805 2710042036531701863877901)
                      ·
                        rfl

theorem cell23_5277788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5277788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277788 prefixEnd_5277788 := by exact prefixLift 5277788
  have htrace : WordTrace (prefixWord ++ tailWord_5277788) baseStart_5277788 baseEnd_5277788 := by
    simpa [prefixWord, tailWord_5277788, baseEnd_5277788] using wordTrace_append hprefix tailTrace_5277788
  have hstable : (prefixWord ++ tailWord_5277788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277788).length < 2 ^ (prefixWord ++ tailWord_5277788).sum := by decide
  have hdescent : baseEnd_5277788 < baseStart_5277788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277831 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_5277831 : Nat := 118140960795 + 5277831 * 2 ^ 59
def prefixEnd_5277831 : Nat := 4983230072969 + 3 ^ 40 * 5277831 * 2
def baseEnd_5277831 : Nat := 2710064116199845195640203

theorem tailTrace_5277831 : CollatzResearch.WordTrace tailWord_5277831 prefixEnd_5277831 2710064116199845195640203 := by
  unfold tailWord_5277831
  simp only [CollatzResearch.WordTrace]
  refine ⟨192498310942327143617241347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128332207294884762411494231 192498310942327143617241347)
  ·
    refine ⟨288747466413490715425862021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192498310942327143617241347 288747466413490715425862021)
    ·
      refine ⟨54140149952529509142349129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288747466413490715425862021 54140149952529509142349129)
      ·
        refine ⟨40605112464397131856761847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54140149952529509142349129 40605112464397131856761847)
        ·
          refine ⟨60907668696595697785142771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40605112464397131856761847 60907668696595697785142771)
          ·
            refine ⟨91361503044893546677714157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60907668696595697785142771 91361503044893546677714157)
            ·
              refine ⟨34260563641835080004142809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91361503044893546677714157 34260563641835080004142809)
              ·
                refine ⟨25695422731376310003107107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34260563641835080004142809 25695422731376310003107107)
                ·
                  refine ⟨38543134097064465004660661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25695422731376310003107107 38543134097064465004660661)
                  ·
                    refine ⟨3613418821599793594186937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38543134097064465004660661 3613418821599793594186937)
                    ·
                      refine ⟨2710064116199845195640203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613418821599793594186937 2710064116199845195640203)
                      ·
                        rfl

theorem cell23_5277831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_5277831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277831 prefixEnd_5277831 := by exact prefixLift 5277831
  have htrace : WordTrace (prefixWord ++ tailWord_5277831) baseStart_5277831 baseEnd_5277831 := by
    simpa [prefixWord, tailWord_5277831, baseEnd_5277831] using wordTrace_append hprefix tailTrace_5277831
  have hstable : (prefixWord ++ tailWord_5277831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277831).length < 2 ^ (prefixWord ++ tailWord_5277831).sum := by decide
  have hdescent : baseEnd_5277831 < baseStart_5277831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277858 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5277858 : Nat := 118140960795 + 5277858 * 2 ^ 59
def prefixEnd_5277858 : Nat := 4983230072969 + 3 ^ 40 * 5277858 * 2
def baseEnd_5277858 : Nat := 903359326725838863334193

theorem tailTrace_5277858 : CollatzResearch.WordTrace tailWord_5277858 prefixEnd_5277858 903359326725838863334193 := by
  unfold tailWord_5277858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124823928307331807118557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128332863808819551485649485 48124823928307331807118557)
  ·
    refine ⟨18046808973115249427669459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48124823928307331807118557 18046808973115249427669459)
    ·
      refine ⟨27070213459672874141504189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18046808973115249427669459 27070213459672874141504189)
      ·
        refine ⟨10151330047377327803064071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27070213459672874141504189 10151330047377327803064071)
        ·
          refine ⟨15226995071065991704596107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10151330047377327803064071 15226995071065991704596107)
          ·
            refine ⟨22840492606598987556894161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226995071065991704596107 22840492606598987556894161)
            ·
              refine ⟨17130369454949240667670621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22840492606598987556894161 17130369454949240667670621)
              ·
                refine ⟨6423888545605965250376483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17130369454949240667670621 6423888545605965250376483)
                ·
                  refine ⟨9635832818408947875564725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423888545605965250376483 9635832818408947875564725)
                  ·
                    refine ⟨903359326725838863334193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9635832818408947875564725 903359326725838863334193)
                    ·
                      rfl

theorem cell23_5277858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5277858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277858 prefixEnd_5277858 := by exact prefixLift 5277858
  have htrace : WordTrace (prefixWord ++ tailWord_5277858) baseStart_5277858 baseEnd_5277858 := by
    simpa [prefixWord, tailWord_5277858, baseEnd_5277858] using wordTrace_append hprefix tailTrace_5277858
  have hstable : (prefixWord ++ tailWord_5277858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277858).length < 2 ^ (prefixWord ++ tailWord_5277858).sum := by decide
  have hdescent : baseEnd_5277858 < baseStart_5277858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277861 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_5277861 : Nat := 118140960795 + 5277861 * 2 ^ 59
def prefixEnd_5277861 : Nat := 4983230072969 + 3 ^ 40 * 5277861 * 2
def baseEnd_5277861 : Nat := 2710079520619480078265065

theorem tailTrace_5277861 : CollatzResearch.WordTrace tailWord_5277861 prefixEnd_5277861 2710079520619480078265065 := by
  unfold tailWord_5277861
  simp only [CollatzResearch.WordTrace]
  refine ⟨192499405132218458740833437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128332936754812305827222291 192499405132218458740833437)
  ·
    refine ⟨72187276924581922027812539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192499405132218458740833437 72187276924581922027812539)
    ·
      refine ⟨108280915386872883041718809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72187276924581922027812539 108280915386872883041718809)
      ·
        refine ⟨81210686540154662281289107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108280915386872883041718809 81210686540154662281289107)
        ·
          refine ⟨121816029810231993421933661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81210686540154662281289107 121816029810231993421933661)
          ·
            refine ⟨45681011178836997533225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121816029810231993421933661 45681011178836997533225123)
            ·
              refine ⟨68521516768255496299837685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45681011178836997533225123 68521516768255496299837685)
              ·
                refine ⟨6423892197023952778109783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68521516768255496299837685 6423892197023952778109783)
                ·
                  refine ⟨9635838295535929167164675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423892197023952778109783 9635838295535929167164675)
                  ·
                    refine ⟨14453757443303893750747013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9635838295535929167164675 14453757443303893750747013)
                    ·
                      refine ⟨2710079520619480078265065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14453757443303893750747013 2710079520619480078265065)
                      ·
                        rfl

theorem cell23_5277861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_5277861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277861 prefixEnd_5277861 := by exact prefixLift 5277861
  have htrace : WordTrace (prefixWord ++ tailWord_5277861) baseStart_5277861 baseEnd_5277861 := by
    simpa [prefixWord, tailWord_5277861, baseEnd_5277861] using wordTrace_append hprefix tailTrace_5277861
  have hstable : (prefixWord ++ tailWord_5277861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277861).length < 2 ^ (prefixWord ++ tailWord_5277861).sum := by decide
  have hdescent : baseEnd_5277861 < baseStart_5277861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277871 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 2, 4]
def baseStart_5277871 : Nat := 118140960795 + 5277871 * 2 ^ 59
def prefixEnd_5277871 : Nat := 4983230072969 + 3 ^ 40 * 5277871 * 2
def baseEnd_5277871 : Nat := 903361551808675013046673

theorem tailTrace_5277871 : CollatzResearch.WordTrace tailWord_5277871 prefixEnd_5277871 903361551808675013046673 := by
  unfold tailWord_5277871
  simp only [CollatzResearch.WordTrace]
  refine ⟨192499769862182230448697467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128333179908121486965798311 192499769862182230448697467)
  ·
    refine ⟨288749654793273345673046201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192499769862182230448697467 288749654793273345673046201)
    ·
      refine ⟨216562241094955009254784651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288749654793273345673046201 216562241094955009254784651)
      ·
        refine ⟨324843361642432513882176977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216562241094955009254784651 324843361642432513882176977)
        ·
          refine ⟨243632521231824385411632733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324843361642432513882176977 243632521231824385411632733)
          ·
            refine ⟨91362195461934144529362275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243632521231824385411632733 91362195461934144529362275)
            ·
              refine ⟨137043293192901216794043413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91362195461934144529362275 137043293192901216794043413)
              ·
                refine ⟨6423904368417244537220785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137043293192901216794043413 6423904368417244537220785)
                ·
                  refine ⟨4817928276312933402915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6423904368417244537220785 4817928276312933402915589)
                  ·
                    refine ⟨903361551808675013046673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817928276312933402915589 903361551808675013046673)
                    ·
                      rfl

theorem cell23_5277871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_5277871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277871 prefixEnd_5277871 := by exact prefixLift 5277871
  have htrace : WordTrace (prefixWord ++ tailWord_5277871) baseStart_5277871 baseEnd_5277871 := by
    simpa [prefixWord, tailWord_5277871, baseEnd_5277871] using wordTrace_append hprefix tailTrace_5277871
  have hstable : (prefixWord ++ tailWord_5277871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277871).length < 2 ^ (prefixWord ++ tailWord_5277871).sum := by decide
  have hdescent : baseEnd_5277871 < baseStart_5277871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277874 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5277874 : Nat := 118140960795 + 5277874 * 2 ^ 59
def prefixEnd_5277874 : Nat := 4983230072969 + 3 ^ 40 * 5277874 * 2
def baseEnd_5277874 : Nat := 2710086195867988527402505

theorem tailTrace_5277874 : CollatzResearch.WordTrace tailWord_5277874 prefixEnd_5277874 2710086195867988527402505 := by
  unfold tailWord_5277874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124969820292840490264169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128333252854114241307371117 48124969820292840490264169)
  ·
    refine ⟨36093727365219630367698127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48124969820292840490264169 36093727365219630367698127)
    ·
      refine ⟨54140591047829445551547191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36093727365219630367698127 54140591047829445551547191)
      ·
        refine ⟨81210886571744168327320787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54140591047829445551547191 81210886571744168327320787)
        ·
          refine ⟨121816329857616252490981181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81210886571744168327320787 121816329857616252490981181)
          ·
            refine ⟨45681123696606094684117943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121816329857616252490981181 45681123696606094684117943)
            ·
              refine ⟨68521685544909142026176915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45681123696606094684117943 68521685544909142026176915)
              ·
                refine ⟨102782528317363713039265373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68521685544909142026176915 102782528317363713039265373)
                ·
                  refine ⟨38543448119011392389724515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102782528317363713039265373 38543448119011392389724515)
                  ·
                    refine ⟨57815172178517088584586773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38543448119011392389724515 57815172178517088584586773)
                    ·
                      refine ⟨2710086195867988527402505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57815172178517088584586773 2710086195867988527402505)
                      ·
                        rfl

theorem cell23_5277874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5277874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277874 prefixEnd_5277874 := by exact prefixLift 5277874
  have htrace : WordTrace (prefixWord ++ tailWord_5277874) baseStart_5277874 baseEnd_5277874 := by
    simpa [prefixWord, tailWord_5277874, baseEnd_5277874] using wordTrace_append hprefix tailTrace_5277874
  have hstable : (prefixWord ++ tailWord_5277874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277874).length < 2 ^ (prefixWord ++ tailWord_5277874).sum := by decide
  have hdescent : baseEnd_5277874 < baseStart_5277874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277881 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5277881 : Nat := 118140960795 + 5277881 * 2 ^ 59
def prefixEnd_5277881 : Nat := 4983230072969 + 3 ^ 40 * 5277881 * 2
def baseEnd_5277881 : Nat := 2710089790232570000014973

theorem tailTrace_5277881 : CollatzResearch.WordTrace tailWord_5277881 prefixEnd_5277881 2710089790232570000014973 := by
  unfold tailWord_5277881
  simp only [CollatzResearch.WordTrace]
  refine ⟨192500134592146002156561497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128333423061430668104374331 192500134592146002156561497)
  ·
    refine ⟨144375100944109501617421123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192500134592146002156561497 144375100944109501617421123)
    ·
      refine ⟨216562651416164252426131685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144375100944109501617421123 216562651416164252426131685)
      ·
        refine ⟨40605497140530797329899691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216562651416164252426131685 40605497140530797329899691)
        ·
          refine ⟨60908245710796195994849537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40605497140530797329899691 60908245710796195994849537)
          ·
            refine ⟨45681184283097146996137153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60908245710796195994849537 45681184283097146996137153)
            ·
              refine ⟨34260888212322860247102865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45681184283097146996137153 34260888212322860247102865)
              ·
                refine ⟨25695666159242145185327149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34260888212322860247102865 25695666159242145185327149)
                ·
                  refine ⟨9635874809715804444497681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25695666159242145185327149 9635874809715804444497681)
                  ·
                    refine ⟨7226906107286853333373261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9635874809715804444497681 7226906107286853333373261)
                    ·
                      refine ⟨2710089790232570000014973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7226906107286853333373261 2710089790232570000014973)
                      ·
                        rfl

theorem cell23_5277881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5277881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277881 prefixEnd_5277881 := by exact prefixLift 5277881
  have htrace : WordTrace (prefixWord ++ tailWord_5277881) baseStart_5277881 baseEnd_5277881 := by
    simpa [prefixWord, tailWord_5277881, baseEnd_5277881] using wordTrace_append hprefix tailTrace_5277881
  have hstable : (prefixWord ++ tailWord_5277881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277881).length < 2 ^ (prefixWord ++ tailWord_5277881).sum := by decide
  have hdescent : baseEnd_5277881 < baseStart_5277881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277888 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_5277888 : Nat := 118140960795 + 5277888 * 2 ^ 59
def prefixEnd_5277888 : Nat := 4983230072969 + 3 ^ 40 * 5277888 * 2
def baseEnd_5277888 : Nat := 903364461532383824209147

theorem tailTrace_5277888 : CollatzResearch.WordTrace tailWord_5277888 prefixEnd_5277888 903364461532383824209147 := by
  unfold tailWord_5277888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96250194951560321176033159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128333593268747094901377545 96250194951560321176033159)
  ·
    refine ⟨144375292427340481764049739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96250194951560321176033159 144375292427340481764049739)
    ·
      refine ⟨216562938641010722646074609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144375292427340481764049739 216562938641010722646074609)
      ·
        refine ⟨162422203980758041984555957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216562938641010722646074609 162422203980758041984555957)
        ·
          refine ⟨15227081623196066436052121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162422203980758041984555957 15227081623196066436052121)
          ·
            refine ⟨11420311217397049827039091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15227081623196066436052121 11420311217397049827039091)
            ·
              refine ⟨17130466826095574740558637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420311217397049827039091 17130466826095574740558637)
              ·
                refine ⟨6423925059785840527709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17130466826095574740558637 6423925059785840527709489)
                ·
                  refine ⟨4817943794839380395782117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6423925059785840527709489 4817943794839380395782117)
                  ·
                    refine ⟨903364461532383824209147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817943794839380395782117 903364461532383824209147)
                    ·
                      rfl

theorem cell23_5277888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_5277888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5277888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5277888 prefixEnd_5277888 := by exact prefixLift 5277888
  have htrace : WordTrace (prefixWord ++ tailWord_5277888) baseStart_5277888 baseEnd_5277888 := by
    simpa [prefixWord, tailWord_5277888, baseEnd_5277888] using wordTrace_append hprefix tailTrace_5277888
  have hstable : (prefixWord ++ tailWord_5277888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277888).length < 2 ^ (prefixWord ++ tailWord_5277888).sum := by decide
  have hdescent : baseEnd_5277888 < baseStart_5277888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278002 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_5278002 : Nat := 118140960795 + 5278002 * 2 ^ 59
def prefixEnd_5278002 : Nat := 4983230072969 + 3 ^ 40 * 5278002 * 2
def baseEnd_5278002 : Nat := 2710151921391764026601917

theorem tailTrace_5278002 : CollatzResearch.WordTrace tailWord_5278002 prefixEnd_5278002 2710151921391764026601917 := by
  unfold tailWord_5278002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48126136956176909955429065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128336365216471759881144173 48126136956176909955429065)
  ·
    refine ⟨36094602717132682466571799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48126136956176909955429065 36094602717132682466571799)
    ·
      refine ⟨54141904075699023699857699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36094602717132682466571799 54141904075699023699857699)
      ·
        refine ⟨81212856113548535549786549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54141904075699023699857699 81212856113548535549786549)
        ·
          refine ⟨7613705260645175207792489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81212856113548535549786549 7613705260645175207792489)
          ·
            refine ⟨5710278945483881405844367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613705260645175207792489 5710278945483881405844367)
            ·
              refine ⟨8565418418225822108766551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710278945483881405844367 8565418418225822108766551)
              ·
                refine ⟨12848127627338733163149827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565418418225822108766551 12848127627338733163149827)
                ·
                  refine ⟨19272191441008099744724741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12848127627338733163149827 19272191441008099744724741)
                  ·
                    refine ⟨3613535895189018702135889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19272191441008099744724741 3613535895189018702135889)
                    ·
                      refine ⟨2710151921391764026601917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613535895189018702135889 2710151921391764026601917)
                      ·
                        rfl

theorem cell23_5278002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_5278002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278002 prefixEnd_5278002 := by exact prefixLift 5278002
  have htrace : WordTrace (prefixWord ++ tailWord_5278002) baseStart_5278002 baseEnd_5278002 := by
    simpa [prefixWord, tailWord_5278002, baseEnd_5278002] using wordTrace_append hprefix tailTrace_5278002
  have hstable : (prefixWord ++ tailWord_5278002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278002).length < 2 ^ (prefixWord ++ tailWord_5278002).sum := by decide
  have hdescent : baseEnd_5278002 < baseStart_5278002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278048 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_5278048 : Nat := 118140960795 + 5278048 * 2 ^ 59
def prefixEnd_5278048 : Nat := 4983230072969 + 3 ^ 40 * 5278048 * 2
def baseEnd_5278048 : Nat := 2710175541501870846626705

theorem tailTrace_5278048 : CollatzResearch.WordTrace tailWord_5278048 prefixEnd_5278048 2710175541501870846626705 := by
  unfold tailWord_5278048
  simp only [CollatzResearch.WordTrace]
  refine ⟨96253112791270494838945399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128337483721693993118593865 96253112791270494838945399)
  ·
    refine ⟨144379669186905742258418099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96253112791270494838945399 144379669186905742258418099)
    ·
      refine ⟨216569503780358613387627149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144379669186905742258418099 216569503780358613387627149)
      ·
        refine ⟨81213563917634480020360181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216569503780358613387627149 81213563917634480020360181)
        ·
          refine ⟨7613771617278232501908767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81213563917634480020360181 7613771617278232501908767)
          ·
            refine ⟨11420657425917348752863151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613771617278232501908767 11420657425917348752863151)
            ·
              refine ⟨17130986138876023129294727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420657425917348752863151 17130986138876023129294727)
              ·
                refine ⟨25696479208314034693942091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17130986138876023129294727 25696479208314034693942091)
                ·
                  refine ⟨38544718812471052040913137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25696479208314034693942091 38544718812471052040913137)
                  ·
                    refine ⟨28908539109353289030684853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38544718812471052040913137 28908539109353289030684853)
                    ·
                      refine ⟨2710175541501870846626705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28908539109353289030684853 2710175541501870846626705)
                      ·
                        rfl

theorem cell23_5278048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_5278048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278048 prefixEnd_5278048 := by exact prefixLift 5278048
  have htrace : WordTrace (prefixWord ++ tailWord_5278048) baseStart_5278048 baseEnd_5278048 := by
    simpa [prefixWord, tailWord_5278048, baseEnd_5278048] using wordTrace_append hprefix tailTrace_5278048
  have hstable : (prefixWord ++ tailWord_5278048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278048).length < 2 ^ (prefixWord ++ tailWord_5278048).sum := by decide
  have hdescent : baseEnd_5278048 < baseStart_5278048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278085 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_5278085 : Nat := 118140960795 + 5278085 * 2 ^ 59
def prefixEnd_5278085 : Nat := 4983230072969 + 3 ^ 40 * 5278085 * 2
def baseEnd_5278085 : Nat := 903398180095362400621345

theorem tailTrace_5278085 : CollatzResearch.WordTrace tailWord_5278085 prefixEnd_5278085 903398180095362400621345 := by
  unfold tailWord_5278085
  simp only [CollatzResearch.WordTrace]
  refine ⟨192507575083406944996987709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128338383388937963331325139 192507575083406944996987709)
  ·
    refine ⟨72190340656277604373870391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192507575083406944996987709 72190340656277604373870391)
    ·
      refine ⟨108285510984416406560805587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72190340656277604373870391 108285510984416406560805587)
      ·
        refine ⟨162428266476624609841208381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108285510984416406560805587 162428266476624609841208381)
        ·
          refine ⟨60910599928734228690453143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162428266476624609841208381 60910599928734228690453143)
          ·
            refine ⟨91365899893101343035679715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60910599928734228690453143 91365899893101343035679715)
            ·
              refine ⟨137048849839652014553519573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91365899893101343035679715 137048849839652014553519573)
              ·
                refine ⟨3212082418116844091098115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137048849839652014553519573 3212082418116844091098115)
                ·
                  refine ⟨4818123627175266136647173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212082418116844091098115 4818123627175266136647173)
                  ·
                    refine ⟨903398180095362400621345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818123627175266136647173 903398180095362400621345)
                    ·
                      rfl

theorem cell23_5278085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_5278085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278085 prefixEnd_5278085 := by exact prefixLift 5278085
  have htrace : WordTrace (prefixWord ++ tailWord_5278085) baseStart_5278085 baseEnd_5278085 := by
    simpa [prefixWord, tailWord_5278085, baseEnd_5278085] using wordTrace_append hprefix tailTrace_5278085
  have hstable : (prefixWord ++ tailWord_5278085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278085).length < 2 ^ (prefixWord ++ tailWord_5278085).sum := by decide
  have hdescent : baseEnd_5278085 < baseStart_5278085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278101 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_5278101 : Nat := 118140960795 + 5278101 * 2 ^ 59
def prefixEnd_5278101 : Nat := 4983230072969 + 3 ^ 40 * 5278101 * 2
def baseEnd_5278101 : Nat := 2710202755976559139263961

theorem tailTrace_5278101 : CollatzResearch.WordTrace tailWord_5278101 prefixEnd_5278101 2710202755976559139263961 := by
  unfold tailWord_5278101
  simp only [CollatzResearch.WordTrace]
  refine ⟨192508158651348979729570157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128338772434232653153046771 192508158651348979729570157)
  ·
    refine ⟨72190559494255867398588809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192508158651348979729570157 72190559494255867398588809)
    ·
      refine ⟨54142919620691900548941607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72190559494255867398588809 54142919620691900548941607)
      ·
        refine ⟨81214379431037850823412411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54142919620691900548941607 81214379431037850823412411)
        ·
          refine ⟨121821569146556776235118617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81214379431037850823412411 121821569146556776235118617)
          ·
            refine ⟨91366176859917582176338963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121821569146556776235118617 91366176859917582176338963)
            ·
              refine ⟨137049265289876373264508445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91366176859917582176338963 137049265289876373264508445)
              ·
                refine ⟨51393474483703639974190667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137049265289876373264508445 51393474483703639974190667)
                ·
                  refine ⟨77090211725555459961286001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51393474483703639974190667 77090211725555459961286001)
                  ·
                    refine ⟨57817658794166594970964501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77090211725555459961286001 57817658794166594970964501)
                    ·
                      refine ⟨2710202755976559139263961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57817658794166594970964501 2710202755976559139263961)
                      ·
                        rfl

theorem cell23_5278101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_5278101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278101 prefixEnd_5278101 := by exact prefixLift 5278101
  have htrace : WordTrace (prefixWord ++ tailWord_5278101) baseStart_5278101 baseEnd_5278101 := by
    simpa [prefixWord, tailWord_5278101, baseEnd_5278101] using wordTrace_append hprefix tailTrace_5278101
  have hstable : (prefixWord ++ tailWord_5278101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278101).length < 2 ^ (prefixWord ++ tailWord_5278101).sum := by decide
  have hdescent : baseEnd_5278101 < baseStart_5278101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278135 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_5278135 : Nat := 118140960795 + 5278135 * 2 ^ 59
def prefixEnd_5278135 : Nat := 4983230072969 + 3 ^ 40 * 5278135 * 2
def baseEnd_5278135 : Nat := 2710220214318812006238805

theorem tailTrace_5278135 : CollatzResearch.WordTrace tailWord_5278135 prefixEnd_5278135 2710220214318812006238805 := by
  unfold tailWord_5278135
  simp only [CollatzResearch.WordTrace]
  refine ⟨192509398733225803536307859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128339599155483869024205239 192509398733225803536307859)
  ·
    refine ⟨288764098099838705304461789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192509398733225803536307859 288764098099838705304461789)
    ·
      refine ⟨108286536787439514489173171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288764098099838705304461789 108286536787439514489173171)
      ·
        refine ⟨162429805181159271733759757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108286536787439514489173171 162429805181159271733759757)
        ·
          refine ⟨60911176942934726900159909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162429805181159271733759757 60911176942934726900159909)
          ·
            refine ⟨11420845676800261293779983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60911176942934726900159909 11420845676800261293779983)
            ·
              refine ⟨17131268515200391940669975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420845676800261293779983 17131268515200391940669975)
              ·
                refine ⟨25696902772800587911004963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17131268515200391940669975 25696902772800587911004963)
                ·
                  refine ⟨38545354159200881866507445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25696902772800587911004963 38545354159200881866507445)
                  ·
                    refine ⟨3613626952425082674985073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38545354159200881866507445 3613626952425082674985073)
                    ·
                      refine ⟨2710220214318812006238805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613626952425082674985073 2710220214318812006238805)
                      ·
                        rfl

theorem cell23_5278135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_5278135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278135 prefixEnd_5278135 := by exact prefixLift 5278135
  have htrace : WordTrace (prefixWord ++ tailWord_5278135) baseStart_5278135 baseEnd_5278135 := by
    simpa [prefixWord, tailWord_5278135, baseEnd_5278135] using wordTrace_append hprefix tailTrace_5278135
  have hstable : (prefixWord ++ tailWord_5278135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278135).length < 2 ^ (prefixWord ++ tailWord_5278135).sum := by decide
  have hdescent : baseEnd_5278135 < baseStart_5278135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278175 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 6]
def baseStart_5278175 : Nat := 118140960795 + 5278175 * 2 ^ 59
def prefixEnd_5278175 : Nat := 4983230072969 + 3 ^ 40 * 5278175 * 2
def baseEnd_5278175 : Nat := 903413584514997283246207

theorem tailTrace_5278175 : CollatzResearch.WordTrace tailWord_5278175 prefixEnd_5278175 903413584514997283246207 := by
  unfold tailWord_5278175
  simp only [CollatzResearch.WordTrace]
  refine ⟨192510857653080890367763979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128340571768720593578509319 192510857653080890367763979)
  ·
    refine ⟨288766286479621335551645969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192510857653080890367763979 288766286479621335551645969)
    ·
      refine ⟨216574714859716001663734477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288766286479621335551645969 216574714859716001663734477)
      ·
        refine ⟨81215518072393500623900429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216574714859716001663734477 81215518072393500623900429)
        ·
          refine ⟨30455819277147562733962661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81215518072393500623900429 30455819277147562733962661)
          ·
            refine ⟨5710466114465168012617999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30455819277147562733962661 5710466114465168012617999)
            ·
              refine ⟨8565699171697752018926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710466114465168012617999 8565699171697752018926999)
              ·
                refine ⟨12848548757546628028390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565699171697752018926999 12848548757546628028390499)
                ·
                  refine ⟨19272823136319942042585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12848548757546628028390499 19272823136319942042585749)
                  ·
                    refine ⟨903413584514997283246207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19272823136319942042585749 903413584514997283246207)
                    ·
                      rfl

theorem cell23_5278175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_5278175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278175 prefixEnd_5278175 := by exact prefixLift 5278175
  have htrace : WordTrace (prefixWord ++ tailWord_5278175) baseStart_5278175 baseEnd_5278175 := by
    simpa [prefixWord, tailWord_5278175, baseEnd_5278175] using wordTrace_append hprefix tailTrace_5278175
  have hstable : (prefixWord ++ tailWord_5278175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278175).length < 2 ^ (prefixWord ++ tailWord_5278175).sum := by decide
  have hdescent : baseEnd_5278175 < baseStart_5278175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278218 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_5278218 : Nat := 118140960795 + 5278218 * 2 ^ 59
def prefixEnd_5278218 : Nat := 4983230072969 + 3 ^ 40 * 5278218 * 2
def baseEnd_5278218 : Nat := 903420944404378393833641

theorem tailTrace_5278218 : CollatzResearch.WordTrace tailWord_5278218 prefixEnd_5278218 903420944404378393833641 := by
  unfold tailWord_5278218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48128106497981277177894827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128341617327950072474386205 48128106497981277177894827)
  ·
    refine ⟨72192159746971915766842241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48128106497981277177894827 72192159746971915766842241)
    ·
      refine ⟨54144119810228936825131681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72192159746971915766842241 54144119810228936825131681)
      ·
        refine ⟨40608089857671702618848761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54144119810228936825131681 40608089857671702618848761)
        ·
          refine ⟨30456067393253776964136571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40608089857671702618848761 30456067393253776964136571)
          ·
            refine ⟨45684101089880665446204857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30456067393253776964136571 45684101089880665446204857)
            ·
              refine ⟨34263075817410499084653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45684101089880665446204857 34263075817410499084653643)
              ·
                refine ⟨51394613726115748626980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34263075817410499084653643 51394613726115748626980465)
                ·
                  refine ⟨38545960294586811470235349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51394613726115748626980465 38545960294586811470235349)
                  ·
                    refine ⟨903420944404378393833641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38545960294586811470235349 903420944404378393833641)
                    ·
                      rfl

theorem cell23_5278218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_5278218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278218 prefixEnd_5278218 := by exact prefixLift 5278218
  have htrace : WordTrace (prefixWord ++ tailWord_5278218) baseStart_5278218 baseEnd_5278218 := by
    simpa [prefixWord, tailWord_5278218, baseEnd_5278218] using wordTrace_append hprefix tailTrace_5278218
  have hstable : (prefixWord ++ tailWord_5278218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278218).length < 2 ^ (prefixWord ++ tailWord_5278218).sum := by decide
  have hdescent : baseEnd_5278218 < baseStart_5278218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278253 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5278253 : Nat := 118140960795 + 5278253 * 2 ^ 59
def prefixEnd_5278253 : Nat := 4983230072969 + 3 ^ 40 * 5278253 * 2
def baseEnd_5278253 : Nat := 2710280805036042544563263

theorem tailTrace_5278253 : CollatzResearch.WordTrace tailWord_5278253 prefixEnd_5278253 2710280805036042544563263 := by
  unfold tailWord_5278253
  simp only [CollatzResearch.WordTrace]
  refine ⟨192513702546798309689103413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128342468364532206459402275 192513702546798309689103413)
  ·
    refine ⟨18048159613762341533353445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192513702546798309689103413 18048159613762341533353445)
    ·
      refine ⟨3384029927580439037503771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18048159613762341533353445 3384029927580439037503771)
      ·
        refine ⟨5076044891370658556255657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384029927580439037503771 5076044891370658556255657)
        ·
          refine ⟨3807033668527993917191743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5076044891370658556255657 3807033668527993917191743)
          ·
            refine ⟨5710550502791990875787615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807033668527993917191743 5710550502791990875787615)
            ·
              refine ⟨8565825754187986313681423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710550502791990875787615 8565825754187986313681423)
              ·
                refine ⟨12848738631281979470522135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565825754187986313681423 12848738631281979470522135)
                ·
                  refine ⟨19273107946922969205783203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12848738631281979470522135 19273107946922969205783203)
                  ·
                    refine ⟨28909661920384453808674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19273107946922969205783203 28909661920384453808674805)
                    ·
                      refine ⟨2710280805036042544563263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28909661920384453808674805 2710280805036042544563263)
                      ·
                        rfl

theorem cell23_5278253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5278253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278253 prefixEnd_5278253 := by exact prefixLift 5278253
  have htrace : WordTrace (prefixWord ++ tailWord_5278253) baseStart_5278253 baseEnd_5278253 := by
    simpa [prefixWord, tailWord_5278253, baseEnd_5278253] using wordTrace_append hprefix tailTrace_5278253
  have hstable : (prefixWord ++ tailWord_5278253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278253).length < 2 ^ (prefixWord ++ tailWord_5278253).sum := by decide
  have hdescent : baseEnd_5278253 < baseStart_5278253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278259 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 1, 3, 2]
def baseStart_5278259 : Nat := 118140960795 + 5278259 * 2 ^ 59
def prefixEnd_5278259 : Nat := 4983230072969 + 3 ^ 40 * 5278259 * 2
def baseEnd_5278259 : Nat := 2710283885919969521088235

theorem tailTrace_5278259 : CollatzResearch.WordTrace tailWord_5278259 prefixEnd_5278259 2710283885919969521088235 := by
  unfold tailWord_5278259
  simp only [CollatzResearch.WordTrace]
  refine ⟨192513921384776572713821831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128342614256517715142547887 192513921384776572713821831)
  ·
    refine ⟨288770882077164859070732747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192513921384776572713821831 288770882077164859070732747)
    ·
      refine ⟨433156323115747288606099121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288770882077164859070732747 433156323115747288606099121)
      ·
        refine ⟨324867242336810466454574341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433156323115747288606099121 324867242336810466454574341)
        ·
          refine ⟨60912607938151962460232689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324867242336810466454574341 60912607938151962460232689)
          ·
            refine ⟨45684455953613971845174517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60912607938151962460232689 45684455953613971845174517)
            ·
              refine ⟨4282917745651309860485111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45684455953613971845174517 4282917745651309860485111)
              ·
                refine ⟨6424376618476964790727667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282917745651309860485111 6424376618476964790727667)
                ·
                  refine ⟨9636564927715447186091501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424376618476964790727667 9636564927715447186091501)
                  ·
                    refine ⟨3613711847893292694784313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9636564927715447186091501 3613711847893292694784313)
                    ·
                      refine ⟨2710283885919969521088235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613711847893292694784313 2710283885919969521088235)
                      ·
                        rfl

theorem cell23_5278259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 3, 2].length) (baseStart_5278259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278259 prefixEnd_5278259 := by exact prefixLift 5278259
  have htrace : WordTrace (prefixWord ++ tailWord_5278259) baseStart_5278259 baseEnd_5278259 := by
    simpa [prefixWord, tailWord_5278259, baseEnd_5278259] using wordTrace_append hprefix tailTrace_5278259
  have hstable : (prefixWord ++ tailWord_5278259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278259).length < 2 ^ (prefixWord ++ tailWord_5278259).sum := by decide
  have hdescent : baseEnd_5278259 < baseStart_5278259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278272 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2]
def baseStart_5278272 : Nat := 118140960795 + 5278272 * 2 ^ 59
def prefixEnd_5278272 : Nat := 4983230072969 + 3 ^ 40 * 5278272 * 2
def baseEnd_5278272 : Nat := 2710290561168477970225675

theorem tailTrace_5278272 : CollatzResearch.WordTrace tailWord_5278272 prefixEnd_5278272 2710290561168477970225675 := by
  unfold tailWord_5278272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96257197766864737967022535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128342930355819650622696713 96257197766864737967022535)
  ·
    refine ⟨144385796650297106950533803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96257197766864737967022535 144385796650297106950533803)
    ·
      refine ⟨216578694975445660425800705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144385796650297106950533803 216578694975445660425800705)
      ·
        refine ⟨162434021231584245319350529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216578694975445660425800705 162434021231584245319350529)
        ·
          refine ⟨121825515923688183989512897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162434021231584245319350529 121825515923688183989512897)
          ·
            refine ⟨91369136942766137992134673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121825515923688183989512897 91369136942766137992134673)
            ·
              refine ⟨68526852707074603494101005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91369136942766137992134673 68526852707074603494101005)
              ·
                refine ⟨25697569765152976310287877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68526852707074603494101005 25697569765152976310287877)
                ·
                  refine ⟨4818294330966183058178977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25697569765152976310287877 4818294330966183058178977)
                  ·
                    refine ⟨3613720748224637293634233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4818294330966183058178977 3613720748224637293634233)
                    ·
                      refine ⟨2710290561168477970225675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613720748224637293634233 2710290561168477970225675)
                      ·
                        rfl

theorem cell23_5278272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_5278272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278272 prefixEnd_5278272 := by exact prefixLift 5278272
  have htrace : WordTrace (prefixWord ++ tailWord_5278272) baseStart_5278272 baseEnd_5278272 := by
    simpa [prefixWord, tailWord_5278272, baseEnd_5278272] using wordTrace_append hprefix tailTrace_5278272
  have hstable : (prefixWord ++ tailWord_5278272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278272).length < 2 ^ (prefixWord ++ tailWord_5278272).sum := by decide
  have hdescent : baseEnd_5278272 < baseStart_5278272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278289 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_5278289 : Nat := 118140960795 + 5278289 * 2 ^ 59
def prefixEnd_5278289 : Nat := 4983230072969 + 3 ^ 40 * 5278289 * 2
def baseEnd_5278289 : Nat := 2710299290339604403713097

theorem tailTrace_5278289 : CollatzResearch.WordTrace tailWord_5278289 prefixEnd_5278289 2710299290339604403713097 := by
  unfold tailWord_5278289
  simp only [CollatzResearch.WordTrace]
  refine ⟨192515015574667887837413921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128343343716445258558275947 192515015574667887837413921)
  ·
    refine ⟨144386261681000915878060441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192515015574667887837413921 144386261681000915878060441)
    ·
      refine ⟨108289696260750686908545331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144386261681000915878060441 108289696260750686908545331)
      ·
        refine ⟨162434544391126030362817997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108289696260750686908545331 162434544391126030362817997)
        ·
          refine ⟨60912954146672261386056749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162434544391126030362817997 60912954146672261386056749)
          ·
            refine ⟨22842357805002098019771281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60912954146672261386056749 22842357805002098019771281)
            ·
              refine ⟨17131768353751573514828461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22842357805002098019771281 17131768353751573514828461)
              ·
                refine ⟨6424413132656840068060673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17131768353751573514828461 6424413132656840068060673)
                ·
                  refine ⟨4818309849492630051045505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6424413132656840068060673 4818309849492630051045505)
                  ·
                    refine ⟨3613732387119472538284129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4818309849492630051045505 3613732387119472538284129)
                    ·
                      refine ⟨2710299290339604403713097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613732387119472538284129 2710299290339604403713097)
                      ·
                        rfl

theorem cell23_5278289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_5278289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278289 prefixEnd_5278289 := by exact prefixLift 5278289
  have htrace : WordTrace (prefixWord ++ tailWord_5278289) baseStart_5278289 baseEnd_5278289 := by
    simpa [prefixWord, tailWord_5278289, baseEnd_5278289] using wordTrace_append hprefix tailTrace_5278289
  have hstable : (prefixWord ++ tailWord_5278289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278289).length < 2 ^ (prefixWord ++ tailWord_5278289).sum := by decide
  have hdescent : baseEnd_5278289 < baseStart_5278289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278315 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 7, 2]
def baseStart_5278315 : Nat := 118140960795 + 5278315 * 2 ^ 59
def prefixEnd_5278315 : Nat := 4983230072969 + 3 ^ 40 * 5278315 * 2
def baseEnd_5278315 : Nat := 2710312640836621301987977

theorem tailTrace_5278315 : CollatzResearch.WordTrace tailWord_5278315 prefixEnd_5278315 2710312640836621301987977 := by
  unfold tailWord_5278315
  simp only [CollatzResearch.WordTrace]
  refine ⟨192515963872573694277860399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128343975915049129518573599 192515963872573694277860399)
  ·
    refine ⟨288773945808860541416790599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192515963872573694277860399 288773945808860541416790599)
    ·
      refine ⟨433160918713290812125185899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288773945808860541416790599 433160918713290812125185899)
      ·
        refine ⟨649741378069936218187778849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433160918713290812125185899 649741378069936218187778849)
        ·
          refine ⟨487306033552452163640834137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649741378069936218187778849 487306033552452163640834137)
          ·
            refine ⟨365479525164339122730625603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487306033552452163640834137 365479525164339122730625603)
            ·
              refine ⟨548219287746508684095938405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365479525164339122730625603 548219287746508684095938405)
              ·
                refine ⟨102791116452470378267988451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548219287746508684095938405 102791116452470378267988451)
                ·
                  refine ⟨154186674678705567401982677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102791116452470378267988451 154186674678705567401982677)
                  ·
                    refine ⟨3613750187782161735983969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154186674678705567401982677 3613750187782161735983969)
                    ·
                      refine ⟨2710312640836621301987977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613750187782161735983969 2710312640836621301987977)
                      ·
                        rfl

theorem cell23_5278315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7, 2].length) (baseStart_5278315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278315 prefixEnd_5278315 := by exact prefixLift 5278315
  have htrace : WordTrace (prefixWord ++ tailWord_5278315) baseStart_5278315 baseEnd_5278315 := by
    simpa [prefixWord, tailWord_5278315, baseEnd_5278315] using wordTrace_append hprefix tailTrace_5278315
  have hstable : (prefixWord ++ tailWord_5278315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278315).length < 2 ^ (prefixWord ++ tailWord_5278315).sum := by decide
  have hdescent : baseEnd_5278315 < baseStart_5278315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278389 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5278389 : Nat := 118140960795 + 5278389 * 2 ^ 59
def prefixEnd_5278389 : Nat := 4983230072969 + 3 ^ 40 * 5278389 * 2
def baseEnd_5278389 : Nat := 903450212801684670820879

theorem tailTrace_5278389 : CollatzResearch.WordTrace tailWord_5278389 prefixEnd_5278389 903450212801684670820879 := by
  unfold tailWord_5278389
  simp only [CollatzResearch.WordTrace]
  refine ⟨192518662874305604916054221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128345775249537069944036147 192518662874305604916054221)
  ·
    refine ⟨72194498577864601843520333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192518662874305604916054221 72194498577864601843520333)
    ·
      refine ⟨27072936966699225691320125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72194498577864601843520333 27072936966699225691320125)
      ·
        refine ⟨10152351362512209634245047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27072936966699225691320125 10152351362512209634245047)
        ·
          refine ⟨15228527043768314451367571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10152351362512209634245047 15228527043768314451367571)
          ·
            refine ⟨22842790565652471677051357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15228527043768314451367571 22842790565652471677051357)
            ·
              refine ⟨8566046462119676878894259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22842790565652471677051357 8566046462119676878894259)
              ·
                refine ⟨12849069693179515318341389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8566046462119676878894259 12849069693179515318341389)
                ·
                  refine ⟨4818401134942318244378021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12849069693179515318341389 4818401134942318244378021)
                  ·
                    refine ⟨903450212801684670820879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818401134942318244378021 903450212801684670820879)
                    ·
                      rfl

theorem cell23_5278389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5278389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278389 prefixEnd_5278389 := by exact prefixLift 5278389
  have htrace : WordTrace (prefixWord ++ tailWord_5278389) baseStart_5278389 baseEnd_5278389 := by
    simpa [prefixWord, tailWord_5278389, baseEnd_5278389] using wordTrace_append hprefix tailTrace_5278389
  have hstable : (prefixWord ++ tailWord_5278389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278389).length < 2 ^ (prefixWord ++ tailWord_5278389).sum := by decide
  have hdescent : baseEnd_5278389 < baseStart_5278389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278440 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 1, 4]
def baseStart_5278440 : Nat := 118140960795 + 5278440 * 2 ^ 59
def prefixEnd_5278440 : Nat := 4983230072969 + 3 ^ 40 * 5278440 * 2
def baseEnd_5278440 : Nat := 903458941972811104308301

theorem tailTrace_5278440 : CollatzResearch.WordTrace tailWord_5278440 prefixEnd_5278440 903458941972811104308301 := by
  unfold tailWord_5278440
  simp only [CollatzResearch.WordTrace]
  refine ⟨96260261498560420313080387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128347015331413893750773849 96260261498560420313080387)
  ·
    refine ⟨144390392247840630469620581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96260261498560420313080387 144390392247840630469620581)
    ·
      refine ⟨27073198546470118213053859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144390392247840630469620581 27073198546470118213053859)
      ·
        refine ⟨40609797819705177319580789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27073198546470118213053859 40609797819705177319580789)
        ·
          refine ⟨3807168545597360373710699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40609797819705177319580789 3807168545597360373710699)
          ·
            refine ⟨5710752818396040560566049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807168545597360373710699 5710752818396040560566049)
            ·
              refine ⟨4283064613797030420424537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5710752818396040560566049 4283064613797030420424537)
              ·
                refine ⟨3212298460347772815318403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4283064613797030420424537 3212298460347772815318403)
                ·
                  refine ⟨4818447690521659222977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212298460347772815318403 4818447690521659222977605)
                  ·
                    refine ⟨903458941972811104308301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818447690521659222977605 903458941972811104308301)
                    ·
                      rfl

theorem cell23_5278440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_5278440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278440 prefixEnd_5278440 := by exact prefixLift 5278440
  have htrace : WordTrace (prefixWord ++ tailWord_5278440) baseStart_5278440 baseEnd_5278440 := by
    simpa [prefixWord, tailWord_5278440, baseEnd_5278440] using wordTrace_append hprefix tailTrace_5278440
  have hstable : (prefixWord ++ tailWord_5278440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278440).length < 2 ^ (prefixWord ++ tailWord_5278440).sum := by decide
  have hdescent : baseEnd_5278440 < baseStart_5278440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278455 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_5278455 : Nat := 118140960795 + 5278455 * 2 ^ 59
def prefixEnd_5278455 : Nat := 4983230072969 + 3 ^ 40 * 5278455 * 2
def baseEnd_5278455 : Nat := 2710384528128250754237333

theorem tailTrace_5278455 : CollatzResearch.WordTrace tailWord_5278455 prefixEnd_5278455 2710384528128250754237333 := by
  unfold tailWord_5278455
  simp only [CollatzResearch.WordTrace]
  refine ⟨192521070092066498187956819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128347380061377665458637879 192521070092066498187956819)
  ·
    refine ⟨288781605138099747281935229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192521070092066498187956819 288781605138099747281935229)
    ·
      refine ⟨108293101926787405230725711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288781605138099747281935229 108293101926787405230725711)
      ·
        refine ⟨162439652890181107846088567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108293101926787405230725711 162439652890181107846088567)
        ·
          refine ⟨243659479335271661769132851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162439652890181107846088567 243659479335271661769132851)
          ·
            refine ⟨365489219002907492653699277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243659479335271661769132851 365489219002907492653699277)
            ·
              refine ⟨137058457126090309745137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365489219002907492653699277 137058457126090309745137229)
              ·
                refine ⟨51396921422283866154426461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137058457126090309745137229 51396921422283866154426461)
                ·
                  refine ⟨19273845533356449807909923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51396921422283866154426461 19273845533356449807909923)
                  ·
                    refine ⟨28910768300034674711864885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19273845533356449807909923 28910768300034674711864885)
                    ·
                      refine ⟨2710384528128250754237333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28910768300034674711864885 2710384528128250754237333)
                      ·
                        rfl

theorem cell23_5278455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_5278455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278455 prefixEnd_5278455 := by exact prefixLift 5278455
  have htrace : WordTrace (prefixWord ++ tailWord_5278455) baseStart_5278455 baseEnd_5278455 := by
    simpa [prefixWord, tailWord_5278455, baseEnd_5278455] using wordTrace_append hprefix tailTrace_5278455
  have hstable : (prefixWord ++ tailWord_5278455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278455).length < 2 ^ (prefixWord ++ tailWord_5278455).sum := by decide
  have hdescent : baseEnd_5278455 < baseStart_5278455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278496 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_5278496 : Nat := 118140960795 + 5278496 * 2 ^ 59
def prefixEnd_5278496 : Nat := 4983230072969 + 3 ^ 40 * 5278496 * 2
def baseEnd_5278496 : Nat := 903468526945028364608215

theorem tailTrace_5278496 : CollatzResearch.WordTrace tailWord_5278496 prefixEnd_5278496 903468526945028364608215 := by
  unfold tailWord_5278496
  simp only [CollatzResearch.WordTrace]
  refine ⟨96261282742458981095099671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128348376989945308126799561 96261282742458981095099671)
  ·
    refine ⟨144391924113688471642649507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96261282742458981095099671 144391924113688471642649507)
    ·
      refine ⟨216587886170532707463974261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144391924113688471642649507 216587886170532707463974261)
      ·
        refine ⟨20305114328487441324747587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216587886170532707463974261 20305114328487441324747587)
        ·
          refine ⟨30457671492731161987121381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20305114328487441324747587 30457671492731161987121381)
          ·
            refine ⟨5710813404887092872585259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30457671492731161987121381 5710813404887092872585259)
            ·
              refine ⟨8566220107330639308877889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710813404887092872585259 8566220107330639308877889)
              ·
                refine ⟨6424665080497979481658417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8566220107330639308877889 6424665080497979481658417)
                ·
                  refine ⟨4818498810373484611243813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6424665080497979481658417 4818498810373484611243813)
                  ·
                    refine ⟨903468526945028364608215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818498810373484611243813 903468526945028364608215)
                    ·
                      rfl

theorem cell23_5278496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_5278496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278496 prefixEnd_5278496 := by exact prefixLift 5278496
  have htrace : WordTrace (prefixWord ++ tailWord_5278496) baseStart_5278496 baseEnd_5278496 := by
    simpa [prefixWord, tailWord_5278496, baseEnd_5278496] using wordTrace_append hprefix tailTrace_5278496
  have hstable : (prefixWord ++ tailWord_5278496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278496).length < 2 ^ (prefixWord ++ tailWord_5278496).sum := by decide
  have hdescent : baseEnd_5278496 < baseStart_5278496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278506 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5278506 : Nat := 118140960795 + 5278506 * 2 ^ 59
def prefixEnd_5278506 : Nat := 4983230072969 + 3 ^ 40 * 5278506 * 2
def baseEnd_5278506 : Nat := 2710410715641630054699599

theorem tailTrace_5278506 : CollatzResearch.WordTrace tailWord_5278506 prefixEnd_5278506 2710410715641630054699599 := by
  unfold tailWord_5278506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48130732553720433474515843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128348620143254489265375581 48130732553720433474515843)
  ·
    refine ⟨72196098830580650211773765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48130732553720433474515843 72196098830580650211773765)
    ·
      refine ⟨13536768530733871914707581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72196098830580650211773765 13536768530733871914707581)
      ·
        refine ⟨5076288199025201968015343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13536768530733871914707581 5076288199025201968015343)
        ·
          refine ⟨7614432298537802952023015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076288199025201968015343 7614432298537802952023015)
          ·
            refine ⟨11421648447806704428034523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614432298537802952023015 11421648447806704428034523)
            ·
              refine ⟨17132472671710056642051785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421648447806704428034523 17132472671710056642051785)
              ·
                refine ⟨12849354503782542481538839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17132472671710056642051785 12849354503782542481538839)
                ·
                  refine ⟨19274031755673813722308259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12849354503782542481538839 19274031755673813722308259)
                  ·
                    refine ⟨28911047633510720583462389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19274031755673813722308259 28911047633510720583462389)
                    ·
                      refine ⟨2710410715641630054699599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28911047633510720583462389 2710410715641630054699599)
                      ·
                        rfl

theorem cell23_5278506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5278506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278506 prefixEnd_5278506 := by exact prefixLift 5278506
  have htrace : WordTrace (prefixWord ++ tailWord_5278506) baseStart_5278506 baseEnd_5278506 := by
    simpa [prefixWord, tailWord_5278506, baseEnd_5278506] using wordTrace_append hprefix tailTrace_5278506
  have hstable : (prefixWord ++ tailWord_5278506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278506).length < 2 ^ (prefixWord ++ tailWord_5278506).sum := by decide
  have hdescent : baseEnd_5278506 < baseStart_5278506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278526 : List Nat := [4, 2, 1, 2, 3, 2, 2, 7]
def baseStart_5278526 : Nat := 118140960795 + 5278526 * 2 ^ 59
def prefixEnd_5278526 : Nat := 4983230072969 + 3 ^ 40 * 5278526 * 2
def baseEnd_5278526 : Nat := 100385962416841480609241

theorem tailTrace_5278526 : CollatzResearch.WordTrace tailWord_5278526 prefixEnd_5278526 100385962416841480609241 := by
  unfold tailWord_5278526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24065457459351159664223929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128349106449872851542527621 24065457459351159664223929)
  ·
    refine ⟨18049093094513369748167947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24065457459351159664223929 18049093094513369748167947)
    ·
      refine ⟨27073639641770054622251921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049093094513369748167947 27073639641770054622251921)
      ·
        refine ⟨20305229731327540966688941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27073639641770054622251921 20305229731327540966688941)
        ·
          refine ⟨7614461149247827862508353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20305229731327540966688941 7614461149247827862508353)
          ·
            refine ⟨5710845861935870896881265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7614461149247827862508353 5710845861935870896881265)
            ·
              refine ⟨4283134396451903172660949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5710845861935870896881265 4283134396451903172660949)
              ·
                refine ⟨100385962416841480609241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4283134396451903172660949 100385962416841480609241)
                ·
                  rfl

theorem cell23_5278526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_5278526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278526 prefixEnd_5278526 := by exact prefixLift 5278526
  have htrace : WordTrace (prefixWord ++ tailWord_5278526) baseStart_5278526 baseEnd_5278526 := by
    simpa [prefixWord, tailWord_5278526, baseEnd_5278526] using wordTrace_append hprefix tailTrace_5278526
  have hstable : (prefixWord ++ tailWord_5278526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278526).length < 2 ^ (prefixWord ++ tailWord_5278526).sum := by decide
  have hdescent : baseEnd_5278526 < baseStart_5278526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278546 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_5278546 : Nat := 118140960795 + 5278546 * 2 ^ 59
def prefixEnd_5278546 : Nat := 4983230072969 + 3 ^ 40 * 5278546 * 2
def baseEnd_5278546 : Nat := 2710431254867809898199415

theorem tailTrace_5278546 : CollatzResearch.WordTrace tailWord_5278546 prefixEnd_5278546 2710431254867809898199415 := by
  unfold tailWord_5278546
  simp only [CollatzResearch.WordTrace]
  refine ⟨48131097283684205182379873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128349592756491213819679661 48131097283684205182379873)
  ·
    refine ⟨36098322962763153886784905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48131097283684205182379873 36098322962763153886784905)
    ·
      refine ⟨27073742222072365415088679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36098322962763153886784905 27073742222072365415088679)
      ·
        refine ⟨40610613333108548122633019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27073742222072365415088679 40610613333108548122633019)
        ·
          refine ⟨60915919999662822183949529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40610613333108548122633019 60915919999662822183949529)
          ·
            refine ⟨45686939999747116637962147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60915919999662822183949529 45686939999747116637962147)
            ·
              refine ⟨68530409999620674956943221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45686939999747116637962147 68530409999620674956943221)
              ·
                refine ⟨6424725937464438277213427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68530409999620674956943221 6424725937464438277213427)
                ·
                  refine ⟨9637088906196657415820141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424725937464438277213427 9637088906196657415820141)
                  ·
                    refine ⟨3613908339823746530932553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9637088906196657415820141 3613908339823746530932553)
                    ·
                      refine ⟨2710431254867809898199415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3613908339823746530932553 2710431254867809898199415)
                      ·
                        rfl

theorem cell23_5278546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_5278546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278546 prefixEnd_5278546 := by exact prefixLift 5278546
  have htrace : WordTrace (prefixWord ++ tailWord_5278546) baseStart_5278546 baseEnd_5278546 := by
    simpa [prefixWord, tailWord_5278546, baseEnd_5278546] using wordTrace_append hprefix tailTrace_5278546
  have hstable : (prefixWord ++ tailWord_5278546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278546).length < 2 ^ (prefixWord ++ tailWord_5278546).sum := by decide
  have hdescent : baseEnd_5278546 < baseStart_5278546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278572 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_5278572 : Nat := 118140960795 + 5278572 * 2 ^ 59
def prefixEnd_5278572 : Nat := 4983230072969 + 3 ^ 40 * 5278572 * 2
def baseEnd_5278572 : Nat := 2710444605364826796474295

theorem tailTrace_5278572 : CollatzResearch.WordTrace tailWord_5278572 prefixEnd_5278572 2710444605364826796474295 := by
  unfold tailWord_5278572
  simp only [CollatzResearch.WordTrace]
  refine ⟨96262668716321313584982985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128350224955095084779977313 96262668716321313584982985)
  ·
    refine ⟨72197001537240985188737239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96262668716321313584982985 72197001537240985188737239)
    ·
      refine ⟨108295502305861477783105859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72197001537240985188737239 108295502305861477783105859)
      ·
        refine ⟨162443253458792216674658789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108295502305861477783105859 162443253458792216674658789)
        ·
          refine ⟨30458110023523540626498523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162443253458792216674658789 30458110023523540626498523)
          ·
            refine ⟨45687165035285310939747785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30458110023523540626498523 45687165035285310939747785)
            ·
              refine ⟨34265373776463983204810839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45687165035285310939747785 34265373776463983204810839)
              ·
                refine ⟨51398060664695974807216259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34265373776463983204810839 51398060664695974807216259)
                ·
                  refine ⟨77097090997043962210824389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51398060664695974807216259 77097090997043962210824389)
                  ·
                    refine ⟨14455704561945742914529573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77097090997043962210824389 14455704561945742914529573)
                    ·
                      refine ⟨2710444605364826796474295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14455704561945742914529573 2710444605364826796474295)
                      ·
                        rfl

theorem cell23_5278572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_5278572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278572 prefixEnd_5278572 := by exact prefixLift 5278572
  have htrace : WordTrace (prefixWord ++ tailWord_5278572) baseStart_5278572 baseEnd_5278572 := by
    simpa [prefixWord, tailWord_5278572, baseEnd_5278572] using wordTrace_append hprefix tailTrace_5278572
  have hstable : (prefixWord ++ tailWord_5278572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278572).length < 2 ^ (prefixWord ++ tailWord_5278572).sum := by decide
  have hdescent : baseEnd_5278572 < baseStart_5278572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278592 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_5278592 : Nat := 118140960795 + 5278592 * 2 ^ 59
def prefixEnd_5278592 : Nat := 4983230072969 + 3 ^ 40 * 5278592 * 2
def baseEnd_5278592 : Nat := 2710454874977916718224203

theorem tailTrace_5278592 : CollatzResearch.WordTrace tailWord_5278592 prefixEnd_5278592 2710454874977916718224203 := by
  unfold tailWord_5278592
  simp only [CollatzResearch.WordTrace]
  refine ⟨96263033446285085292847015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128350711261713447057129353 96263033446285085292847015)
  ·
    refine ⟨144394550169427627939270523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96263033446285085292847015 144394550169427627939270523)
    ·
      refine ⟨216591825254141441908905785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144394550169427627939270523 216591825254141441908905785)
      ·
        refine ⟨162443868940606081431679339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216591825254141441908905785 162443868940606081431679339)
        ·
          refine ⟨243665803410909122147519009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162443868940606081431679339 243665803410909122147519009)
          ·
            refine ⟨182749352558181841610639257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243665803410909122147519009 182749352558181841610639257)
            ·
              refine ⟨137062014418636381207979443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182749352558181841610639257 137062014418636381207979443)
              ·
                refine ⟨205593021627954571811969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137062014418636381207979443 205593021627954571811969165)
                ·
                  refine ⟨77097383110482964429488437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205593021627954571811969165 77097383110482964429488437)
                  ·
                    refine ⟨7227879666607777915264541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77097383110482964429488437 7227879666607777915264541)
                    ·
                      refine ⟨2710454874977916718224203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7227879666607777915264541 2710454874977916718224203)
                      ·
                        rfl

theorem cell23_5278592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_5278592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278592 prefixEnd_5278592 := by exact prefixLift 5278592
  have htrace : WordTrace (prefixWord ++ tailWord_5278592) baseStart_5278592 baseEnd_5278592 := by
    simpa [prefixWord, tailWord_5278592, baseEnd_5278592] using wordTrace_append hprefix tailTrace_5278592
  have hstable : (prefixWord ++ tailWord_5278592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278592).length < 2 ^ (prefixWord ++ tailWord_5278592).sum := by decide
  have hdescent : baseEnd_5278592 < baseStart_5278592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278626 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5278626 : Nat := 118140960795 + 5278626 * 2 ^ 59
def prefixEnd_5278626 : Nat := 4983230072969 + 3 ^ 40 * 5278626 * 2
def baseEnd_5278626 : Nat := 2710472333320169585199047

theorem tailTrace_5278626 : CollatzResearch.WordTrace tailWord_5278626 prefixEnd_5278626 2710472333320169585199047 := by
  unfold tailWord_5278626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48131826743611748598107933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128351537982964662928287821 48131826743611748598107933)
  ·
    refine ⟨18049435028854405724290475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48131826743611748598107933 18049435028854405724290475)
    ·
      refine ⟨27074152543281608586435713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049435028854405724290475 27074152543281608586435713)
      ·
        refine ⟨20305614407461206439826785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27074152543281608586435713 20305614407461206439826785)
        ·
          refine ⟨15229210805595904829870089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20305614407461206439826785 15229210805595904829870089)
          ·
            refine ⟨11421908104196928622402567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15229210805595904829870089 11421908104196928622402567)
            ·
              refine ⟨17132862156295392933603851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421908104196928622402567 17132862156295392933603851)
              ·
                refine ⟨25699293234443089400405777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17132862156295392933603851 25699293234443089400405777)
                ·
                  refine ⟨19274469925832317050304333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25699293234443089400405777 19274469925832317050304333)
                  ·
                    refine ⟨7227926222187118893864125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19274469925832317050304333 7227926222187118893864125)
                    ·
                      refine ⟨2710472333320169585199047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7227926222187118893864125 2710472333320169585199047)
                      ·
                        rfl

theorem cell23_5278626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5278626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278626 prefixEnd_5278626 := by exact prefixLift 5278626
  have htrace : WordTrace (prefixWord ++ tailWord_5278626) baseStart_5278626 baseEnd_5278626 := by
    simpa [prefixWord, tailWord_5278626, baseEnd_5278626] using wordTrace_append hprefix tailTrace_5278626
  have hstable : (prefixWord ++ tailWord_5278626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278626).length < 2 ^ (prefixWord ++ tailWord_5278626).sum := by decide
  have hdescent : baseEnd_5278626 < baseStart_5278626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278649 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5278649 : Nat := 118140960795 + 5278649 * 2 ^ 59
def prefixEnd_5278649 : Nat := 4983230072969 + 3 ^ 40 * 5278649 * 2
def baseEnd_5278649 : Nat := 2710484143375222995211441

theorem tailTrace_5278649 : CollatzResearch.WordTrace tailWord_5278649 prefixEnd_5278649 2710484143375222995211441 := by
  unfold tailWord_5278649
  simp only [CollatzResearch.WordTrace]
  refine ⟨192528145853363669320519001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128352097235575779547012667 192528145853363669320519001)
  ·
    refine ⟨144396109390022751990389251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192528145853363669320519001 144396109390022751990389251)
    ·
      refine ⟨216594164085034127985583877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144396109390022751990389251 216594164085034127985583877)
      ·
        refine ⟨40611405765943898997296977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216594164085034127985583877 40611405765943898997296977)
        ·
          refine ⟨30458554324457924247972733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40611405765943898997296977 30458554324457924247972733)
          ·
            refine ⟨11421957871671721592989775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30458554324457924247972733 11421957871671721592989775)
            ·
              refine ⟨17132936807507582389484663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421957871671721592989775 17132936807507582389484663)
              ·
                refine ⟨25699405211261373584226995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17132936807507582389484663 25699405211261373584226995)
                ·
                  refine ⟨38549107816892060376340493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25699405211261373584226995 38549107816892060376340493)
                  ·
                    refine ⟨14455915431334522641127685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38549107816892060376340493 14455915431334522641127685)
                    ·
                      refine ⟨2710484143375222995211441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14455915431334522641127685 2710484143375222995211441)
                      ·
                        rfl

theorem cell23_5278649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5278649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278649 prefixEnd_5278649 := by exact prefixLift 5278649
  have htrace : WordTrace (prefixWord ++ tailWord_5278649) baseStart_5278649 baseEnd_5278649 := by
    simpa [prefixWord, tailWord_5278649, baseEnd_5278649] using wordTrace_append hprefix tailTrace_5278649
  have hstable : (prefixWord ++ tailWord_5278649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278649).length < 2 ^ (prefixWord ++ tailWord_5278649).sum := by decide
  have hdescent : baseEnd_5278649 < baseStart_5278649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278676 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_5278676 : Nat := 118140960795 + 5278676 * 2 ^ 59
def prefixEnd_5278676 : Nat := 4983230072969 + 3 ^ 40 * 5278676 * 2
def baseEnd_5278676 : Nat := 903499335784298129857939

theorem tailTrace_5278676 : CollatzResearch.WordTrace tailWord_5278676 prefixEnd_5278676 903499335784298129857939 := by
  unfold tailWord_5278676
  simp only [CollatzResearch.WordTrace]
  refine ⟨96264565312132926465875941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128352753749510568621167921 96264565312132926465875941)
  ·
    refine ⟨18049605996024923712351739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96264565312132926465875941 18049605996024923712351739)
    ·
      refine ⟨27074408994037385568527609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049605996024923712351739 27074408994037385568527609)
      ·
        refine ⟨20305806745528039176395707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27074408994037385568527609 20305806745528039176395707)
        ·
          refine ⟨30458710118292058764593561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20305806745528039176395707 30458710118292058764593561)
          ·
            refine ⟨22844032588719044073445171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30458710118292058764593561 22844032588719044073445171)
            ·
              refine ⟨34266048883078566110167757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22844032588719044073445171 34266048883078566110167757)
              ·
                refine ⟨12849768331154462291312909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34266048883078566110167757 12849768331154462291312909)
                ·
                  refine ⟨4818663124182923359242341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12849768331154462291312909 4818663124182923359242341)
                  ·
                    refine ⟨903499335784298129857939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818663124182923359242341 903499335784298129857939)
                    ·
                      rfl

theorem cell23_5278676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_5278676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278676 prefixEnd_5278676 := by exact prefixLift 5278676
  have htrace : WordTrace (prefixWord ++ tailWord_5278676) baseStart_5278676 baseEnd_5278676 := by
    simpa [prefixWord, tailWord_5278676, baseEnd_5278676] using wordTrace_append hprefix tailTrace_5278676
  have hstable : (prefixWord ++ tailWord_5278676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278676).length < 2 ^ (prefixWord ++ tailWord_5278676).sum := by decide
  have hdescent : baseEnd_5278676 < baseStart_5278676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278710 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_5278710 : Nat := 118140960795 + 5278710 * 2 ^ 59
def prefixEnd_5278710 : Nat := 4983230072969 + 3 ^ 40 * 5278710 * 2
def baseEnd_5278710 : Nat := 903505155231715752182887

theorem tailTrace_5278710 : CollatzResearch.WordTrace tailWord_5278710 prefixEnd_5278710 903505155231715752182887 := by
  unfold tailWord_5278710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033148169133917296155599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128353580470761784492326389 12033148169133917296155599)
  ·
    refine ⟨18049722253700875944233399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12033148169133917296155599 18049722253700875944233399)
    ·
      refine ⟨27074583380551313916350099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049722253700875944233399 27074583380551313916350099)
      ·
        refine ⟨40611875070826970874525149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27074583380551313916350099 40611875070826970874525149)
        ·
          refine ⟨15229453151560114077946931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40611875070826970874525149 15229453151560114077946931)
          ·
            refine ⟨22844179727340171116920397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15229453151560114077946931 22844179727340171116920397)
            ·
              refine ⟨8566567397752564168845149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22844179727340171116920397 8566567397752564168845149)
              ·
                refine ⟨3212462774157211563316931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8566567397752564168845149 3212462774157211563316931)
                ·
                  refine ⟨4818694161235817344975397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212462774157211563316931 4818694161235817344975397)
                  ·
                    refine ⟨903505155231715752182887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818694161235817344975397 903505155231715752182887)
                    ·
                      rfl

theorem cell23_5278710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_5278710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278710 prefixEnd_5278710 := by exact prefixLift 5278710
  have htrace : WordTrace (prefixWord ++ tailWord_5278710) baseStart_5278710 baseEnd_5278710 := by
    simpa [prefixWord, tailWord_5278710, baseEnd_5278710] using wordTrace_append hprefix tailTrace_5278710
  have hstable : (prefixWord ++ tailWord_5278710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278710).length < 2 ^ (prefixWord ++ tailWord_5278710).sum := by decide
  have hdescent : baseEnd_5278710 < baseStart_5278710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278739 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4]
def baseStart_5278739 : Nat := 118140960795 + 5278739 * 2 ^ 59
def prefixEnd_5278739 : Nat := 4983230072969 + 3 ^ 40 * 5278739 * 2
def baseEnd_5278739 : Nat := 2710530356634127643086027

theorem tailTrace_5278739 : CollatzResearch.WordTrace tailWord_5278739 prefixEnd_5278739 2710530356634127643086027 := by
  unfold tailWord_5278739
  simp only [CollatzResearch.WordTrace]
  refine ⟨192531428423037614691295271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128354285615358409794196847 192531428423037614691295271)
  ·
    refine ⟨288797142634556422036942907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192531428423037614691295271 288797142634556422036942907)
    ·
      refine ⟨433195713951834633055414361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288797142634556422036942907 433195713951834633055414361)
      ·
        refine ⟨324896785463875974791560771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433195713951834633055414361 324896785463875974791560771)
        ·
          refine ⟨487345178195813962187341157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324896785463875974791560771 487345178195813962187341157)
          ·
            refine ⟨91377220911715117910126467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487345178195813962187341157 91377220911715117910126467)
            ·
              refine ⟨137065831367572676865189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91377220911715117910126467 137065831367572676865189701)
              ·
                refine ⟨25699843381419876912223069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137065831367572676865189701 25699843381419876912223069)
                ·
                  refine ⟨9637441268032453842083651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25699843381419876912223069 9637441268032453842083651)
                  ·
                    refine ⟨14456161902048680763125477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9637441268032453842083651 14456161902048680763125477)
                    ·
                      refine ⟨2710530356634127643086027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14456161902048680763125477 2710530356634127643086027)
                      ·
                        rfl

theorem cell23_5278739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_5278739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278739 prefixEnd_5278739 := by exact prefixLift 5278739
  have htrace : WordTrace (prefixWord ++ tailWord_5278739) baseStart_5278739 baseEnd_5278739 := by
    simpa [prefixWord, tailWord_5278739, baseEnd_5278739] using wordTrace_append hprefix tailTrace_5278739
  have hstable : (prefixWord ++ tailWord_5278739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278739).length < 2 ^ (prefixWord ++ tailWord_5278739).sum := by decide
  have hdescent : baseEnd_5278739 < baseStart_5278739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278753 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_5278753 : Nat := 118140960795 + 5278753 * 2 ^ 59
def prefixEnd_5278753 : Nat := 4983230072969 + 3 ^ 40 * 5278753 * 2
def baseEnd_5278753 : Nat := 903512515121096862770321

theorem tailTrace_5278753 : CollatzResearch.WordTrace tailWord_5278753 prefixEnd_5278753 903512515121096862770321 := by
  unfold tailWord_5278753
  simp only [CollatzResearch.WordTrace]
  refine ⟨192531939044986895082304913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128354626029991263388203275 192531939044986895082304913)
  ·
    refine ⟨144398954283740171311728685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192531939044986895082304913 144398954283740171311728685)
    ·
      refine ⟨54149607856402564241898257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144398954283740171311728685 54149607856402564241898257)
      ·
        refine ⟨40612205892301923181423693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54149607856402564241898257 40612205892301923181423693)
        ·
          refine ⟨15229577209613221193033885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40612205892301923181423693 15229577209613221193033885)
          ·
            refine ⟨5711091453604957947387707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15229577209613221193033885 5711091453604957947387707)
            ·
              refine ⟨8566637180407436921081561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711091453604957947387707 8566637180407436921081561)
              ·
                refine ⟨6424977885305577690811171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8566637180407436921081561 6424977885305577690811171)
                ·
                  refine ⟨9637466827958366536216757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424977885305577690811171 9637466827958366536216757)
                  ·
                    refine ⟨903512515121096862770321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9637466827958366536216757 903512515121096862770321)
                    ·
                      rfl

theorem cell23_5278753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_5278753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278753 prefixEnd_5278753 := by exact prefixLift 5278753
  have htrace : WordTrace (prefixWord ++ tailWord_5278753) baseStart_5278753 baseEnd_5278753 := by
    simpa [prefixWord, tailWord_5278753, baseEnd_5278753] using wordTrace_append hprefix tailTrace_5278753
  have hstable : (prefixWord ++ tailWord_5278753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278753).length < 2 ^ (prefixWord ++ tailWord_5278753).sum := by decide
  have hdescent : baseEnd_5278753 < baseStart_5278753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278766 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5278766 : Nat := 118140960795 + 5278766 * 2 ^ 59
def prefixEnd_5278766 : Nat := 4983230072969 + 3 ^ 40 * 5278766 * 2
def baseEnd_5278766 : Nat := 903514740203933012482801

theorem tailTrace_5278766 : CollatzResearch.WordTrace tailWord_5278766 prefixEnd_5278766 903514740203933012482801 := by
  unfold tailWord_5278766
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066551649242474787816019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128354942129293198868352101 24066551649242474787816019)
  ·
    refine ⟨36099827473863712181724029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24066551649242474787816019 36099827473863712181724029)
    ·
      refine ⟨13537435302698892068146511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36099827473863712181724029 13537435302698892068146511)
      ·
        refine ⟨20306152954048338102219767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13537435302698892068146511 20306152954048338102219767)
        ·
          refine ⟨30459229431072507153329651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20306152954048338102219767 30459229431072507153329651)
          ·
            refine ⟨45688844146608760729994477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30459229431072507153329651 45688844146608760729994477)
            ·
              refine ⟨17133316554978285273747929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45688844146608760729994477 17133316554978285273747929)
              ·
                refine ⟨12849987416233713955310947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17133316554978285273747929 12849987416233713955310947)
                ·
                  refine ⟨19274981124350570932966421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12849987416233713955310947 19274981124350570932966421)
                  ·
                    refine ⟨903514740203933012482801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19274981124350570932966421 903514740203933012482801)
                    ·
                      rfl

theorem cell23_5278766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5278766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278766 prefixEnd_5278766 := by exact prefixLift 5278766
  have htrace : WordTrace (prefixWord ++ tailWord_5278766) baseStart_5278766 baseEnd_5278766 := by
    simpa [prefixWord, tailWord_5278766, baseEnd_5278766] using wordTrace_append hprefix tailTrace_5278766
  have hstable : (prefixWord ++ tailWord_5278766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278766).length < 2 ^ (prefixWord ++ tailWord_5278766).sum := by decide
  have hdescent : baseEnd_5278766 < baseStart_5278766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278776 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_5278776 : Nat := 118140960795 + 5278776 * 2 ^ 59
def prefixEnd_5278776 : Nat := 4983230072969 + 3 ^ 40 * 5278776 * 2
def baseEnd_5278776 : Nat := 2710549355418343998323357

theorem tailTrace_5278776 : CollatzResearch.WordTrace tailWord_5278776 prefixEnd_5278776 2710549355418343998323357 := by
  unfold tailWord_5278776
  simp only [CollatzResearch.WordTrace]
  refine ⟨96266388961951785005196091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128355185282602380006928121 96266388961951785005196091)
  ·
    refine ⟨144399583442927677507794137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96266388961951785005196091 144399583442927677507794137)
    ·
      refine ⟨108299687582195758130845603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144399583442927677507794137 108299687582195758130845603)
      ·
        refine ⟨162449531373293637196268405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108299687582195758130845603 162449531373293637196268405)
        ·
          refine ⟨15229643566246278487150163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162449531373293637196268405 15229643566246278487150163)
          ·
            refine ⟨22844465349369417730725245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15229643566246278487150163 22844465349369417730725245)
            ·
              refine ⟨8566674506013531649021967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22844465349369417730725245 8566674506013531649021967)
              ·
                refine ⟨12850011759020297473532951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8566674506013531649021967 12850011759020297473532951)
                ·
                  refine ⟨19275017638530446210299427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12850011759020297473532951 19275017638530446210299427)
                  ·
                    refine ⟨28912526457795669315449141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19275017638530446210299427 28912526457795669315449141)
                    ·
                      refine ⟨2710549355418343998323357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28912526457795669315449141 2710549355418343998323357)
                      ·
                        rfl

theorem cell23_5278776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_5278776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278776 prefixEnd_5278776 := by exact prefixLift 5278776
  have htrace : WordTrace (prefixWord ++ tailWord_5278776) baseStart_5278776 baseEnd_5278776 := by
    simpa [prefixWord, tailWord_5278776, baseEnd_5278776] using wordTrace_append hprefix tailTrace_5278776
  have hstable : (prefixWord ++ tailWord_5278776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278776).length < 2 ^ (prefixWord ++ tailWord_5278776).sum := by decide
  have hdescent : baseEnd_5278776 < baseStart_5278776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278819 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5278819 : Nat := 118140960795 + 5278819 * 2 ^ 59
def prefixEnd_5278819 : Nat := 4983230072969 + 3 ^ 40 * 5278819 * 2
def baseEnd_5278819 : Nat := 2710571435086487330085659

theorem tailTrace_5278819 : CollatzResearch.WordTrace tailWord_5278819 prefixEnd_5278819 2710571435086487330085659 := by
  unfold tailWord_5278819
  simp only [CollatzResearch.WordTrace]
  refine ⟨192534346262747788354207511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128356230841831858902805007 192534346262747788354207511)
  ·
    refine ⟨288801519394121682531311267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192534346262747788354207511 288801519394121682531311267)
    ·
      refine ⟨433202279091182523796966901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288801519394121682531311267 433202279091182523796966901)
      ·
        refine ⟨40612713664798361605965647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 433202279091182523796966901 40612713664798361605965647)
        ·
          refine ⟨60919070497197542408948471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40612713664798361605965647 60919070497197542408948471)
          ·
            refine ⟨91378605745796313613422707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60919070497197542408948471 91378605745796313613422707)
            ·
              refine ⟨137067908618694470420134061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91378605745796313613422707 137067908618694470420134061)
              ·
                refine ⟨51400465732010426407550273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137067908618694470420134061 51400465732010426407550273)
                ·
                  refine ⟨38550349299007819805662705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51400465732010426407550273 38550349299007819805662705)
                  ·
                    refine ⟨28912761974255864854247029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38550349299007819805662705 28912761974255864854247029)
                    ·
                      refine ⟨2710571435086487330085659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28912761974255864854247029 2710571435086487330085659)
                      ·
                        rfl

theorem cell23_5278819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5278819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278819 prefixEnd_5278819 := by exact prefixLift 5278819
  have htrace : WordTrace (prefixWord ++ tailWord_5278819) baseStart_5278819 baseEnd_5278819 := by
    simpa [prefixWord, tailWord_5278819, baseEnd_5278819] using wordTrace_append hprefix tailTrace_5278819
  have hstable : (prefixWord ++ tailWord_5278819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278819).length < 2 ^ (prefixWord ++ tailWord_5278819).sum := by decide
  have hdescent : baseEnd_5278819 < baseStart_5278819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278824 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5278824 : Nat := 118140960795 + 5278824 * 2 ^ 59
def prefixEnd_5278824 : Nat := 4983230072969 + 3 ^ 40 * 5278824 * 2
def baseEnd_5278824 : Nat := 2710574002489759810523137

theorem tailTrace_5278824 : CollatzResearch.WordTrace tailWord_5278824 prefixEnd_5278824 2710574002489759810523137 := by
  unfold tailWord_5278824
  simp only [CollatzResearch.WordTrace]
  refine ⟨96267264313864837104069763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128356352418486449472093017 96267264313864837104069763)
  ·
    refine ⟨144400896470797255656104645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96267264313864837104069763 144400896470797255656104645)
    ·
      refine ⟨27075168088274485435519621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144400896470797255656104645 27075168088274485435519621)
      ·
        refine ⟨5076594016551466019159929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27075168088274485435519621 5076594016551466019159929)
        ·
          refine ⟨3807445512413599514369947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5076594016551466019159929 3807445512413599514369947)
          ·
            refine ⟨5711168268620399271554921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807445512413599514369947 5711168268620399271554921)
            ·
              refine ⟨4283376201465299453666191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711168268620399271554921 4283376201465299453666191)
              ·
                refine ⟨6425064302197949180499287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283376201465299453666191 6425064302197949180499287)
                ·
                  refine ⟨9637596453296923770748931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425064302197949180499287 9637596453296923770748931)
                  ·
                    refine ⟨14456394679945385656123397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9637596453296923770748931 14456394679945385656123397)
                    ·
                      refine ⟨2710574002489759810523137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14456394679945385656123397 2710574002489759810523137)
                      ·
                        rfl

theorem cell23_5278824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5278824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278824 prefixEnd_5278824 := by exact prefixLift 5278824
  have htrace : WordTrace (prefixWord ++ tailWord_5278824) baseStart_5278824 baseEnd_5278824 := by
    simpa [prefixWord, tailWord_5278824, baseEnd_5278824] using wordTrace_append hprefix tailTrace_5278824
  have hstable : (prefixWord ++ tailWord_5278824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278824).length < 2 ^ (prefixWord ++ tailWord_5278824).sum := by decide
  have hdescent : baseEnd_5278824 < baseStart_5278824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278839 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 6]
def baseStart_5278839 : Nat := 118140960795 + 5278839 * 2 ^ 59
def prefixEnd_5278839 : Nat := 4983230072969 + 3 ^ 40 * 5278839 * 2
def baseEnd_5278839 : Nat := 903527234899859083945189

theorem tailTrace_5278839 : CollatzResearch.WordTrace tailWord_5278839 prefixEnd_5278839 903527234899859083945189 := by
  unfold tailWord_5278839
  simp only [CollatzResearch.WordTrace]
  refine ⟨192535075722675331769935571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128356717148450221179957047 192535075722675331769935571)
  ·
    refine ⟨288802613584012997654903357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192535075722675331769935571 288802613584012997654903357)
    ·
      refine ⟨108300980094004874120588759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288802613584012997654903357 108300980094004874120588759)
      ·
        refine ⟨162451470141007311180883139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108300980094004874120588759 162451470141007311180883139)
        ·
          refine ⟨243677205211510966771324709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162451470141007311180883139 243677205211510966771324709)
          ·
            refine ⟨45689475977158306269623383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243677205211510966771324709 45689475977158306269623383)
            ·
              refine ⟨68534213965737459404435075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45689475977158306269623383 68534213965737459404435075)
              ·
                refine ⟨102801320948606189106652613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68534213965737459404435075 102801320948606189106652613)
                ·
                  refine ⟨19275247677863660457497365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102801320948606189106652613 19275247677863660457497365)
                  ·
                    refine ⟨903527234899859083945189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19275247677863660457497365 903527234899859083945189)
                    ·
                      rfl

theorem cell23_5278839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_5278839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278839 prefixEnd_5278839 := by exact prefixLift 5278839
  have htrace : WordTrace (prefixWord ++ tailWord_5278839) baseStart_5278839 baseEnd_5278839 := by
    simpa [prefixWord, tailWord_5278839, baseEnd_5278839] using wordTrace_append hprefix tailTrace_5278839
  have hstable : (prefixWord ++ tailWord_5278839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278839).length < 2 ^ (prefixWord ++ tailWord_5278839).sum := by decide
  have hdescent : baseEnd_5278839 < baseStart_5278839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278869 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 9]
def baseStart_5278869 : Nat := 118140960795 + 5278869 * 2 ^ 59
def prefixEnd_5278869 : Nat := 4983230072969 + 3 ^ 40 * 5278869 * 2
def baseEnd_5278869 : Nat := 301177456568801348273381

theorem tailTrace_5278869 : CollatzResearch.WordTrace tailWord_5278869 prefixEnd_5278869 301177456568801348273381 := by
  unfold tailWord_5278869
  simp only [CollatzResearch.WordTrace]
  refine ⟨192536169912566646893527661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128357446608377764595685107 192536169912566646893527661)
  ·
    refine ⟨72201063717212492585072873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192536169912566646893527661 72201063717212492585072873)
    ·
      refine ⟨54150797787909369438804655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72201063717212492585072873 54150797787909369438804655)
      ·
        refine ⟨81226196681864054158206983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54150797787909369438804655 81226196681864054158206983)
        ·
          refine ⟨121839295022796081237310475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81226196681864054158206983 121839295022796081237310475)
          ·
            refine ⟨182758942534194121855965713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121839295022796081237310475 182758942534194121855965713)
            ·
              refine ⟨137069206900645591391974285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182758942534194121855965713 137069206900645591391974285)
              ·
                refine ⟨51400952587742096771990357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137069206900645591391974285 51400952587742096771990357)
                ·
                  refine ⟨301177456568801348273381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51400952587742096771990357 301177456568801348273381)
                  ·
                    rfl

theorem cell23_5278869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_5278869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278869 prefixEnd_5278869 := by exact prefixLift 5278869
  have htrace : WordTrace (prefixWord ++ tailWord_5278869) baseStart_5278869 baseEnd_5278869 := by
    simpa [prefixWord, tailWord_5278869, baseEnd_5278869] using wordTrace_append hprefix tailTrace_5278869
  have hstable : (prefixWord ++ tailWord_5278869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278869).length < 2 ^ (prefixWord ++ tailWord_5278869).sum := by decide
  have hdescent : baseEnd_5278869 < baseStart_5278869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278918 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5278918 : Nat := 118140960795 + 5278918 * 2 ^ 59
def prefixEnd_5278918 : Nat := 4983230072969 + 3 ^ 40 * 5278918 * 2
def baseEnd_5278918 : Nat := 2710622269671282442747705

theorem tailTrace_5278918 : CollatzResearch.WordTrace tailWord_5278918 prefixEnd_5278918 2710622269671282442747705 := by
  unfold tailWord_5278918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016811159043410258189419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128358638059592752174707605 6016811159043410258189419)
  ·
    refine ⟨9025216738565115387284129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6016811159043410258189419 9025216738565115387284129)
    ·
      refine ⟨6768912553923836540463097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9025216738565115387284129 6768912553923836540463097)
      ·
        refine ⟨5076684415442877405347323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6768912553923836540463097 5076684415442877405347323)
        ·
          refine ⟨7615026623164316108020985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076684415442877405347323 7615026623164316108020985)
          ·
            refine ⟨5711269967373237081015739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7615026623164316108020985 5711269967373237081015739)
            ·
              refine ⟨8566904951059855621523609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711269967373237081015739 8566904951059855621523609)
              ·
                refine ⟨6425178713294891716142707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8566904951059855621523609 6425178713294891716142707)
                ·
                  refine ⟨9637768069942337574214061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425178713294891716142707 9637768069942337574214061)
                  ·
                    refine ⟨3614163026228376590330273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9637768069942337574214061 3614163026228376590330273)
                    ·
                      refine ⟨2710622269671282442747705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614163026228376590330273 2710622269671282442747705)
                      ·
                        rfl

theorem cell23_5278918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5278918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278918 prefixEnd_5278918 := by exact prefixLift 5278918
  have htrace : WordTrace (prefixWord ++ tailWord_5278918) baseStart_5278918 baseEnd_5278918 := by
    simpa [prefixWord, tailWord_5278918, baseEnd_5278918] using wordTrace_append hprefix tailTrace_5278918
  have hstable : (prefixWord ++ tailWord_5278918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278918).length < 2 ^ (prefixWord ++ tailWord_5278918).sum := by decide
  have hdescent : baseEnd_5278918 < baseStart_5278918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278933 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_5278933 : Nat := 118140960795 + 5278933 * 2 ^ 59
def prefixEnd_5278933 : Nat := 4983230072969 + 3 ^ 40 * 5278933 * 2
def baseEnd_5278933 : Nat := 903543323960366628020045

theorem tailTrace_5278933 : CollatzResearch.WordTrace tailWord_5278933 prefixEnd_5278933 903543323960366628020045 := by
  unfold tailWord_5278933
  simp only [CollatzResearch.WordTrace]
  refine ⟨192538504184334785823857453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128359002789556523882571635 192538504184334785823857453)
  ·
    refine ⟨72201939069125544683946545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192538504184334785823857453 72201939069125544683946545)
    ·
      refine ⟨54151454301844158512959909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72201939069125544683946545 54151454301844158512959909)
      ·
        refine ⟨10153397681595779721179983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54151454301844158512959909 10153397681595779721179983)
        ·
          refine ⟨15230096522393669581769975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153397681595779721179983 15230096522393669581769975)
          ·
            refine ⟨22845144783590504372654963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15230096522393669581769975 22845144783590504372654963)
            ·
              refine ⟨34267717175385756558982445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22845144783590504372654963 34267717175385756558982445)
              ·
                refine ⟨12850393940769658709618417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34267717175385756558982445 12850393940769658709618417)
                ·
                  refine ⟨9637795455577244032213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12850393940769658709618417 9637795455577244032213813)
                  ·
                    refine ⟨903543323960366628020045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9637795455577244032213813 903543323960366628020045)
                    ·
                      rfl

theorem cell23_5278933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_5278933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278933 prefixEnd_5278933 := by exact prefixLift 5278933
  have htrace : WordTrace (prefixWord ++ tailWord_5278933) baseStart_5278933 baseEnd_5278933 := by
    simpa [prefixWord, tailWord_5278933, baseEnd_5278933] using wordTrace_append hprefix tailTrace_5278933
  have hstable : (prefixWord ++ tailWord_5278933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278933).length < 2 ^ (prefixWord ++ tailWord_5278933).sum := by decide
  have hdescent : baseEnd_5278933 < baseStart_5278933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278964 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5278964 : Nat := 118140960795 + 5278964 * 2 ^ 59
def prefixEnd_5278964 : Nat := 4983230072969 + 3 ^ 40 * 5278964 * 2
def baseEnd_5278964 : Nat := 2710645889781389262772493

theorem tailTrace_5278964 : CollatzResearch.WordTrace tailWord_5278964 prefixEnd_5278964 2710645889781389262772493 := by
  unfold tailWord_5278964
  simp only [CollatzResearch.WordTrace]
  refine ⟨96269817423611239059117973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128359756564814985412157297 96269817423611239059117973)
  ·
    refine ⟨4512647691731776830896155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96269817423611239059117973 4512647691731776830896155)
    ·
      refine ⟨6768971537597665246344233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512647691731776830896155 6768971537597665246344233)
      ·
        refine ⟨5076728653198248934758175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6768971537597665246344233 5076728653198248934758175)
        ·
          refine ⟨7615092979797373402137263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076728653198248934758175 7615092979797373402137263)
          ·
            refine ⟨11422639469696060103205895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615092979797373402137263 11422639469696060103205895)
            ·
              refine ⟨17133959204544090154808843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11422639469696060103205895 17133959204544090154808843)
              ·
                refine ⟨25700938806816135232213265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17133959204544090154808843 25700938806816135232213265)
                ·
                  refine ⟨19275704105112101424159949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25700938806816135232213265 19275704105112101424159949)
                  ·
                    refine ⟨7228389039417038034059981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19275704105112101424159949 7228389039417038034059981)
                    ·
                      refine ⟨2710645889781389262772493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228389039417038034059981 2710645889781389262772493)
                      ·
                        rfl

theorem cell23_5278964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5278964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278964 prefixEnd_5278964 := by exact prefixLift 5278964
  have htrace : WordTrace (prefixWord ++ tailWord_5278964) baseStart_5278964 baseEnd_5278964 := by
    simpa [prefixWord, tailWord_5278964, baseEnd_5278964] using wordTrace_append hprefix tailTrace_5278964
  have hstable : (prefixWord ++ tailWord_5278964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278964).length < 2 ^ (prefixWord ++ tailWord_5278964).sum := by decide
  have hdescent : baseEnd_5278964 < baseStart_5278964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278980 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_5278980 : Nat := 118140960795 + 5278980 * 2 ^ 59
def prefixEnd_5278980 : Nat := 4983230072969 + 3 ^ 40 * 5278980 * 2
def baseEnd_5278980 : Nat := 903551368490620400057473

theorem tailTrace_5278980 : CollatzResearch.WordTrace tailWord_5278980 prefixEnd_5278980 903551368490620400057473 := by
  unfold tailWord_5278980
  simp only [CollatzResearch.WordTrace]
  refine ⟨96270109207582256425409197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128360145610109675233878929 96270109207582256425409197)
  ·
    refine ⟨36101290952843346159528449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96270109207582256425409197 36101290952843346159528449)
    ·
      refine ⟨27075968214632509619646337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36101290952843346159528449 27075968214632509619646337)
      ·
        refine ⟨20306976160974382214734753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27075968214632509619646337 20306976160974382214734753)
        ·
          refine ⟨15230232120730786661051065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20306976160974382214734753 15230232120730786661051065)
          ·
            refine ⟨11422674090548089995788299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15230232120730786661051065 11422674090548089995788299)
            ·
              refine ⟨17134011135822134993682449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11422674090548089995788299 17134011135822134993682449)
              ·
                refine ⟨12850508351866601245261837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17134011135822134993682449 12850508351866601245261837)
                ·
                  refine ⟨4818940631949975466973189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12850508351866601245261837 4818940631949975466973189)
                  ·
                    refine ⟨903551368490620400057473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818940631949975466973189 903551368490620400057473)
                    ·
                      rfl

theorem cell23_5278980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_5278980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278980 prefixEnd_5278980 := by exact prefixLift 5278980
  have htrace : WordTrace (prefixWord ++ tailWord_5278980) baseStart_5278980 baseEnd_5278980 := by
    simpa [prefixWord, tailWord_5278980, baseEnd_5278980] using wordTrace_append hprefix tailTrace_5278980
  have hstable : (prefixWord ++ tailWord_5278980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278980).length < 2 ^ (prefixWord ++ tailWord_5278980).sum := by decide
  have hdescent : baseEnd_5278980 < baseStart_5278980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5278990 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5278990 : Nat := 118140960795 + 5278990 * 2 ^ 59
def prefixEnd_5278990 : Nat := 4983230072969 + 3 ^ 40 * 5278990 * 2
def baseEnd_5278990 : Nat := 2710659240278406161047373

theorem tailTrace_5278990 : CollatzResearch.WordTrace tailWord_5278990 prefixEnd_5278990 2710659240278406161047373 := by
  unfold tailWord_5278990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067572893141035569835303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128360388763418856372454949 24067572893141035569835303)
  ·
    refine ⟨36101359339711553354752955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24067572893141035569835303 36101359339711553354752955)
    ·
      refine ⟨54152039009567330032129433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36101359339711553354752955 54152039009567330032129433)
      ·
        refine ⟨40614029257175497524097075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54152039009567330032129433 40614029257175497524097075)
        ·
          refine ⟨60921043885763246286145613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40614029257175497524097075 60921043885763246286145613)
          ·
            refine ⟨22845391457161217357304605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60921043885763246286145613 22845391457161217357304605)
            ·
              refine ⟨8567021796435456508989227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22845391457161217357304605 8567021796435456508989227)
              ·
                refine ⟨12850532694653184763483841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567021796435456508989227 12850532694653184763483841)
                ·
                  refine ⟨9637899520989888572612881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12850532694653184763483841 9637899520989888572612881)
                  ·
                    refine ⟨7228424640742416429459661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9637899520989888572612881 7228424640742416429459661)
                    ·
                      refine ⟨2710659240278406161047373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228424640742416429459661 2710659240278406161047373)
                      ·
                        rfl

theorem cell23_5278990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5278990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5278990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5278990 prefixEnd_5278990 := by exact prefixLift 5278990
  have htrace : WordTrace (prefixWord ++ tailWord_5278990) baseStart_5278990 baseEnd_5278990 := by
    simpa [prefixWord, tailWord_5278990, baseEnd_5278990] using wordTrace_append hprefix tailTrace_5278990
  have hstable : (prefixWord ++ tailWord_5278990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5278990).length < 2 ^ (prefixWord ++ tailWord_5278990).sum := by decide
  have hdescent : baseEnd_5278990 < baseStart_5278990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5278990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279003 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 3]
def baseStart_5279003 : Nat := 118140960795 + 5279003 * 2 ^ 59
def prefixEnd_5279003 : Nat := 4983230072969 + 3 ^ 40 * 5279003 * 2
def baseEnd_5279003 : Nat := 2710665915526914610184813

theorem tailTrace_5279003 : CollatzResearch.WordTrace tailWord_5279003 prefixEnd_5279003 2710665915526914610184813 := by
  unfold tailWord_5279003
  simp only [CollatzResearch.WordTrace]
  refine ⟨192541057294081187778905663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128360704862720791852603775 192541057294081187778905663)
  ·
    refine ⟨288811585941121781668358495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192541057294081187778905663 288811585941121781668358495)
    ·
      refine ⟨433217378911682672502537743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288811585941121781668358495 433217378911682672502537743)
      ·
        refine ⟨649826068367524008753806615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433217378911682672502537743 649826068367524008753806615)
        ·
          refine ⟨974739102551286013130709923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649826068367524008753806615 974739102551286013130709923)
          ·
            refine ⟨1462108653826929019696064885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974739102551286013130709923 1462108653826929019696064885)
            ·
              refine ⟨137072686296274595596506083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1462108653826929019696064885 137072686296274595596506083)
              ·
                refine ⟨205609029444411893394759125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137072686296274595596506083 205609029444411893394759125)
                ·
                  refine ⟨4818961627603403751439667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 205609029444411893394759125 4818961627603403751439667)
                  ·
                    refine ⟨7228442441405105627159501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4818961627603403751439667 7228442441405105627159501)
                    ·
                      refine ⟨2710665915526914610184813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228442441405105627159501 2710665915526914610184813)
                      ·
                        rfl

theorem cell23_5279003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 3].length) (baseStart_5279003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279003 prefixEnd_5279003 := by exact prefixLift 5279003
  have htrace : WordTrace (prefixWord ++ tailWord_5279003) baseStart_5279003 baseEnd_5279003 := by
    simpa [prefixWord, tailWord_5279003, baseEnd_5279003] using wordTrace_append hprefix tailTrace_5279003
  have hstable : (prefixWord ++ tailWord_5279003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279003).length < 2 ^ (prefixWord ++ tailWord_5279003).sum := by decide
  have hdescent : baseEnd_5279003 < baseStart_5279003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279043 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 8, 2]
def baseStart_5279043 : Nat := 118140960795 + 5279043 * 2 ^ 59
def prefixEnd_5279043 : Nat := 4983230072969 + 3 ^ 40 * 5279043 * 2
def baseEnd_5279043 : Nat := 2710686454753094453684629

theorem tailTrace_5279043 : CollatzResearch.WordTrace tailWord_5279043 prefixEnd_5279043 2710686454753094453684629 := by
  unfold tailWord_5279043
  simp only [CollatzResearch.WordTrace]
  refine ⟨192542516213936274610361783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128361677475957516406907855 192542516213936274610361783)
  ·
    refine ⟨288813774320904411915542675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192542516213936274610361783 288813774320904411915542675)
    ·
      refine ⟨433220661481356617873314013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288813774320904411915542675 433220661481356617873314013)
      ·
        refine ⟨162457748055508731702492755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433220661481356617873314013 162457748055508731702492755)
        ·
          refine ⟨243686622083263097553739133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162457748055508731702492755 243686622083263097553739133)
          ·
            refine ⟨91382483281223661582652175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243686622083263097553739133 91382483281223661582652175)
            ·
              refine ⟨137073724921835492373978263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91382483281223661582652175 137073724921835492373978263)
              ·
                refine ⟨205610587382753238560967395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137073724921835492373978263 205610587382753238560967395)
                ·
                  refine ⟨308415881074129857841451093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205610587382753238560967395 308415881074129857841451093)
                  ·
                    refine ⟨3614248606337459271579505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 308415881074129857841451093 3614248606337459271579505)
                    ·
                      refine ⟨2710686454753094453684629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614248606337459271579505 2710686454753094453684629)
                      ·
                        rfl

theorem cell23_5279043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_5279043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279043 prefixEnd_5279043 := by exact prefixLift 5279043
  have htrace : WordTrace (prefixWord ++ tailWord_5279043) baseStart_5279043 baseEnd_5279043 := by
    simpa [prefixWord, tailWord_5279043, baseEnd_5279043] using wordTrace_append hprefix tailTrace_5279043
  have hstable : (prefixWord ++ tailWord_5279043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279043).length < 2 ^ (prefixWord ++ tailWord_5279043).sum := by decide
  have hdescent : baseEnd_5279043 < baseStart_5279043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279060 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_5279060 : Nat := 118140960795 + 5279060 * 2 ^ 59
def prefixEnd_5279060 : Nat := 4983230072969 + 3 ^ 40 * 5279060 * 2
def baseEnd_5279060 : Nat := 2710695183924220887172051

theorem tailTrace_5279060 : CollatzResearch.WordTrace tailWord_5279060 prefixEnd_5279060 2710695183924220887172051 := by
  unfold tailWord_5279060
  simp only [CollatzResearch.WordTrace]
  refine ⟨96271568127437343256865317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128362090836583124342487089 96271568127437343256865317)
  ·
    refine ⟨18050919023894501860662247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96271568127437343256865317 18050919023894501860662247)
    ·
      refine ⟨27076378535841752790993371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18050919023894501860662247 27076378535841752790993371)
      ·
        refine ⟨40614567803762629186490057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27076378535841752790993371 40614567803762629186490057)
        ·
          refine ⟨30460925852821971889867543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40614567803762629186490057 30460925852821971889867543)
          ·
            refine ⟨45691388779232957834801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30460925852821971889867543 45691388779232957834801315)
            ·
              refine ⟨68537083168849436752201973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45691388779232957834801315 68537083168849436752201973)
              ·
                refine ⟨6425351547079634695518935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68537083168849436752201973 6425351547079634695518935)
                ·
                  refine ⟨9638027320619452043278403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425351547079634695518935 9638027320619452043278403)
                  ·
                    refine ⟨14457040980929178064917605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9638027320619452043278403 14457040980929178064917605)
                    ·
                      refine ⟨2710695183924220887172051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14457040980929178064917605 2710695183924220887172051)
                      ·
                        rfl

theorem cell23_5279060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_5279060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279060 prefixEnd_5279060 := by exact prefixLift 5279060
  have htrace : WordTrace (prefixWord ++ tailWord_5279060) baseStart_5279060 baseEnd_5279060 := by
    simpa [prefixWord, tailWord_5279060, baseEnd_5279060] using wordTrace_append hprefix tailTrace_5279060
  have hstable : (prefixWord ++ tailWord_5279060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279060).length < 2 ^ (prefixWord ++ tailWord_5279060).sum := by decide
  have hdescent : baseEnd_5279060 < baseStart_5279060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279063 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5279063 : Nat := 118140960795 + 5279063 * 2 ^ 59
def prefixEnd_5279063 : Nat := 4983230072969 + 3 ^ 40 * 5279063 * 2
def baseEnd_5279063 : Nat := 2710696724366184375434537

theorem tailTrace_5279063 : CollatzResearch.WordTrace tailWord_5279063 prefixEnd_5279063 2710696724366184375434537 := by
  unfold tailWord_5279063
  simp only [CollatzResearch.WordTrace]
  refine ⟨192543245673863818026089843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128362163782575878684059895 192543245673863818026089843)
  ·
    refine ⟨288814868510795727039134765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192543245673863818026089843 288814868510795727039134765)
    ·
      refine ⟨108305575691548397639675537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288814868510795727039134765 108305575691548397639675537)
      ·
        refine ⟨81229181768661298229756653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108305575691548397639675537 81229181768661298229756653)
        ·
          refine ⟨30460943163247986836158745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81229181768661298229756653 30460943163247986836158745)
          ·
            refine ⟨22845707372435990127119059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30460943163247986836158745 22845707372435990127119059)
            ·
              refine ⟨34268561058653985190678589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22845707372435990127119059 34268561058653985190678589)
              ·
                refine ⟨12850710396995244446504471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34268561058653985190678589 12850710396995244446504471)
                ·
                  refine ⟨19276065595492866669756707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12850710396995244446504471 19276065595492866669756707)
                  ·
                    refine ⟨28914098393239300004635061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19276065595492866669756707 28914098393239300004635061)
                    ·
                      refine ⟨2710696724366184375434537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28914098393239300004635061 2710696724366184375434537)
                      ·
                        rfl

theorem cell23_5279063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5279063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279063 prefixEnd_5279063 := by exact prefixLift 5279063
  have htrace : WordTrace (prefixWord ++ tailWord_5279063) baseStart_5279063 baseEnd_5279063 := by
    simpa [prefixWord, tailWord_5279063, baseEnd_5279063] using wordTrace_append hprefix tailTrace_5279063
  have hstable : (prefixWord ++ tailWord_5279063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279063).length < 2 ^ (prefixWord ++ tailWord_5279063).sum := by decide
  have hdescent : baseEnd_5279063 < baseStart_5279063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279066 : List Nat := [3, 1, 1, 2, 1, 2, 13]
def baseStart_5279066 : Nat := 118140960795 + 5279066 * 2 ^ 59
def prefixEnd_5279066 : Nat := 4983230072969 + 3 ^ 40 * 5279066 * 2
def baseEnd_5279066 : Nat := 33465410676643800786383

theorem tailTrace_5279066 : CollatzResearch.WordTrace tailWord_5279066 prefixEnd_5279066 33465410676643800786383 := by
  unfold tailWord_5279066
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135838773213237384612263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128362236728568633025632701 48135838773213237384612263)
  ·
    refine ⟨72203758159819856076918395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48135838773213237384612263 72203758159819856076918395)
    ·
      refine ⟨108305637239729784115377593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72203758159819856076918395 108305637239729784115377593)
      ·
        refine ⟨81229227929797338086533195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108305637239729784115377593 81229227929797338086533195)
        ·
          refine ⟨121843841894696007129799793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81229227929797338086533195 121843841894696007129799793)
          ·
            refine ⟨91382881421022005347349845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121843841894696007129799793 91382881421022005347349845)
            ·
              refine ⟨33465410676643800786383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 91382881421022005347349845 33465410676643800786383)
              ·
                rfl

theorem cell23_5279066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 13].length) (baseStart_5279066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279066 prefixEnd_5279066 := by exact prefixLift 5279066
  have htrace : WordTrace (prefixWord ++ tailWord_5279066) baseStart_5279066 baseEnd_5279066 := by
    simpa [prefixWord, tailWord_5279066, baseEnd_5279066] using wordTrace_append hprefix tailTrace_5279066
  have hstable : (prefixWord ++ tailWord_5279066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279066).length < 2 ^ (prefixWord ++ tailWord_5279066).sum := by decide
  have hdescent : baseEnd_5279066 < baseStart_5279066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279134 : List Nat := [4, 3, 1, 2, 3, 1, 1, 8]
def baseStart_5279134 : Nat := 118140960795 + 5279134 * 2 ^ 59
def prefixEnd_5279134 : Nat := 4983230072969 + 3 ^ 40 * 5279134 * 2
def baseEnd_5279134 : Nat := 100397525240468651764693

theorem tailTrace_5279134 : CollatzResearch.WordTrace tailWord_5279134 prefixEnd_5279134 100397525240468651764693 := by
  unfold tailWord_5279134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24068229407075824643990557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128363890171071064767949637 24068229407075824643990557)
  ·
    refine ⟨9025586027653434241496459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24068229407075824643990557 9025586027653434241496459)
    ·
      refine ⟨13538379041480151362244689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9025586027653434241496459 13538379041480151362244689)
      ·
        refine ⟨10153784281110113521683517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13538379041480151362244689 10153784281110113521683517)
        ·
          refine ⟨3807669105416292570631319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10153784281110113521683517 3807669105416292570631319)
          ·
            refine ⟨5711503658124438855946979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807669105416292570631319 5711503658124438855946979)
            ·
              refine ⟨8567255487186658283920469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711503658124438855946979 8567255487186658283920469)
              ·
                refine ⟨100397525240468651764693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8567255487186658283920469 100397525240468651764693)
                ·
                  rfl

theorem cell23_5279134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_5279134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279134 prefixEnd_5279134 := by exact prefixLift 5279134
  have htrace : WordTrace (prefixWord ++ tailWord_5279134) baseStart_5279134 baseEnd_5279134 := by
    simpa [prefixWord, tailWord_5279134, baseEnd_5279134] using wordTrace_append hprefix tailTrace_5279134
  have hstable : (prefixWord ++ tailWord_5279134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279134).length < 2 ^ (prefixWord ++ tailWord_5279134).sum := by decide
  have hdescent : baseEnd_5279134 < baseStart_5279134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279144 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5279144 : Nat := 118140960795 + 5279144 * 2 ^ 59
def prefixEnd_5279144 : Nat := 4983230072969 + 3 ^ 40 * 5279144 * 2
def baseEnd_5279144 : Nat := 2710738316299198558521665

theorem tailTrace_5279144 : CollatzResearch.WordTrace tailWord_5279144 prefixEnd_5279144 2710738316299198558521665 := by
  unfold tailWord_5279144
  simp only [CollatzResearch.WordTrace]
  refine ⟨96273099993285184429894243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128364133324380245906525657 96273099993285184429894243)
  ·
    refine ⟨144409649989927776644841365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96273099993285184429894243 144409649989927776644841365)
    ·
      refine ⟨6769202343277864530226939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144409649989927776644841365 6769202343277864530226939)
      ·
        refine ⟨10153803514916796795340409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769202343277864530226939 10153803514916796795340409)
        ·
          refine ⟨7615352636187597596505307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10153803514916796795340409 7615352636187597596505307)
          ·
            refine ⟨11423028954281396394757961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615352636187597596505307 11423028954281396394757961)
            ·
              refine ⟨8567271715711047296068471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11423028954281396394757961 8567271715711047296068471)
              ·
                refine ⟨12850907573566570944102707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567271715711047296068471 12850907573566570944102707)
                ·
                  refine ⟨19276361360349856416154061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12850907573566570944102707 19276361360349856416154061)
                  ·
                    refine ⟨7228635510131196156057773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19276361360349856416154061 7228635510131196156057773)
                    ·
                      refine ⟨2710738316299198558521665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228635510131196156057773 2710738316299198558521665)
                      ·
                        rfl

theorem cell23_5279144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5279144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279144 prefixEnd_5279144 := by exact prefixLift 5279144
  have htrace : WordTrace (prefixWord ++ tailWord_5279144) baseStart_5279144 baseEnd_5279144 := by
    simpa [prefixWord, tailWord_5279144, baseEnd_5279144] using wordTrace_append hprefix tailTrace_5279144
  have hstable : (prefixWord ++ tailWord_5279144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279144).length < 2 ^ (prefixWord ++ tailWord_5279144).sum := by decide
  have hdescent : baseEnd_5279144 < baseStart_5279144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279180 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5279180 : Nat := 118140960795 + 5279180 * 2 ^ 59
def prefixEnd_5279180 : Nat := 4983230072969 + 3 ^ 40 * 5279180 * 2
def baseEnd_5279180 : Nat := 2710756801602760417671499

theorem tailTrace_5279180 : CollatzResearch.WordTrace tailWord_5279180 prefixEnd_5279180 2710756801602760417671499 := by
  unfold tailWord_5279180
  simp only [CollatzResearch.WordTrace]
  refine ⟨96273756507219973504049497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128365008676293298005399329 96273756507219973504049497)
  ·
    refine ⟨72205317380414980128037123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96273756507219973504049497 72205317380414980128037123)
    ·
      refine ⟨108307976070622470192055685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72205317380414980128037123 108307976070622470192055685)
      ·
        refine ⟨20307745513241713161010441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108307976070622470192055685 20307745513241713161010441)
        ·
          refine ⟨15230809134931284870757831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20307745513241713161010441 15230809134931284870757831)
          ·
            refine ⟨22846213702396927306136747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15230809134931284870757831 22846213702396927306136747)
            ·
              refine ⟨34269320553595390959205121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22846213702396927306136747 34269320553595390959205121)
              ·
                refine ⟨25701990415196543219403841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34269320553595390959205121 25701990415196543219403841)
                ·
                  refine ⟨19276492811397407414552881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25701990415196543219403841 19276492811397407414552881)
                  ·
                    refine ⟨14457369608548055560914661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19276492811397407414552881 14457369608548055560914661)
                    ·
                      refine ⟨2710756801602760417671499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14457369608548055560914661 2710756801602760417671499)
                      ·
                        rfl

theorem cell23_5279180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5279180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279180 prefixEnd_5279180 := by exact prefixLift 5279180
  have htrace : WordTrace (prefixWord ++ tailWord_5279180) baseStart_5279180 baseEnd_5279180 := by
    simpa [prefixWord, tailWord_5279180, baseEnd_5279180] using wordTrace_append hprefix tailTrace_5279180
  have hstable : (prefixWord ++ tailWord_5279180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279180).length < 2 ^ (prefixWord ++ tailWord_5279180).sum := by decide
  have hdescent : baseEnd_5279180 < baseStart_5279180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279201 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_5279201 : Nat := 118140960795 + 5279201 * 2 ^ 59
def prefixEnd_5279201 : Nat := 4983230072969 + 3 ^ 40 * 5279201 * 2
def baseEnd_5279201 : Nat := 2710767584696504835508903

theorem tailTrace_5279201 : CollatzResearch.WordTrace tailWord_5279201 prefixEnd_5279201 2710767584696504835508903 := by
  unfold tailWord_5279201
  simp only [CollatzResearch.WordTrace]
  refine ⟨192548278947363867594613457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128365519298242578396408971 192548278947363867594613457)
  ·
    refine ⟨144411209210522900695960093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192548278947363867594613457 144411209210522900695960093)
    ·
      refine ⟨54154203453946087760985035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144411209210522900695960093 54154203453946087760985035)
      ·
        refine ⟨81231305180919131641477553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54154203453946087760985035 81231305180919131641477553)
        ·
          refine ⟨60923478885689348731108165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81231305180919131641477553 60923478885689348731108165)
          ·
            refine ⟨11423152291066752887082781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60923478885689348731108165 11423152291066752887082781)
            ·
              refine ⟨4283682109150032332656043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11423152291066752887082781 4283682109150032332656043)
              ·
                refine ⟨6425523163725048498984065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283682109150032332656043 6425523163725048498984065)
                ·
                  refine ⟨4819142372793786374238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6425523163725048498984065 4819142372793786374238049)
                  ·
                    refine ⟨3614356779595339780678537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4819142372793786374238049 3614356779595339780678537)
                    ·
                      refine ⟨2710767584696504835508903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614356779595339780678537 2710767584696504835508903)
                      ·
                        rfl

theorem cell23_5279201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_5279201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279201 prefixEnd_5279201 := by exact prefixLift 5279201
  have htrace : WordTrace (prefixWord ++ tailWord_5279201) baseStart_5279201 baseEnd_5279201 := by
    simpa [prefixWord, tailWord_5279201, baseEnd_5279201] using wordTrace_append hprefix tailTrace_5279201
  have hstable : (prefixWord ++ tailWord_5279201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279201).length < 2 ^ (prefixWord ++ tailWord_5279201).sum := by decide
  have hdescent : baseEnd_5279201 < baseStart_5279201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279240 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5279240 : Nat := 118140960795 + 5279240 * 2 ^ 59
def prefixEnd_5279240 : Nat := 4983230072969 + 3 ^ 40 * 5279240 * 2
def baseEnd_5279240 : Nat := 2710787610442030182921223

theorem tailTrace_5279240 : CollatzResearch.WordTrace tailWord_5279240 prefixEnd_5279240 2710787610442030182921223 := by
  unfold tailWord_5279240
  simp only [CollatzResearch.WordTrace]
  refine ⟨96274850697111288627641587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128366467596148384836855449 96274850697111288627641587)
  ·
    refine ⟨144412276045666932941462381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96274850697111288627641587 144412276045666932941462381)
    ·
      refine ⟨54154603517125099853048393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144412276045666932941462381 54154603517125099853048393)
      ·
        refine ⟨40615952637843824889786295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54154603517125099853048393 40615952637843824889786295)
        ·
          refine ⟨60923928956765737334679443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40615952637843824889786295 60923928956765737334679443)
          ·
            refine ⟨91385893435148606002019165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60923928956765737334679443 91385893435148606002019165)
            ·
              refine ⟨34269710038180727250757187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91385893435148606002019165 34269710038180727250757187)
              ·
                refine ⟨51404565057271090876135781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34269710038180727250757187 51404565057271090876135781)
                ·
                  refine ⟨9638355948238329539275459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51404565057271090876135781 9638355948238329539275459)
                  ·
                    refine ⟨14457533922357494308913189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9638355948238329539275459 14457533922357494308913189)
                    ·
                      refine ⟨2710787610442030182921223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14457533922357494308913189 2710787610442030182921223)
                      ·
                        rfl

theorem cell23_5279240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5279240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279240 prefixEnd_5279240 := by exact prefixLift 5279240
  have htrace : WordTrace (prefixWord ++ tailWord_5279240) baseStart_5279240 baseEnd_5279240 := by
    simpa [prefixWord, tailWord_5279240, baseEnd_5279240] using wordTrace_append hprefix tailTrace_5279240
  have hstable : (prefixWord ++ tailWord_5279240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279240).length < 2 ^ (prefixWord ++ tailWord_5279240).sum := by decide
  have hdescent : baseEnd_5279240 < baseStart_5279240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279252 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5279252 : Nat := 118140960795 + 5279252 * 2 ^ 59
def prefixEnd_5279252 : Nat := 4983230072969 + 3 ^ 40 * 5279252 * 2
def baseEnd_5279252 : Nat := 2710793772209884135971169

theorem tailTrace_5279252 : CollatzResearch.WordTrace tailWord_5279252 prefixEnd_5279252 2710793772209884135971169 := by
  unfold tailWord_5279252
  simp only [CollatzResearch.WordTrace]
  refine ⟨96275069535089551652360005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128366759380119402203146673 96275069535089551652360005)
  ·
    refine ⟨18051575537829290934817501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96275069535089551652360005 18051575537829290934817501)
    ·
      refine ⟨6769340826685984100556563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18051575537829290934817501 6769340826685984100556563)
      ·
        refine ⟨10154011240028976150834845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769340826685984100556563 10154011240028976150834845)
        ·
          refine ⟨3807754215010866056563067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10154011240028976150834845 3807754215010866056563067)
          ·
            refine ⟨5711631322516299084844601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807754215010866056563067 5711631322516299084844601)
            ·
              refine ⟨4283723491887224313633451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711631322516299084844601 4283723491887224313633451)
              ·
                refine ⟨6425585237830836470450177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283723491887224313633451 6425585237830836470450177)
                ·
                  refine ⟨4819188928373127352837633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6425585237830836470450177 4819188928373127352837633)
                  ·
                    refine ⟨3614391696279845514628225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4819188928373127352837633 3614391696279845514628225)
                    ·
                      refine ⟨2710793772209884135971169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614391696279845514628225 2710793772209884135971169)
                      ·
                        rfl

theorem cell23_5279252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5279252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279252 prefixEnd_5279252 := by exact prefixLift 5279252
  have htrace : WordTrace (prefixWord ++ tailWord_5279252) baseStart_5279252 baseEnd_5279252 := by
    simpa [prefixWord, tailWord_5279252, baseEnd_5279252] using wordTrace_append hprefix tailTrace_5279252
  have hstable : (prefixWord ++ tailWord_5279252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279252).length < 2 ^ (prefixWord ++ tailWord_5279252).sum := by decide
  have hdescent : baseEnd_5279252 < baseStart_5279252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279297 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 6]
def baseStart_5279297 : Nat := 118140960795 + 5279297 * 2 ^ 59
def prefixEnd_5279297 : Nat := 4983230072969 + 3 ^ 40 * 5279297 * 2
def baseEnd_5279297 : Nat := 301201875426592939989829

theorem tailTrace_5279297 : CollatzResearch.WordTrace tailWord_5279297 prefixEnd_5279297 301201875426592939989829 := by
  unfold tailWord_5279297
  simp only [CollatzResearch.WordTrace]
  refine ⟨192551780355016075990108145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128367853570010717326738763 192551780355016075990108145)
  ·
    refine ⟨144413835266262056992581109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192551780355016075990108145 144413835266262056992581109)
    ·
      refine ⟨13538797056212067843054479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144413835266262056992581109 13538797056212067843054479)
      ·
        refine ⟨20308195584318101764581719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13538797056212067843054479 20308195584318101764581719)
        ·
          refine ⟨30462293376477152646872579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20308195584318101764581719 30462293376477152646872579)
          ·
            refine ⟨45693440064715728970308869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30462293376477152646872579 45693440064715728970308869)
            ·
              refine ⟨8567520012134199181932913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45693440064715728970308869 8567520012134199181932913)
              ·
                refine ⟨6425640009100649386449685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8567520012134199181932913 6425640009100649386449685)
                ·
                  refine ⟨301201875426592939989829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6425640009100649386449685 301201875426592939989829)
                  ·
                    rfl

theorem cell23_5279297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_5279297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279297 prefixEnd_5279297 := by exact prefixLift 5279297
  have htrace : WordTrace (prefixWord ++ tailWord_5279297) baseStart_5279297 baseEnd_5279297 := by
    simpa [prefixWord, tailWord_5279297, baseEnd_5279297] using wordTrace_append hprefix tailTrace_5279297
  have hstable : (prefixWord ++ tailWord_5279297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279297).length < 2 ^ (prefixWord ++ tailWord_5279297).sum := by decide
  have hdescent : baseEnd_5279297 < baseStart_5279297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279307 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 3]
def baseStart_5279307 : Nat := 118140960795 + 5279307 * 2 ^ 59
def prefixEnd_5279307 : Nat := 4983230072969 + 3 ^ 40 * 5279307 * 2
def baseEnd_5279307 : Nat := 2710822013645881420783415

theorem tailTrace_5279307 : CollatzResearch.WordTrace tailWord_5279307 prefixEnd_5279307 2710822013645881420783415 := by
  unfold tailWord_5279307
  simp only [CollatzResearch.WordTrace]
  refine ⟨192552145084979847697972175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128368096723319898465314783 192552145084979847697972175)
  ·
    refine ⟨288828217627469771546958263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192552145084979847697972175 288828217627469771546958263)
    ·
      refine ⟨433242326441204657320437395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288828217627469771546958263 433242326441204657320437395)
      ·
        refine ⟨649863489661806985980656093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433242326441204657320437395 649863489661806985980656093)
        ·
          refine ⟨243698808623177619742746035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 649863489661806985980656093 243698808623177619742746035)
          ·
            refine ⟨365548212934766429614119053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243698808623177619742746035 365548212934766429614119053)
            ·
              refine ⟨137080579850537411105294645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365548212934766429614119053 137080579850537411105294645)
              ·
                refine ⟨12851304360987882291121373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137080579850537411105294645 12851304360987882291121373)
                ·
                  refine ⟨4819239135370455859170515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12851304360987882291121373 4819239135370455859170515)
                  ·
                    refine ⟨7228858703055683788755773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819239135370455859170515 7228858703055683788755773)
                    ·
                      refine ⟨2710822013645881420783415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228858703055683788755773 2710822013645881420783415)
                      ·
                        rfl

theorem cell23_5279307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 3].length) (baseStart_5279307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279307 prefixEnd_5279307 := by exact prefixLift 5279307
  have htrace : WordTrace (prefixWord ++ tailWord_5279307) baseStart_5279307 baseEnd_5279307 := by
    simpa [prefixWord, tailWord_5279307, baseEnd_5279307] using wordTrace_append hprefix tailTrace_5279307
  have hstable : (prefixWord ++ tailWord_5279307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279307).length < 2 ^ (prefixWord ++ tailWord_5279307).sum := by decide
  have hdescent : baseEnd_5279307 < baseStart_5279307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279317 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5279317 : Nat := 118140960795 + 5279317 * 2 ^ 59
def prefixEnd_5279317 : Nat := 4983230072969 + 3 ^ 40 * 5279317 * 2
def baseEnd_5279317 : Nat := 2710827148452426381658369

theorem tailTrace_5279317 : CollatzResearch.WordTrace tailWord_5279317 prefixEnd_5279317 2710827148452426381658369 := by
  unfold tailWord_5279317
  simp only [CollatzResearch.WordTrace]
  refine ⟨192552509814943619405836205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128368339876629079603890803 192552509814943619405836205)
  ·
    refine ⟨72207191180603857277188577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192552509814943619405836205 72207191180603857277188577)
    ·
      refine ⟨54155393385452892957891433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72207191180603857277188577 54155393385452892957891433)
      ·
        refine ⟨40616545039089669718418575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54155393385452892957891433 40616545039089669718418575)
        ·
          refine ⟨60924817558634504577627863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40616545039089669718418575 60924817558634504577627863)
          ·
            refine ⟨91387226337951756866441795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60924817558634504577627863 91387226337951756866441795)
            ·
              refine ⟨137080839506927635299662693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91387226337951756866441795 137080839506927635299662693)
              ·
                refine ⟨25702657407548931618686755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137080839506927635299662693 25702657407548931618686755)
                ·
                  refine ⟨38553986111323397428030133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25702657407548931618686755 38553986111323397428030133)
                  ·
                    refine ⟨3614436197936568508877825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38553986111323397428030133 3614436197936568508877825)
                    ·
                      refine ⟨2710827148452426381658369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614436197936568508877825 2710827148452426381658369)
                      ·
                        rfl

theorem cell23_5279317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5279317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279317 prefixEnd_5279317 := by exact prefixLift 5279317
  have htrace : WordTrace (prefixWord ++ tailWord_5279317) baseStart_5279317 baseEnd_5279317 := by
    simpa [prefixWord, tailWord_5279317, baseEnd_5279317] using wordTrace_append hprefix tailTrace_5279317
  have hstable : (prefixWord ++ tailWord_5279317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279317).length < 2 ^ (prefixWord ++ tailWord_5279317).sum := by decide
  have hdescent : baseEnd_5279317 < baseStart_5279317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279318 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5279318 : Nat := 118140960795 + 5279318 * 2 ^ 59
def prefixEnd_5279318 : Nat := 4983230072969 + 3 ^ 40 * 5279318 * 2
def baseEnd_5279318 : Nat := 903609220644360292581955

theorem tailTrace_5279318 : CollatzResearch.WordTrace tailWord_5279318 prefixEnd_5279318 903609220644360292581955 := by
  unfold tailWord_5279318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034534142996249786038913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128368364191959997717748405 12034534142996249786038913)
  ·
    refine ⟨9025900607247187339529185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12034534142996249786038913 9025900607247187339529185)
    ·
      refine ⟨6769425455435390504646889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9025900607247187339529185 6769425455435390504646889)
      ·
        refine ⟨5077069091576542878485167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6769425455435390504646889 5077069091576542878485167)
        ·
          refine ⟨7615603637364814317727751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077069091576542878485167 7615603637364814317727751)
          ·
            refine ⟨11423405456047221476591627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615603637364814317727751 11423405456047221476591627)
            ·
              refine ⟨17135108184070832214887441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423405456047221476591627 17135108184070832214887441)
              ·
                refine ⟨12851331138053124161165581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17135108184070832214887441 12851331138053124161165581)
                ·
                  refine ⟨4819249176769921560437093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12851331138053124161165581 4819249176769921560437093)
                  ·
                    refine ⟨903609220644360292581955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4819249176769921560437093 903609220644360292581955)
                    ·
                      rfl

theorem cell23_5279318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5279318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279318 prefixEnd_5279318 := by exact prefixLift 5279318
  have htrace : WordTrace (prefixWord ++ tailWord_5279318) baseStart_5279318 baseEnd_5279318 := by
    simpa [prefixWord, tailWord_5279318, baseEnd_5279318] using wordTrace_append hprefix tailTrace_5279318
  have hstable : (prefixWord ++ tailWord_5279318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279318).length < 2 ^ (prefixWord ++ tailWord_5279318).sum := by decide
  have hdescent : baseEnd_5279318 < baseStart_5279318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279324 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5279324 : Nat := 118140960795 + 5279324 * 2 ^ 59
def prefixEnd_5279324 : Nat := 4983230072969 + 3 ^ 40 * 5279324 * 2
def baseEnd_5279324 : Nat := 2710830742817007854270837

theorem tailTrace_5279324 : CollatzResearch.WordTrace tailWord_5279324 prefixEnd_5279324 2710830742817007854270837 := by
  unfold tailWord_5279324
  simp only [CollatzResearch.WordTrace]
  refine ⟨96276382562959129800670513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128368510083945506400894017 96276382562959129800670513)
  ·
    refine ⟨72207286922219347350502885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96276382562959129800670513 72207286922219347350502885)
    ·
      refine ⟨13538866297916127628219291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72207286922219347350502885 13538866297916127628219291)
      ·
        refine ⟨20308299446874191442328937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13538866297916127628219291 20308299446874191442328937)
        ·
          refine ⟨15231224585155643581746703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20308299446874191442328937 15231224585155643581746703)
          ·
            refine ⟨22846836877733465372620055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15231224585155643581746703 22846836877733465372620055)
            ·
              refine ⟨34270255316600198058930083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22846836877733465372620055 34270255316600198058930083)
              ·
                refine ⟨51405382974900297088395125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34270255316600198058930083 51405382974900297088395125)
                ·
                  refine ⟨4819254653896902852037043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51405382974900297088395125 4819254653896902852037043)
                  ·
                    refine ⟨7228881980845354278055565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819254653896902852037043 7228881980845354278055565)
                    ·
                      refine ⟨2710830742817007854270837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228881980845354278055565 2710830742817007854270837)
                      ·
                        rfl

theorem cell23_5279324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5279324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279324 prefixEnd_5279324 := by exact prefixLift 5279324
  have htrace : WordTrace (prefixWord ++ tailWord_5279324) baseStart_5279324 baseEnd_5279324 := by
    simpa [prefixWord, tailWord_5279324, baseEnd_5279324] using wordTrace_append hprefix tailTrace_5279324
  have hstable : (prefixWord ++ tailWord_5279324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279324).length < 2 ^ (prefixWord ++ tailWord_5279324).sum := by decide
  have hdescent : baseEnd_5279324 < baseStart_5279324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279344 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_5279344 : Nat := 118140960795 + 5279344 * 2 ^ 59
def prefixEnd_5279344 : Nat := 4983230072969 + 3 ^ 40 * 5279344 * 2
def baseEnd_5279344 : Nat := 903613670810032592006915

theorem tailTrace_5279344 : CollatzResearch.WordTrace tailWord_5279344 prefixEnd_5279344 903613670810032592006915 := by
  unfold tailWord_5279344
  simp only [CollatzResearch.WordTrace]
  refine ⟨96276747292922901508534543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128368996390563868678046057 96276747292922901508534543)
  ·
    refine ⟨144415120939384352262801815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96276747292922901508534543 144415120939384352262801815)
    ·
      refine ⟨216622681409076528394202723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144415120939384352262801815 216622681409076528394202723)
      ·
        refine ⟨324934022113614792591304085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216622681409076528394202723 324934022113614792591304085)
        ·
          refine ⟨15231282286575693402717379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324934022113614792591304085 15231282286575693402717379)
          ·
            refine ⟨22846923429863540104076069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15231282286575693402717379 22846923429863540104076069)
            ·
              refine ⟨4283798143099413769514263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22846923429863540104076069 4283798143099413769514263)
              ·
                refine ⟨6425697214649120654271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283798143099413769514263 6425697214649120654271395)
                ·
                  refine ⟨9638545821973680981407093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425697214649120654271395 9638545821973680981407093)
                  ·
                    refine ⟨903613670810032592006915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9638545821973680981407093 903613670810032592006915)
                    ·
                      rfl

theorem cell23_5279344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_5279344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279344 prefixEnd_5279344 := by exact prefixLift 5279344
  have htrace : WordTrace (prefixWord ++ tailWord_5279344) baseStart_5279344 baseEnd_5279344 := by
    simpa [prefixWord, tailWord_5279344, baseEnd_5279344] using wordTrace_append hprefix tailTrace_5279344
  have hstable : (prefixWord ++ tailWord_5279344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279344).length < 2 ^ (prefixWord ++ tailWord_5279344).sum := by decide
  have hdescent : baseEnd_5279344 < baseStart_5279344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279360 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_5279360 : Nat := 118140960795 + 5279360 * 2 ^ 59
def prefixEnd_5279360 : Nat := 4983230072969 + 3 ^ 40 * 5279360 * 2
def baseEnd_5279360 : Nat := 2710849228120569713420671

theorem tailTrace_5279360 : CollatzResearch.WordTrace tailWord_5279360 prefixEnd_5279360 2710849228120569713420671 := by
  unfold tailWord_5279360
  simp only [CollatzResearch.WordTrace]
  refine ⟨96277039076893918874825767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128369385435858558499767689 96277039076893918874825767)
  ·
    refine ⟨144415558615340878312238651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96277039076893918874825767 144415558615340878312238651)
    ·
      refine ⟨216623337923011317468357977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144415558615340878312238651 216623337923011317468357977)
      ·
        refine ⟨162467503442258488101268483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216623337923011317468357977 162467503442258488101268483)
        ·
          refine ⟨243701255163387732151902725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162467503442258488101268483 243701255163387732151902725)
          ·
            refine ⟨45693985343135199778481761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243701255163387732151902725 45693985343135199778481761)
            ·
              refine ⟨34270489007351399833861321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45693985343135199778481761 34270489007351399833861321)
              ·
                refine ⟨25702866755513549875395991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34270489007351399833861321 25702866755513549875395991)
                ·
                  refine ⟨38554300133270324813093987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25702866755513549875395991 38554300133270324813093987)
                  ·
                    refine ⟨57831450199905487219640981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38554300133270324813093987 57831450199905487219640981)
                    ·
                      refine ⟨2710849228120569713420671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57831450199905487219640981 2710849228120569713420671)
                      ·
                        rfl

theorem cell23_5279360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_5279360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279360 prefixEnd_5279360 := by exact prefixLift 5279360
  have htrace : WordTrace (prefixWord ++ tailWord_5279360) baseStart_5279360 baseEnd_5279360 := by
    simpa [prefixWord, tailWord_5279360, baseEnd_5279360] using wordTrace_append hprefix tailTrace_5279360
  have hstable : (prefixWord ++ tailWord_5279360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279360).length < 2 ^ (prefixWord ++ tailWord_5279360).sum := by decide
  have hdescent : baseEnd_5279360 < baseStart_5279360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279367 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_5279367 : Nat := 118140960795 + 5279367 * 2 ^ 59
def prefixEnd_5279367 : Nat := 4983230072969 + 3 ^ 40 * 5279367 * 2
def baseEnd_5279367 : Nat := 2710852822485151186033139

theorem tailTrace_5279367 : CollatzResearch.WordTrace tailWord_5279367 prefixEnd_5279367 2710852822485151186033139 := by
  unfold tailWord_5279367
  simp only [CollatzResearch.WordTrace]
  refine ⟨192554333464762477945156355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128369555643174985296770903 192554333464762477945156355)
  ·
    refine ⟨288831500197143716917734533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192554333464762477945156355 288831500197143716917734533)
    ·
      refine ⟨54155906286964446922075225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288831500197143716917734533 54155906286964446922075225)
      ·
        refine ⟨40616929715223335191556419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54155906286964446922075225 40616929715223335191556419)
        ·
          refine ⟨60925394572835002787334629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40616929715223335191556419 60925394572835002787334629)
          ·
            refine ⟨11423511482406563022625243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60925394572835002787334629 11423511482406563022625243)
            ·
              refine ⟨17135267223609844533937865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423511482406563022625243 17135267223609844533937865)
              ·
                refine ⟨12851450417707383400453399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17135267223609844533937865 12851450417707383400453399)
                ·
                  refine ⟨19277175626561075100680099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12851450417707383400453399 19277175626561075100680099)
                  ·
                    refine ⟨28915763439841612651020149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19277175626561075100680099 28915763439841612651020149)
                    ·
                      refine ⟨2710852822485151186033139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28915763439841612651020149 2710852822485151186033139)
                      ·
                        rfl

theorem cell23_5279367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_5279367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279367 prefixEnd_5279367 := by exact prefixLift 5279367
  have htrace : WordTrace (prefixWord ++ tailWord_5279367) baseStart_5279367 baseEnd_5279367 := by
    simpa [prefixWord, tailWord_5279367, baseEnd_5279367] using wordTrace_append hprefix tailTrace_5279367
  have hstable : (prefixWord ++ tailWord_5279367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279367).length < 2 ^ (prefixWord ++ tailWord_5279367).sum := by decide
  have hdescent : baseEnd_5279367 < baseStart_5279367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279374 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_5279374 : Nat := 118140960795 + 5279374 * 2 ^ 59
def prefixEnd_5279374 : Nat := 4983230072969 + 3 ^ 40 * 5279374 * 2
def baseEnd_5279374 : Nat := 903618805616577552881869

theorem tailTrace_5279374 : CollatzResearch.WordTrace tailWord_5279374 prefixEnd_5279374 903618805616577552881869 := by
  unfold tailWord_5279374
  simp only [CollatzResearch.WordTrace]
  refine ⟨24069323596967139767582647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128369725850491412093774117 24069323596967139767582647)
  ·
    refine ⟨36103985395450709651373971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24069323596967139767582647 36103985395450709651373971)
    ·
      refine ⟨54155978093176064477060957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36103985395450709651373971 54155978093176064477060957)
      ·
        refine ⟨20308491784941024178897859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54155978093176064477060957 20308491784941024178897859)
        ·
          refine ⟨30462737677411536268346789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20308491784941024178897859 30462737677411536268346789)
          ·
            refine ⟨5711763314514663050315023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30462737677411536268346789 5711763314514663050315023)
            ·
              refine ⟨8567644971771994575472535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711763314514663050315023 8567644971771994575472535)
              ·
                refine ⟨12851467457657991863208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567644971771994575472535 12851467457657991863208803)
                ·
                  refine ⟨19277201186486987794813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12851467457657991863208803 19277201186486987794813205)
                  ·
                    refine ⟨903618805616577552881869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19277201186486987794813205 903618805616577552881869)
                    ·
                      rfl

theorem cell23_5279374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_5279374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279374 prefixEnd_5279374 := by exact prefixLift 5279374
  have htrace : WordTrace (prefixWord ++ tailWord_5279374) baseStart_5279374 baseEnd_5279374 := by
    simpa [prefixWord, tailWord_5279374, baseEnd_5279374] using wordTrace_append hprefix tailTrace_5279374
  have hstable : (prefixWord ++ tailWord_5279374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279374).length < 2 ^ (prefixWord ++ tailWord_5279374).sum := by decide
  have hdescent : baseEnd_5279374 < baseStart_5279374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279384 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5279384 : Nat := 118140960795 + 5279384 * 2 ^ 59
def prefixEnd_5279384 : Nat := 4983230072969 + 3 ^ 40 * 5279384 * 2
def baseEnd_5279384 : Nat := 2710861551656277619520561

theorem tailTrace_5279384 : CollatzResearch.WordTrace tailWord_5279384 prefixEnd_5279384 2710861551656277619520561 := by
  unfold tailWord_5279384
  simp only [CollatzResearch.WordTrace]
  refine ⟨96277476752850444924262603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128369969003800593232350137 96277476752850444924262603)
  ·
    refine ⟨144416215129275667386393905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96277476752850444924262603 144416215129275667386393905)
    ·
      refine ⟨108312161346956750539795429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144416215129275667386393905 108312161346956750539795429)
      ·
        refine ⟨20308530252554390726211643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108312161346956750539795429 20308530252554390726211643)
        ·
          refine ⟨30462795378831586089317465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20308530252554390726211643 30462795378831586089317465)
          ·
            refine ⟨22847096534123689566988099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30462795378831586089317465 22847096534123689566988099)
            ·
              refine ⟨34270644801185534350482149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22847096534123689566988099 34270644801185534350482149)
              ·
                refine ⟨6425745900222287690715403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34270644801185534350482149 6425745900222287690715403)
                ·
                  refine ⟨9638618850333431536073105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425745900222287690715403 9638618850333431536073105)
                  ·
                    refine ⟨7228964137750073652054829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9638618850333431536073105 7228964137750073652054829)
                    ·
                      refine ⟨2710861551656277619520561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228964137750073652054829 2710861551656277619520561)
                      ·
                        rfl

theorem cell23_5279384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5279384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279384 prefixEnd_5279384 := by exact prefixLift 5279384
  have htrace : WordTrace (prefixWord ++ tailWord_5279384) baseStart_5279384 baseEnd_5279384 := by
    simpa [prefixWord, tailWord_5279384, baseEnd_5279384] using wordTrace_append hprefix tailTrace_5279384
  have hstable : (prefixWord ++ tailWord_5279384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279384).length < 2 ^ (prefixWord ++ tailWord_5279384).sum := by decide
  have hdescent : baseEnd_5279384 < baseStart_5279384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279397 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_5279397 : Nat := 118140960795 + 5279397 * 2 ^ 59
def prefixEnd_5279397 : Nat := 4983230072969 + 3 ^ 40 * 5279397 * 2
def baseEnd_5279397 : Nat := 2710868226904786068658001

theorem tailTrace_5279397 : CollatzResearch.WordTrace tailWord_5279397 prefixEnd_5279397 2710868226904786068658001 := by
  unfold tailWord_5279397
  simp only [CollatzResearch.WordTrace]
  refine ⟨192555427654653793068748445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128370285103102528712498963 192555427654653793068748445)
  ·
    refine ⟨72208285370495172400780667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192555427654653793068748445 72208285370495172400780667)
    ·
      refine ⟨108312428055742758601171001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72208285370495172400780667 108312428055742758601171001)
      ·
        refine ⟨81234321041807068950878251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108312428055742758601171001 81234321041807068950878251)
        ·
          refine ⟨121851481562710603426317377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81234321041807068950878251 121851481562710603426317377)
          ·
            refine ⟨91388611172032952569738033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121851481562710603426317377 91388611172032952569738033)
            ·
              refine ⟨68541458379024714427303525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91388611172032952569738033 68541458379024714427303525)
              ·
                refine ⟨12851523446067133955119411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68541458379024714427303525 12851523446067133955119411)
                ·
                  refine ⟨19277285169100700932679117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12851523446067133955119411 19277285169100700932679117)
                  ·
                    refine ⟨7228981938412762849754669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19277285169100700932679117 7228981938412762849754669)
                    ·
                      refine ⟨2710868226904786068658001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7228981938412762849754669 2710868226904786068658001)
                      ·
                        rfl

theorem cell23_5279397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_5279397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279397 prefixEnd_5279397 := by exact prefixLift 5279397
  have htrace : WordTrace (prefixWord ++ tailWord_5279397) baseStart_5279397 baseEnd_5279397 := by
    simpa [prefixWord, tailWord_5279397, baseEnd_5279397] using wordTrace_append hprefix tailTrace_5279397
  have hstable : (prefixWord ++ tailWord_5279397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279397).length < 2 ^ (prefixWord ++ tailWord_5279397).sum := by decide
  have hdescent : baseEnd_5279397 < baseStart_5279397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279415 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_5279415 : Nat := 118140960795 + 5279415 * 2 ^ 59
def prefixEnd_5279415 : Nat := 4983230072969 + 3 ^ 40 * 5279415 * 2
def baseEnd_5279415 : Nat := 2710877469556566998232919

theorem tailTrace_5279415 : CollatzResearch.WordTrace tailWord_5279415 prefixEnd_5279415 2710877469556566998232919 := by
  unfold tailWord_5279415
  simp only [CollatzResearch.WordTrace]
  refine ⟨192556084168588582142903699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128370722779059054761935799 192556084168588582142903699)
  ·
    refine ⟨288834126252882873214355549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192556084168588582142903699 288834126252882873214355549)
    ·
      refine ⟨108312797344831077455383331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288834126252882873214355549 108312797344831077455383331)
      ·
        refine ⟨162469196017246616183074997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108312797344831077455383331 162469196017246616183074997)
        ·
          refine ⟨15231487126616870267163281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162469196017246616183074997 15231487126616870267163281)
          ·
            refine ⟨11423615344962652700372461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15231487126616870267163281 11423615344962652700372461)
            ·
              refine ⟨4283855754360994762639673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11423615344962652700372461 4283855754360994762639673)
              ·
                refine ⟨3212891815770746071979755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4283855754360994762639673 3212891815770746071979755)
                ·
                  refine ⟨4819337723656119107969633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212891815770746071979755 4819337723656119107969633)
                  ·
                    refine ⟨3614503292742089330977225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4819337723656119107969633 3614503292742089330977225)
                    ·
                      refine ⟨2710877469556566998232919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614503292742089330977225 2710877469556566998232919)
                      ·
                        rfl

theorem cell23_5279415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_5279415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279415 prefixEnd_5279415 := by exact prefixLift 5279415
  have htrace : WordTrace (prefixWord ++ tailWord_5279415) baseStart_5279415 baseEnd_5279415 := by
    simpa [prefixWord, tailWord_5279415, baseEnd_5279415] using wordTrace_append hprefix tailTrace_5279415
  have hstable : (prefixWord ++ tailWord_5279415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279415).length < 2 ^ (prefixWord ++ tailWord_5279415).sum := by decide
  have hdescent : baseEnd_5279415 < baseStart_5279415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279424 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2]
def baseStart_5279424 : Nat := 118140960795 + 5279424 * 2 ^ 59
def prefixEnd_5279424 : Nat := 4983230072969 + 3 ^ 40 * 5279424 * 2
def baseEnd_5279424 : Nat := 2710882090882457463020377

theorem tailTrace_5279424 : CollatzResearch.WordTrace tailWord_5279424 prefixEnd_5279424 2710882090882457463020377 := by
  unfold tailWord_5279424
  simp only [CollatzResearch.WordTrace]
  refine ⟨96278206212777988339990663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128370941617037317786654217 96278206212777988339990663)
  ·
    refine ⟨144417309319166982509985995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96278206212777988339990663 144417309319166982509985995)
    ·
      refine ⟨216625963978750473764978993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144417309319166982509985995 216625963978750473764978993)
      ·
        refine ⟨162469472984062855323734245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216625963978750473764978993 162469472984062855323734245)
        ·
          refine ⟨30463026184511785373200171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162469472984062855323734245 30463026184511785373200171)
          ·
            refine ⟨45694539276767678059800257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30463026184511785373200171 45694539276767678059800257)
            ·
              refine ⟨34270904457575758544850193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45694539276767678059800257 34270904457575758544850193)
              ·
                refine ⟨25703178343181818908637645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34270904457575758544850193 25703178343181818908637645)
                ·
                  refine ⟨9638691878693182090739117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25703178343181818908637645 9638691878693182090739117)
                  ·
                    refine ⟨3614509454509943284027169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9638691878693182090739117 3614509454509943284027169)
                    ·
                      refine ⟨2710882090882457463020377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614509454509943284027169 2710882090882457463020377)
                      ·
                        rfl

theorem cell23_5279424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_5279424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279424 prefixEnd_5279424 := by exact prefixLift 5279424
  have htrace : WordTrace (prefixWord ++ tailWord_5279424) baseStart_5279424 baseEnd_5279424 := by
    simpa [prefixWord, tailWord_5279424, baseEnd_5279424] using wordTrace_append hprefix tailTrace_5279424
  have hstable : (prefixWord ++ tailWord_5279424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279424).length < 2 ^ (prefixWord ++ tailWord_5279424).sum := by decide
  have hdescent : baseEnd_5279424 < baseStart_5279424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279441 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_5279441 : Nat := 118140960795 + 5279441 * 2 ^ 59
def prefixEnd_5279441 : Nat := 4983230072969 + 3 ^ 40 * 5279441 * 2
def baseEnd_5279441 : Nat := 2710890820053583896507799

theorem tailTrace_5279441 : CollatzResearch.WordTrace tailWord_5279441 prefixEnd_5279441 2710890820053583896507799 := by
  unfold tailWord_5279441
  simp only [CollatzResearch.WordTrace]
  refine ⟨192557032466494388583350177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128371354977662925722233451 192557032466494388583350177)
  ·
    refine ⟨144417774349870791437512633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192557032466494388583350177 144417774349870791437512633)
    ·
      refine ⟨108313330762403093578134475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144417774349870791437512633 108313330762403093578134475)
      ·
        refine ⟨162469996143604640367201713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108313330762403093578134475 162469996143604640367201713)
        ·
          refine ⟨121852497107703480275401285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162469996143604640367201713 121852497107703480275401285)
          ·
            refine ⟨22847343207694402551637741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121852497107703480275401285 22847343207694402551637741)
            ·
              refine ⟨8567753702885400956864153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22847343207694402551637741 8567753702885400956864153)
              ·
                refine ⟨6425815277164050717648115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8567753702885400956864153 6425815277164050717648115)
                ·
                  refine ⟨9638722915746076076472173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425815277164050717648115 9638722915746076076472173)
                  ·
                    refine ⟨3614521093404778528677065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9638722915746076076472173 3614521093404778528677065)
                    ·
                      refine ⟨2710890820053583896507799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614521093404778528677065 2710890820053583896507799)
                      ·
                        rfl

theorem cell23_5279441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_5279441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279441 prefixEnd_5279441 := by exact prefixLift 5279441
  have htrace : WordTrace (prefixWord ++ tailWord_5279441) baseStart_5279441 baseEnd_5279441 := by
    simpa [prefixWord, tailWord_5279441, baseEnd_5279441] using wordTrace_append hprefix tailTrace_5279441
  have hstable : (prefixWord ++ tailWord_5279441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279441).length < 2 ^ (prefixWord ++ tailWord_5279441).sum := by decide
  have hdescent : baseEnd_5279441 < baseStart_5279441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279487 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_5279487 : Nat := 118140960795 + 5279487 * 2 ^ 59
def prefixEnd_5279487 : Nat := 4983230072969 + 3 ^ 40 * 5279487 * 2
def baseEnd_5279487 : Nat := 2710914440163690716532587

theorem tailTrace_5279487 : CollatzResearch.WordTrace tailWord_5279487 prefixEnd_5279487 2710914440163690716532587 := by
  unfold tailWord_5279487
  simp only [CollatzResearch.WordTrace]
  refine ⟨192558710224327738439524715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128372473482885158959683143 192558710224327738439524715)
  ·
    refine ⟨288838065336491607659287073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192558710224327738439524715 288838065336491607659287073)
    ·
      refine ⟨216628549002368705744465305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288838065336491607659287073 216628549002368705744465305)
      ·
        refine ⟨162471411751776529308348979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216628549002368705744465305 162471411751776529308348979)
        ·
          refine ⟨243707117627664793962523469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162471411751776529308348979 243707117627664793962523469)
          ·
            refine ⟨91390169110374297735946301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243707117627664793962523469 91390169110374297735946301)
            ·
              refine ⟨34271313416390361650979863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91390169110374297735946301 34271313416390361650979863)
              ·
                refine ⟨51406970124585542476469795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34271313416390361650979863 51406970124585542476469795)
                ·
                  refine ⟨77110455186878313714704693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51406970124585542476469795 77110455186878313714704693)
                  ·
                    refine ⟨7229105173769841910753565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77110455186878313714704693 7229105173769841910753565)
                    ·
                      refine ⟨2710914440163690716532587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229105173769841910753565 2710914440163690716532587)
                      ·
                        rfl

theorem cell23_5279487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_5279487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279487 prefixEnd_5279487 := by exact prefixLift 5279487
  have htrace : WordTrace (prefixWord ++ tailWord_5279487) baseStart_5279487 baseEnd_5279487 := by
    simpa [prefixWord, tailWord_5279487, baseEnd_5279487] using wordTrace_append hprefix tailTrace_5279487
  have hstable : (prefixWord ++ tailWord_5279487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279487).length < 2 ^ (prefixWord ++ tailWord_5279487).sum := by decide
  have hdescent : baseEnd_5279487 < baseStart_5279487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279507 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 2, 5]
def baseStart_5279507 : Nat := 118140960795 + 5279507 * 2 ^ 59
def prefixEnd_5279507 : Nat := 4983230072969 + 3 ^ 40 * 5279507 * 2
def baseEnd_5279507 : Nat := 903641569925593546094165

theorem tailTrace_5279507 : CollatzResearch.WordTrace tailWord_5279507 prefixEnd_5279507 903641569925593546094165 := by
  unfold tailWord_5279507
  simp only [CollatzResearch.WordTrace]
  refine ⟨192559439684255281855252775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128372959789503521236835183 192559439684255281855252775)
  ·
    refine ⟨288839159526382922782879163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192559439684255281855252775 288839159526382922782879163)
    ·
      refine ⟨433258739289574384174318745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288839159526382922782879163 433258739289574384174318745)
      ·
        refine ⟨324944054467180788130739059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433258739289574384174318745 324944054467180788130739059)
        ·
          refine ⟨487416081700771182196108589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324944054467180788130739059 487416081700771182196108589)
          ·
            refine ⟨182781030637789193323540721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487416081700771182196108589 182781030637789193323540721)
            ·
              refine ⟨137085772978341894992655541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182781030637789193323540721 137085772978341894992655541)
              ·
                refine ⟨12851791216719552655561457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137085772978341894992655541 12851791216719552655561457)
                ·
                  refine ⟨9638843412539664491671093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12851791216719552655561457 9638843412539664491671093)
                  ·
                    refine ⟨903641569925593546094165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9638843412539664491671093 903641569925593546094165)
                    ·
                      rfl

theorem cell23_5279507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].length) (baseStart_5279507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279507 prefixEnd_5279507 := by exact prefixLift 5279507
  have htrace : WordTrace (prefixWord ++ tailWord_5279507) baseStart_5279507 baseEnd_5279507 := by
    simpa [prefixWord, tailWord_5279507, baseEnd_5279507] using wordTrace_append hprefix tailTrace_5279507
  have hstable : (prefixWord ++ tailWord_5279507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279507).length < 2 ^ (prefixWord ++ tailWord_5279507).sum := by decide
  have hdescent : baseEnd_5279507 < baseStart_5279507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279511 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 5]
def baseStart_5279511 : Nat := 118140960795 + 5279511 * 2 ^ 59
def prefixEnd_5279511 : Nat := 4983230072969 + 3 ^ 40 * 5279511 * 2
def baseEnd_5279511 : Nat := 301214084855488735848053

theorem tailTrace_5279511 : CollatzResearch.WordTrace tailWord_5279511 prefixEnd_5279511 301214084855488735848053 := by
  unfold tailWord_5279511
  simp only [CollatzResearch.WordTrace]
  refine ⟨192559585576240790538398387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128373057050827193692265591 192559585576240790538398387)
  ·
    refine ⟨288839378364361185807597581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192559585576240790538398387 288839378364361185807597581)
    ·
      refine ⟨108314766886635444677849093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288839378364361185807597581 108314766886635444677849093)
      ·
        refine ⟨20309018791244145877096705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108314766886635444677849093 20309018791244145877096705)
        ·
          refine ⟨15231764093433109407822529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20309018791244145877096705 15231764093433109407822529)
          ·
            refine ⟨11423823070074832055866897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15231764093433109407822529 11423823070074832055866897)
            ·
              refine ⟨8567867302556124041900173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11423823070074832055866897 8567867302556124041900173)
              ·
                refine ⟨3212950238458546515712565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8567867302556124041900173 3212950238458546515712565)
                ·
                  refine ⟨301214084855488735848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3212950238458546515712565 301214084855488735848053)
                  ·
                    rfl

theorem cell23_5279511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 5].length) (baseStart_5279511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279511 prefixEnd_5279511 := by exact prefixLift 5279511
  have htrace : WordTrace (prefixWord ++ tailWord_5279511) baseStart_5279511 baseEnd_5279511 := by
    simpa [prefixWord, tailWord_5279511, baseEnd_5279511] using wordTrace_append hprefix tailTrace_5279511
  have hstable : (prefixWord ++ tailWord_5279511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279511).length < 2 ^ (prefixWord ++ tailWord_5279511).sum := by decide
  have hdescent : baseEnd_5279511 < baseStart_5279511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279557 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_5279557 : Nat := 118140960795 + 5279557 * 2 ^ 59
def prefixEnd_5279557 : Nat := 4983230072969 + 3 ^ 40 * 5279557 * 2
def baseEnd_5279557 : Nat := 2710950383809505442657265

theorem tailTrace_5279557 : CollatzResearch.WordTrace tailWord_5279557 prefixEnd_5279557 2710950383809505442657265 := by
  unfold tailWord_5279557
  simp only [CollatzResearch.WordTrace]
  refine ⟨192561263334074140394572925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128374175556049426929715283 192561263334074140394572925)
  ·
    refine ⟨72210473750277802647964847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192561263334074140394572925 72210473750277802647964847)
    ·
      refine ⟨108315710625416703971947271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72210473750277802647964847 108315710625416703971947271)
      ·
        refine ⟨162473565938125055957920907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108315710625416703971947271 162473565938125055957920907)
        ·
          refine ⟨243710348907187583936881361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162473565938125055957920907 243710348907187583936881361)
          ·
            refine ⟨182782761680390687952661021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243710348907187583936881361 182782761680390687952661021)
            ·
              refine ⟨68543535630146507982247883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182782761680390687952661021 68543535630146507982247883)
              ·
                refine ⟨102815303445219761973371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68543535630146507982247883 102815303445219761973371825)
                ·
                  refine ⟨77111477583914821480028869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102815303445219761973371825 77111477583914821480028869)
                  ·
                    refine ⟨14458402046984029027505413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77111477583914821480028869 14458402046984029027505413)
                    ·
                      refine ⟨2710950383809505442657265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14458402046984029027505413 2710950383809505442657265)
                      ·
                        rfl

theorem cell23_5279557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_5279557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279557 prefixEnd_5279557 := by exact prefixLift 5279557
  have htrace : WordTrace (prefixWord ++ tailWord_5279557) baseStart_5279557 baseEnd_5279557 := by
    simpa [prefixWord, tailWord_5279557, baseEnd_5279557] using wordTrace_append hprefix tailTrace_5279557
  have hstable : (prefixWord ++ tailWord_5279557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279557).length < 2 ^ (prefixWord ++ tailWord_5279557).sum := by decide
  have hdescent : baseEnd_5279557 < baseStart_5279557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279588 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_5279588 : Nat := 118140960795 + 5279588 * 2 ^ 59
def prefixEnd_5279588 : Nat := 4983230072969 + 3 ^ 40 * 5279588 * 2
def baseEnd_5279588 : Nat := 903655433903264940456541

theorem tailTrace_5279588 : CollatzResearch.WordTrace tailWord_5279588 prefixEnd_5279588 903655433903264940456541 := by
  unfold tailWord_5279588
  simp only [CollatzResearch.WordTrace]
  refine ⟨96281196998480916344475709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128374929331307888459300945 96281196998480916344475709)
  ·
    refine ⟨36105448874430343629178391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96281196998480916344475709 36105448874430343629178391)
    ·
      refine ⟨54158173311645515443767587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36105448874430343629178391 54158173311645515443767587)
      ·
        refine ⟨81237259967468273165651381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54158173311645515443767587 81237259967468273165651381)
        ·
          refine ⟨7615993121950150609279817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81237259967468273165651381 7615993121950150609279817)
          ·
            refine ⟨5711994841462612956959863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7615993121950150609279817 5711994841462612956959863)
            ·
              refine ⟨8567992262193919435439795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711994841462612956959863 8567992262193919435439795)
              ·
                refine ⟨12851988393290879153159693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567992262193919435439795 12851988393290879153159693)
                ·
                  refine ⟨4819495647484079682434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12851988393290879153159693 4819495647484079682434885)
                  ·
                    refine ⟨903655433903264940456541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4819495647484079682434885 903655433903264940456541)
                    ·
                      rfl

theorem cell23_5279588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_5279588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279588 prefixEnd_5279588 := by exact prefixLift 5279588
  have htrace : WordTrace (prefixWord ++ tailWord_5279588) baseStart_5279588 baseEnd_5279588 := by
    simpa [prefixWord, tailWord_5279588, baseEnd_5279588] using wordTrace_append hprefix tailTrace_5279588
  have hstable : (prefixWord ++ tailWord_5279588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279588).length < 2 ^ (prefixWord ++ tailWord_5279588).sum := by decide
  have hdescent : baseEnd_5279588 < baseStart_5279588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_5279628 : Nat := 118140960795 + 5279628 * 2 ^ 59
def prefixEnd_5279628 : Nat := 4983230072969 + 3 ^ 40 * 5279628 * 2
def baseEnd_5279628 : Nat := 2710986840935974664869439

theorem tailTrace_5279628 : CollatzResearch.WordTrace tailWord_5279628 prefixEnd_5279628 2710986840935974664869439 := by
  unfold tailWord_5279628
  simp only [CollatzResearch.WordTrace]
  refine ⟨96281926458408459760203769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128375901944544613013605025 96281926458408459760203769)
  ·
    refine ⟨72211444843806344820152827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96281926458408459760203769 72211444843806344820152827)
    ·
      refine ⟨108317167265709517230229241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72211444843806344820152827 108317167265709517230229241)
      ·
        refine ⟨81237875449282137922671931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108317167265709517230229241 81237875449282137922671931)
        ·
          refine ⟨121856813173923206884007897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81237875449282137922671931 121856813173923206884007897)
          ·
            refine ⟨91392609880442405163005923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121856813173923206884007897 91392609880442405163005923)
            ·
              refine ⟨137088914820663607744508885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91392609880442405163005923 137088914820663607744508885)
              ·
                refine ⟨3213021441109303306511927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137088914820663607744508885 3213021441109303306511927)
                ·
                  refine ⟨4819532161663954959767891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213021441109303306511927 4819532161663954959767891)
                  ·
                    refine ⟨7229298242495932439651837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819532161663954959767891 7229298242495932439651837)
                    ·
                      refine ⟨2710986840935974664869439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229298242495932439651837 2710986840935974664869439)
                      ·
                        rfl

theorem cell23_5279628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_5279628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279628 prefixEnd_5279628 := by exact prefixLift 5279628
  have htrace : WordTrace (prefixWord ++ tailWord_5279628) baseStart_5279628 baseEnd_5279628 := by
    simpa [prefixWord, tailWord_5279628, baseEnd_5279628] using wordTrace_append hprefix tailTrace_5279628
  have hstable : (prefixWord ++ tailWord_5279628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279628).length < 2 ^ (prefixWord ++ tailWord_5279628).sum := by decide
  have hdescent : baseEnd_5279628 < baseStart_5279628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279645 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_5279645 : Nat := 118140960795 + 5279645 * 2 ^ 59
def prefixEnd_5279645 : Nat := 4983230072969 + 3 ^ 40 * 5279645 * 2
def baseEnd_5279645 : Nat := 2710995570107101098356861

theorem tailTrace_5279645 : CollatzResearch.WordTrace tailWord_5279645 prefixEnd_5279645 2710995570107101098356861 := by
  unfold tailWord_5279645
  simp only [CollatzResearch.WordTrace]
  refine ⟨192564472957755331423776389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128376315305170220949184259 192564472957755331423776389)
  ·
    refine ⟨36105838679579124641958073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192564472957755331423776389 36105838679579124641958073)
    ·
      refine ⟨27079379009684343481468555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36105838679579124641958073 27079379009684343481468555)
      ·
        refine ⟨40619068514526515222202833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27079379009684343481468555 40619068514526515222202833)
        ·
          refine ⟨30464301385894886416652125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40619068514526515222202833 30464301385894886416652125)
          ·
            refine ⟨11424113019710582406244547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30464301385894886416652125 11424113019710582406244547)
            ·
              refine ⟨17136169529565873609366821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11424113019710582406244547 17136169529565873609366821)
              ·
                refine ⟨3213031786793601301756279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17136169529565873609366821 3213031786793601301756279)
                ·
                  refine ⟨4819547680190401952634419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213031786793601301756279 4819547680190401952634419)
                  ·
                    refine ⟨7229321520285602928951629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819547680190401952634419 7229321520285602928951629)
                    ·
                      refine ⟨2710995570107101098356861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229321520285602928951629 2710995570107101098356861)
                      ·
                        rfl

theorem cell23_5279645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_5279645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279645 prefixEnd_5279645 := by exact prefixLift 5279645
  have htrace : WordTrace (prefixWord ++ tailWord_5279645) baseStart_5279645 baseEnd_5279645 := by
    simpa [prefixWord, tailWord_5279645, baseEnd_5279645] using wordTrace_append hprefix tailTrace_5279645
  have hstable : (prefixWord ++ tailWord_5279645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279645).length < 2 ^ (prefixWord ++ tailWord_5279645).sum := by decide
  have hdescent : baseEnd_5279645 < baseStart_5279645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279657 : List Nat := [1, 2, 1, 1, 1, 1, 4, 12]
def baseStart_5279657 : Nat := 118140960795 + 5279657 * 2 ^ 59
def prefixEnd_5279657 : Nat := 4983230072969 + 3 ^ 40 * 5279657 * 2
def baseEnd_5279657 : Nat := 100407471550924261163215

theorem tailTrace_5279657 : CollatzResearch.WordTrace tailWord_5279657 prefixEnd_5279657 100407471550924261163215 := by
  unfold tailWord_5279657
  simp only [CollatzResearch.WordTrace]
  refine ⟨192564910633711857473213225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128376607089141238315475483 192564910633711857473213225)
  ·
    refine ⟨144423682975283893104909919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192564910633711857473213225 144423682975283893104909919)
    ·
      refine ⟨216635524462925839657364879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144423682975283893104909919 216635524462925839657364879)
      ·
        refine ⟨324953286694388759486047319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216635524462925839657364879 324953286694388759486047319)
        ·
          refine ⟨487429930041583139229070979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324953286694388759486047319 487429930041583139229070979)
          ·
            refine ⟨731144895062374708843606469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487429930041583139229070979 731144895062374708843606469)
            ·
              refine ⟨137089667824195257908176213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 731144895062374708843606469 137089667824195257908176213)
              ·
                refine ⟨100407471550924261163215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 137089667824195257908176213 100407471550924261163215)
                ·
                  rfl

theorem cell23_5279657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 12].length) (baseStart_5279657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279657 prefixEnd_5279657 := by exact prefixLift 5279657
  have htrace : WordTrace (prefixWord ++ tailWord_5279657) baseStart_5279657 baseEnd_5279657 := by
    simpa [prefixWord, tailWord_5279657, baseEnd_5279657] using wordTrace_append hprefix tailTrace_5279657
  have hstable : (prefixWord ++ tailWord_5279657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279657).length < 2 ^ (prefixWord ++ tailWord_5279657).sum := by decide
  have hdescent : baseEnd_5279657 < baseStart_5279657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279671 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_5279671 : Nat := 118140960795 + 5279671 * 2 ^ 59
def prefixEnd_5279671 : Nat := 4983230072969 + 3 ^ 40 * 5279671 * 2
def baseEnd_5279671 : Nat := 2711008920604117996631741

theorem tailTrace_5279671 : CollatzResearch.WordTrace tailWord_5279671 prefixEnd_5279671 2711008920604117996631741 := by
  unfold tailWord_5279671
  simp only [CollatzResearch.WordTrace]
  refine ⟨192565421255661137864222867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128376947503774091909481911 192565421255661137864222867)
  ·
    refine ⟨288848131883491706796334301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192565421255661137864222867 288848131883491706796334301)
    ·
      refine ⟨108318049456309390048625363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288848131883491706796334301 108318049456309390048625363)
      ·
        refine ⟨162477074184464085072938045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108318049456309390048625363 162477074184464085072938045)
        ·
          refine ⟨60928902819174031902351767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162477074184464085072938045 60928902819174031902351767)
          ·
            refine ⟨91393354228761047853527651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60928902819174031902351767 91393354228761047853527651)
            ·
              refine ⟨137090031343141571780291477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91393354228761047853527651 137090031343141571780291477)
              ·
                refine ⟨6426095219209761177201163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137090031343141571780291477 6426095219209761177201163)
                ·
                  refine ⟨9639142828814641765801745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426095219209761177201163 9639142828814641765801745)
                  ·
                    refine ⟨7229357121610981324351309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9639142828814641765801745 7229357121610981324351309)
                    ·
                      refine ⟨2711008920604117996631741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229357121610981324351309 2711008920604117996631741)
                      ·
                        rfl

theorem cell23_5279671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_5279671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279671 prefixEnd_5279671 := by exact prefixLift 5279671
  have htrace : WordTrace (prefixWord ++ tailWord_5279671) baseStart_5279671 baseEnd_5279671 := by
    simpa [prefixWord, tailWord_5279671, baseEnd_5279671] using wordTrace_append hprefix tailTrace_5279671
  have hstable : (prefixWord ++ tailWord_5279671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279671).length < 2 ^ (prefixWord ++ tailWord_5279671).sum := by decide
  have hdescent : baseEnd_5279671 < baseStart_5279671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279688 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_5279688 : Nat := 118140960795 + 5279688 * 2 ^ 59
def prefixEnd_5279688 : Nat := 4983230072969 + 3 ^ 40 * 5279688 * 2
def baseEnd_5279688 : Nat := 2711017649775244430119163

theorem tailTrace_5279688 : CollatzResearch.WordTrace tailWord_5279688 prefixEnd_5279688 2711017649775244430119163 := by
  unfold tailWord_5279688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96283020648299774883795859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128377360864399699845061145 96283020648299774883795859)
  ·
    refine ⟨144424530972449662325693789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96283020648299774883795859 144424530972449662325693789)
    ·
      refine ⟨54159199114668623372135171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144424530972449662325693789 54159199114668623372135171)
      ·
        refine ⟨81238798672002935058202757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54159199114668623372135171 81238798672002935058202757)
        ·
          refine ⟨15232274751000550323413017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81238798672002935058202757 15232274751000550323413017)
          ·
            refine ⟨11424206063250412742559763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15232274751000550323413017 11424206063250412742559763)
            ·
              refine ⟨17136309094875619113839645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11424206063250412742559763 17136309094875619113839645)
              ·
                refine ⟨6426115910578357167689867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17136309094875619113839645 6426115910578357167689867)
                ·
                  refine ⟨9639173865867535751534801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426115910578357167689867 9639173865867535751534801)
                  ·
                    refine ⟨7229380399400651813651101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9639173865867535751534801 7229380399400651813651101)
                    ·
                      refine ⟨2711017649775244430119163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229380399400651813651101 2711017649775244430119163)
                      ·
                        rfl

theorem cell23_5279688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_5279688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279688 prefixEnd_5279688 := by exact prefixLift 5279688
  have htrace : WordTrace (prefixWord ++ tailWord_5279688) baseStart_5279688 baseEnd_5279688 := by
    simpa [prefixWord, tailWord_5279688, baseEnd_5279688] using wordTrace_append hprefix tailTrace_5279688
  have hstable : (prefixWord ++ tailWord_5279688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279688).length < 2 ^ (prefixWord ++ tailWord_5279688).sum := by decide
  have hdescent : baseEnd_5279688 < baseStart_5279688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279724 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_5279724 : Nat := 118140960795 + 5279724 * 2 ^ 59
def prefixEnd_5279724 : Nat := 4983230072969 + 3 ^ 40 * 5279724 * 2
def baseEnd_5279724 : Nat := 2711036135078806289268997

theorem tailTrace_5279724 : CollatzResearch.WordTrace tailWord_5279724 prefixEnd_5279724 2711036135078806289268997 := by
  unfold tailWord_5279724
  simp only [CollatzResearch.WordTrace]
  refine ⟨96283677162234563957951113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128378236216312751943934817 96283677162234563957951113)
  ·
    refine ⟨72212757871675922968463335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96283677162234563957951113 72212757871675922968463335)
    ·
      refine ⟨108319136807513884452695003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72212757871675922968463335 108319136807513884452695003)
      ·
        refine ⟨162478705211270826679042505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108319136807513884452695003 162478705211270826679042505)
        ·
          refine ⟨121859028908453120009281879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162478705211270826679042505 121859028908453120009281879)
          ·
            refine ⟨182788543362679680013922819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121859028908453120009281879 182788543362679680013922819)
            ·
              refine ⟨274182815044019520020884229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182788543362679680013922819 274182815044019520020884229)
              ·
                refine ⟨51409277820753660003915793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274182815044019520020884229 51409277820753660003915793)
                ·
                  refine ⟨38556958365565245002936845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51409277820753660003915793 38556958365565245002936845)
                  ·
                    refine ⟨14458859387086966876101317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38556958365565245002936845 14458859387086966876101317)
                    ·
                      refine ⟨2711036135078806289268997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14458859387086966876101317 2711036135078806289268997)
                      ·
                        rfl

theorem cell23_5279724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_5279724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279724 prefixEnd_5279724 := by exact prefixLift 5279724
  have htrace : WordTrace (prefixWord ++ tailWord_5279724) baseStart_5279724 baseEnd_5279724 := by
    simpa [prefixWord, tailWord_5279724, baseEnd_5279724] using wordTrace_append hprefix tailTrace_5279724
  have hstable : (prefixWord ++ tailWord_5279724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279724).length < 2 ^ (prefixWord ++ tailWord_5279724).sum := by decide
  have hdescent : baseEnd_5279724 < baseStart_5279724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279725 : List Nat := [1, 5, 1, 4, 1, 2, 2, 7]
def baseStart_5279725 : Nat := 118140960795 + 5279725 * 2 ^ 59
def prefixEnd_5279725 : Nat := 4983230072969 + 3 ^ 40 * 5279725 * 2
def baseEnd_5279725 : Nat := 100408764761461510568759

theorem tailTrace_5279725 : CollatzResearch.WordTrace tailWord_5279725 prefixEnd_5279725 100408764761461510568759 := by
  unfold tailWord_5279725
  simp only [CollatzResearch.WordTrace]
  refine ⟨192567390797465505086688629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128378260531643670057792419 192567390797465505086688629)
  ·
    refine ⟨18053192887262391101877059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192567390797465505086688629 18053192887262391101877059)
    ·
      refine ⟨27079789330893586652815589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18053192887262391101877059 27079789330893586652815589)
      ·
        refine ⟨5077460499542547497402923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27079789330893586652815589 5077460499542547497402923)
        ·
          refine ⟨7616190749313821246104385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077460499542547497402923 7616190749313821246104385)
          ·
            refine ⟨5712143061985365934578289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616190749313821246104385 5712143061985365934578289)
            ·
              refine ⟨4284107296489024450933717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712143061985365934578289 4284107296489024450933717)
              ·
                refine ⟨100408764761461510568759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4284107296489024450933717 100408764761461510568759)
                ·
                  rfl

theorem cell23_5279725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 7].length) (baseStart_5279725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279725 prefixEnd_5279725 := by exact prefixLift 5279725
  have htrace : WordTrace (prefixWord ++ tailWord_5279725) baseStart_5279725 baseEnd_5279725 := by
    simpa [prefixWord, tailWord_5279725, baseEnd_5279725] using wordTrace_append hprefix tailTrace_5279725
  have hstable : (prefixWord ++ tailWord_5279725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279725).length < 2 ^ (prefixWord ++ tailWord_5279725).sum := by decide
  have hdescent : baseEnd_5279725 < baseStart_5279725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279728 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2]
def baseStart_5279728 : Nat := 118140960795 + 5279728 * 2 ^ 59
def prefixEnd_5279728 : Nat := 4983230072969 + 3 ^ 40 * 5279728 * 2
def baseEnd_5279728 : Nat := 2711038189001424273618979

theorem tailTrace_5279728 : CollatzResearch.WordTrace tailWord_5279728 prefixEnd_5279728 2711038189001424273618979 := by
  unfold tailWord_5279728
  simp only [CollatzResearch.WordTrace]
  refine ⟨96283750108227318299523919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128378333477636424399365225 96283750108227318299523919)
  ·
    refine ⟨144425625162340977449285879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96283750108227318299523919 144425625162340977449285879)
    ·
      refine ⟨216638437743511466173928819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144425625162340977449285879 216638437743511466173928819)
      ·
        refine ⟨324957656615267199260893229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216638437743511466173928819 324957656615267199260893229)
        ·
          refine ⟨121859121230725199722834961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324957656615267199260893229 121859121230725199722834961)
          ·
            refine ⟨91394340923043899792126221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121859121230725199722834961 91394340923043899792126221)
            ·
              refine ⟨34272877846141462422047333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91394340923043899792126221 34272877846141462422047333)
              ·
                refine ⟨6426164596151524204133875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34272877846141462422047333 6426164596151524204133875)
                ·
                  refine ⟨9639246894227286306200813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426164596151524204133875 9639246894227286306200813)
                  ·
                    refine ⟨3614717585335232364825305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9639246894227286306200813 3614717585335232364825305)
                    ·
                      refine ⟨2711038189001424273618979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614717585335232364825305 2711038189001424273618979)
                      ·
                        rfl

theorem cell23_5279728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2].length) (baseStart_5279728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279728 prefixEnd_5279728 := by exact prefixLift 5279728
  have htrace : WordTrace (prefixWord ++ tailWord_5279728) baseStart_5279728 baseEnd_5279728 := by
    simpa [prefixWord, tailWord_5279728, baseEnd_5279728] using wordTrace_append hprefix tailTrace_5279728
  have hstable : (prefixWord ++ tailWord_5279728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279728).length < 2 ^ (prefixWord ++ tailWord_5279728).sum := by decide
  have hdescent : baseEnd_5279728 < baseStart_5279728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279775 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 2, 2, 2]
def baseStart_5279775 : Nat := 118140960795 + 5279775 * 2 ^ 59
def prefixEnd_5279775 : Nat := 4983230072969 + 3 ^ 40 * 5279775 * 2
def baseEnd_5279775 : Nat := 2711062322592185589731263

theorem tailTrace_5279775 : CollatzResearch.WordTrace tailWord_5279775 prefixEnd_5279775 2711062322592185589731263 := by
  unfold tailWord_5279775
  simp only [CollatzResearch.WordTrace]
  refine ⟨192569214447284363626008779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128379476298189575750672519 192569214447284363626008779)
  ·
    refine ⟨288853821670926545439013169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192569214447284363626008779 288853821670926545439013169)
    ·
      refine ⟨216640366253194909079259877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288853821670926545439013169 216640366253194909079259877)
      ·
        refine ⟨40620068672474045452361227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216640366253194909079259877 40620068672474045452361227)
        ·
          refine ⟨60930103008711068178541841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40620068672474045452361227 60930103008711068178541841)
          ·
            refine ⟨45697577256533301133906381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60930103008711068178541841 45697577256533301133906381)
            ·
              refine ⟨17136591471199987925214893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45697577256533301133906381 17136591471199987925214893)
              ·
                refine ⟨6426221801699995471955585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17136591471199987925214893 6426221801699995471955585)
                ·
                  refine ⟨4819666351274996603966689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6426221801699995471955585 4819666351274996603966689)
                  ·
                    refine ⟨3614749763456247452975017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4819666351274996603966689 3614749763456247452975017)
                    ·
                      refine ⟨2711062322592185589731263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614749763456247452975017 2711062322592185589731263)
                      ·
                        rfl

theorem cell23_5279775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_5279775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279775 prefixEnd_5279775 := by exact prefixLift 5279775
  have htrace : WordTrace (prefixWord ++ tailWord_5279775) baseStart_5279775 baseEnd_5279775 := by
    simpa [prefixWord, tailWord_5279775, baseEnd_5279775] using wordTrace_append hprefix tailTrace_5279775
  have hstable : (prefixWord ++ tailWord_5279775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279775).length < 2 ^ (prefixWord ++ tailWord_5279775).sum := by decide
  have hdescent : baseEnd_5279775 < baseStart_5279775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
