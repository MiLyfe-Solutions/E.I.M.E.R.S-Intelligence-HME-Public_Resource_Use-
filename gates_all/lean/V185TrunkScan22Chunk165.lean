import V185TrunkScan22Chunk164

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1474786 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1474786 : Nat := 118140960795 + 1474786 * 2 ^ 59
def prefixEnd_1474786 : Nat := 4983230072969 + 3 ^ 40 * 1474786 * 2
def baseEnd_1474786 : Nat := 168283129004838250376131

theorem tailTrace_1474786 : CollatzResearch.WordTrace tailWord_1474786 prefixEnd_1474786 168283129004838250376131 := by
  unfold tailWord_1474786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447466108777417560311053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35859909623406446827496141 13447466108777417560311053)
  ·
    refine ⟨5042799790791531585116645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13447466108777417560311053 5042799790791531585116645)
    ·
      refine ⟨945524960773412172209371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5042799790791531585116645 945524960773412172209371)
      ·
        refine ⟨1418287441160118258314057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945524960773412172209371 1418287441160118258314057)
        ·
          refine ⟨1063715580870088693735543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418287441160118258314057 1063715580870088693735543)
          ·
            refine ⟨1595573371305133040603315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063715580870088693735543 1595573371305133040603315)
            ·
              refine ⟨2393360056957699560904973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595573371305133040603315 2393360056957699560904973)
              ·
                refine ⟨897510021359137335339365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393360056957699560904973 897510021359137335339365)
                ·
                  refine ⟨168283129004838250376131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 897510021359137335339365 168283129004838250376131)
                  ·
                    rfl

theorem cell22_1474786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1474786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474786 prefixEnd_1474786 := by exact prefixLift 1474786
  have htrace : WordTrace (prefixWord ++ tailWord_1474786) baseStart_1474786 baseEnd_1474786 := by
    simpa [prefixWord, tailWord_1474786, baseEnd_1474786] using wordTrace_append hprefix tailTrace_1474786
  have hstable : (prefixWord ++ tailWord_1474786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474786).length < 2 ^ (prefixWord ++ tailWord_1474786).sum := by decide
  have hdescent : baseEnd_1474786 < baseStart_1474786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474791 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 7]
def baseStart_1474791 : Nat := 118140960795 + 1474791 * 2 ^ 59
def prefixEnd_1474791 : Nat := 4983230072969 + 3 ^ 40 * 1474791 * 2
def baseEnd_1474791 : Nat := 168283699538898801584459

theorem tailTrace_1474791 : CollatzResearch.WordTrace tailWord_1474791 prefixEnd_1474791 168283699538898801584459 := by
  unfold tailWord_1474791
  simp only [CollatzResearch.WordTrace]
  refine ⟨53790046800091556095176227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35860031200061037396784151 53790046800091556095176227)
  ·
    refine ⟨80685070200137334142764341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53790046800091556095176227 80685070200137334142764341)
    ·
      refine ⟨7564225331262875075884157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80685070200137334142764341 7564225331262875075884157)
      ·
        refine ⟨2836584499223578153456559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7564225331262875075884157 2836584499223578153456559)
        ·
          refine ⟨4254876748835367230184839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836584499223578153456559 4254876748835367230184839)
          ·
            refine ⟨6382315123253050845277259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254876748835367230184839 6382315123253050845277259)
            ·
              refine ⟨9573472684879576267915889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382315123253050845277259 9573472684879576267915889)
              ·
                refine ⟨7180104513659682200936917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573472684879576267915889 7180104513659682200936917)
                ·
                  refine ⟨168283699538898801584459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7180104513659682200936917 168283699538898801584459)
                  ·
                    rfl

theorem cell22_1474791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_1474791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474791 prefixEnd_1474791 := by exact prefixLift 1474791
  have htrace : WordTrace (prefixWord ++ tailWord_1474791) baseStart_1474791 baseEnd_1474791 := by
    simpa [prefixWord, tailWord_1474791, baseEnd_1474791] using wordTrace_append hprefix tailTrace_1474791
  have hstable : (prefixWord ++ tailWord_1474791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474791).length < 2 ^ (prefixWord ++ tailWord_1474791).sum := by decide
  have hdescent : baseEnd_1474791 < baseStart_1474791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474806 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1474806 : Nat := 118140960795 + 1474806 * 2 ^ 59
def prefixEnd_1474806 : Nat := 4983230072969 + 3 ^ 40 * 1474806 * 2
def baseEnd_1474806 : Nat := 504856233423241365628331

theorem tailTrace_1474806 : CollatzResearch.WordTrace tailWord_1474806 prefixEnd_1474806 504856233423241365628331 := by
  unfold tailWord_1474806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361912118439825853560767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35860395930024809104648181 3361912118439825853560767)
  ·
    refine ⟨5042868177659738780341151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3361912118439825853560767 5042868177659738780341151)
    ·
      refine ⟨7564302266489608170511727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042868177659738780341151 7564302266489608170511727)
      ·
        refine ⟨11346453399734412255767591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564302266489608170511727 11346453399734412255767591)
        ·
          refine ⟨17019680099601618383651387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346453399734412255767591 17019680099601618383651387)
          ·
            refine ⟨25529520149402427575477081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17019680099601618383651387 25529520149402427575477081)
            ·
              refine ⟨19147140112051820681607811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25529520149402427575477081 19147140112051820681607811)
              ·
                refine ⟨28720710168077731022411717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147140112051820681607811 28720710168077731022411717)
                ·
                  refine ⟨5385133156514574566702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28720710168077731022411717 5385133156514574566702197)
                  ·
                    refine ⟨504856233423241365628331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5385133156514574566702197 504856233423241365628331)
                    ·
                      rfl

theorem cell22_1474806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1474806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474806 prefixEnd_1474806 := by exact prefixLift 1474806
  have htrace : WordTrace (prefixWord ++ tailWord_1474806) baseStart_1474806 baseEnd_1474806 := by
    simpa [prefixWord, tailWord_1474806, baseEnd_1474806] using wordTrace_append hprefix tailTrace_1474806
  have hstable : (prefixWord ++ tailWord_1474806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474806).length < 2 ^ (prefixWord ++ tailWord_1474806).sum := by decide
  have hdescent : baseEnd_1474806 < baseStart_1474806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474812 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1474812 : Nat := 118140960795 + 1474812 * 2 ^ 59
def prefixEnd_1474812 : Nat := 4983230072969 + 3 ^ 40 * 1474812 * 2
def baseEnd_1474812 : Nat := 504858287345859349978313

theorem tailTrace_1474812 : CollatzResearch.WordTrace tailWord_1474812 prefixEnd_1474812 504858287345859349978313 := by
  unfold tailWord_1474812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895406366507738340845345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35860541822010317787793793 26895406366507738340845345)
  ·
    refine ⟨20171554774880803755634009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26895406366507738340845345 20171554774880803755634009)
    ·
      refine ⟨15128666081160602816725507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20171554774880803755634009 15128666081160602816725507)
      ·
        refine ⟨22692999121740904225088261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128666081160602816725507 22692999121740904225088261)
        ·
          refine ⟨4254937335326419542204049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22692999121740904225088261 4254937335326419542204049)
          ·
            refine ⟨3191203001494814656653037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254937335326419542204049 3191203001494814656653037)
            ·
              refine ⟨1196701125560555496244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3191203001494814656653037 1196701125560555496244889)
              ·
                refine ⟨897525844170416622183667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196701125560555496244889 897525844170416622183667)
                ·
                  refine ⟨1346288766255624933275501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897525844170416622183667 1346288766255624933275501)
                  ·
                    refine ⟨504858287345859349978313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346288766255624933275501 504858287345859349978313)
                    ·
                      rfl

theorem cell22_1474812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1474812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474812 prefixEnd_1474812 := by exact prefixLift 1474812
  have htrace : WordTrace (prefixWord ++ tailWord_1474812) baseStart_1474812 baseEnd_1474812 := by
    simpa [prefixWord, tailWord_1474812, baseEnd_1474812] using wordTrace_append hprefix tailTrace_1474812
  have hstable : (prefixWord ++ tailWord_1474812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474812).length < 2 ^ (prefixWord ++ tailWord_1474812).sum := by decide
  have hdescent : baseEnd_1474812 < baseStart_1474812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474851 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_1474851 : Nat := 118140960795 + 1474851 * 2 ^ 59
def prefixEnd_1474851 : Nat := 4983230072969 + 3 ^ 40 * 1474851 * 2
def baseEnd_1474851 : Nat := 504871637842876248253193

theorem tailTrace_1474851 : CollatzResearch.WordTrace tailWord_1474851 prefixEnd_1474851 504871637842876248253193 := by
  unfold tailWord_1474851
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792235179874186342360407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35861490119916124228240271 53792235179874186342360407)
  ·
    refine ⟨80688352769811279513540611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53792235179874186342360407 80688352769811279513540611)
    ·
      refine ⟨121032529154716919270310917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80688352769811279513540611 121032529154716919270310917)
      ·
        refine ⟨22693599216509422363183297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121032529154716919270310917 22693599216509422363183297)
        ·
          refine ⟨17020199412382066772387473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22693599216509422363183297 17020199412382066772387473)
          ·
            refine ⟨12765149559286550079290605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17020199412382066772387473 12765149559286550079290605)
            ·
              refine ⟨4786931084732456279733977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12765149559286550079290605 4786931084732456279733977)
              ·
                refine ⟨3590198313549342209800483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786931084732456279733977 3590198313549342209800483)
                ·
                  refine ⟨5385297470324013314700725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590198313549342209800483 5385297470324013314700725)
                  ·
                    refine ⟨504871637842876248253193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5385297470324013314700725 504871637842876248253193)
                    ·
                      rfl

theorem cell22_1474851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_1474851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474851 prefixEnd_1474851 := by exact prefixLift 1474851
  have htrace : WordTrace (prefixWord ++ tailWord_1474851) baseStart_1474851 baseEnd_1474851 := by
    simpa [prefixWord, tailWord_1474851, baseEnd_1474851] using wordTrace_append hprefix tailTrace_1474851
  have hstable : (prefixWord ++ tailWord_1474851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474851).length < 2 ^ (prefixWord ++ tailWord_1474851).sum := by decide
  have hdescent : baseEnd_1474851 < baseStart_1474851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474900 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1474900 : Nat := 118140960795 + 1474900 * 2 ^ 59
def prefixEnd_1474900 : Nat := 4983230072969 + 3 ^ 40 * 1474900 * 2
def baseEnd_1474900 : Nat := 504888411544256453778043

theorem tailTrace_1474900 : CollatzResearch.WordTrace tailWord_1474900 prefixEnd_1474900 504888411544256453778043 := by
  unfold tailWord_1474900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26897011178348333855447077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35862681571131111807262769 26897011178348333855447077)
  ·
    refine ⟨5043189595940312597896327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26897011178348333855447077 5043189595940312597896327)
    ·
      refine ⟨7564784393910468896844491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043189595940312597896327 7564784393910468896844491)
      ·
        refine ⟨11347176590865703345266737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564784393910468896844491 11347176590865703345266737)
        ·
          refine ⟨8510382443149277508950053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11347176590865703345266737 8510382443149277508950053)
          ·
            refine ⟨1595696708090489532928135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8510382443149277508950053 1595696708090489532928135)
            ·
              refine ⟨2393545062135734299392203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595696708090489532928135 2393545062135734299392203)
              ·
                refine ⟨3590317593203601449088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393545062135734299392203 3590317593203601449088305)
                ·
                  refine ⟨2692738194902701086816229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590317593203601449088305 2692738194902701086816229)
                  ·
                    refine ⟨504888411544256453778043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2692738194902701086816229 504888411544256453778043)
                    ·
                      rfl

theorem cell22_1474900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1474900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474900 prefixEnd_1474900 := by exact prefixLift 1474900
  have htrace : WordTrace (prefixWord ++ tailWord_1474900) baseStart_1474900 baseEnd_1474900 := by
    simpa [prefixWord, tailWord_1474900, baseEnd_1474900] using wordTrace_append hprefix tailTrace_1474900
  have hstable : (prefixWord ++ tailWord_1474900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474900).length < 2 ^ (prefixWord ++ tailWord_1474900).sum := by decide
  have hdescent : baseEnd_1474900 < baseStart_1474900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474930 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_1474930 : Nat := 118140960795 + 1474930 * 2 ^ 59
def prefixEnd_1474930 : Nat := 4983230072969 + 3 ^ 40 * 1474930 * 2
def baseEnd_1474930 : Nat := 504898681157346375527951

theorem tailTrace_1474930 : CollatzResearch.WordTrace tailWord_1474930 prefixEnd_1474930 504898681157346375527951 := by
  unfold tailWord_1474930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13448779136646995708621561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35863411031058655222990829 13448779136646995708621561)
  ·
    refine ⟨10086584352485246781466171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13448779136646995708621561 10086584352485246781466171)
    ·
      refine ⟨15129876528727870172199257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10086584352485246781466171 15129876528727870172199257)
      ·
        refine ⟨11347407396545902629149443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15129876528727870172199257 11347407396545902629149443)
        ·
          refine ⟨17021111094818853943724165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347407396545902629149443 17021111094818853943724165)
          ·
            refine ⟨3191458330278535114448281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17021111094818853943724165 3191458330278535114448281)
            ·
              refine ⟨2393593747708901335836211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191458330278535114448281 2393593747708901335836211)
              ·
                refine ⟨3590390621563352003754317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393593747708901335836211 3590390621563352003754317)
                ·
                  refine ⟨1346396483086257001407869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3590390621563352003754317 1346396483086257001407869)
                  ·
                    refine ⟨504898681157346375527951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346396483086257001407869 504898681157346375527951)
                    ·
                      rfl

theorem cell22_1474930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_1474930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474930 prefixEnd_1474930 := by exact prefixLift 1474930
  have htrace : WordTrace (prefixWord ++ tailWord_1474930) baseStart_1474930 baseEnd_1474930 := by
    simpa [prefixWord, tailWord_1474930, baseEnd_1474930] using wordTrace_append hprefix tailTrace_1474930
  have hstable : (prefixWord ++ tailWord_1474930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474930).length < 2 ^ (prefixWord ++ tailWord_1474930).sum := by decide
  have hdescent : baseEnd_1474930 < baseStart_1474930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475020 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1475020 : Nat := 118140960795 + 1475020 * 2 ^ 59
def prefixEnd_1475020 : Nat := 4983230072969 + 3 ^ 40 * 1475020 * 2
def baseEnd_1475020 : Nat := 504929489996616140777675

theorem tailTrace_1475020 : CollatzResearch.WordTrace tailWord_1475020 prefixEnd_1475020 504929489996616140777675 := by
  unfold tailWord_1475020
  simp only [CollatzResearch.WordTrace]
  refine ⟨26899199558130964102631257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35865599410841285470175009 26899199558130964102631257)
  ·
    refine ⟨20174399668598223076973443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26899199558130964102631257 20174399668598223076973443)
    ·
      refine ⟨30261599502897334615460165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20174399668598223076973443 30261599502897334615460165)
      ·
        refine ⟨5674049906793250240398781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30261599502897334615460165 5674049906793250240398781)
        ·
          refine ⟨2127768715047468840149543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5674049906793250240398781 2127768715047468840149543)
          ·
            refine ⟨3191653072571203260224315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127768715047468840149543 3191653072571203260224315)
            ·
              refine ⟨4787479608856804890336473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191653072571203260224315 4787479608856804890336473)
              ·
                refine ⟨3590609706642603667752355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4787479608856804890336473 3590609706642603667752355)
                ·
                  refine ⟨5385914559963905501628533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590609706642603667752355 5385914559963905501628533)
                  ·
                    refine ⟨504929489996616140777675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5385914559963905501628533 504929489996616140777675)
                    ·
                      rfl

theorem cell22_1475020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1475020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475020 prefixEnd_1475020 := by exact prefixLift 1475020
  have htrace : WordTrace (prefixWord ++ tailWord_1475020) baseStart_1475020 baseEnd_1475020 := by
    simpa [prefixWord, tailWord_1475020, baseEnd_1475020] using wordTrace_append hprefix tailTrace_1475020
  have hstable : (prefixWord ++ tailWord_1475020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475020).length < 2 ^ (prefixWord ++ tailWord_1475020).sum := by decide
  have hdescent : baseEnd_1475020 < baseStart_1475020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475037 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1475037 : Nat := 118140960795 + 1475037 * 2 ^ 59
def prefixEnd_1475037 : Nat := 4983230072969 + 3 ^ 40 * 1475037 * 2
def baseEnd_1475037 : Nat := 504935309444033763102623

theorem tailTrace_1475037 : CollatzResearch.WordTrace tailWord_1475037 prefixEnd_1475037 504935309444033763102623 := by
  unfold tailWord_1475037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53799019157200340108631365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35866012771466893405754243 53799019157200340108631365)
  ·
    refine ⟨10087316091975063770368381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53799019157200340108631365 10087316091975063770368381)
    ·
      refine ⟨3782743534490648913888143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10087316091975063770368381 3782743534490648913888143)
      ·
        refine ⟨5674115301735973370832215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782743534490648913888143 5674115301735973370832215)
        ·
          refine ⟨8511172952603960056248323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674115301735973370832215 8511172952603960056248323)
          ·
            refine ⟨12766759428905940084372485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511172952603960056248323 12766759428905940084372485)
            ·
              refine ⟨2393767392919863765819841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12766759428905940084372485 2393767392919863765819841)
              ·
                refine ⟨1795325544689897824364881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393767392919863765819841 1795325544689897824364881)
                ·
                  refine ⟨1346494158517423368273661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795325544689897824364881 1346494158517423368273661)
                  ·
                    refine ⟨504935309444033763102623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346494158517423368273661 504935309444033763102623)
                    ·
                      rfl

theorem cell22_1475037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1475037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475037 prefixEnd_1475037 := by exact prefixLift 1475037
  have htrace : WordTrace (prefixWord ++ tailWord_1475037) baseStart_1475037 baseEnd_1475037 := by
    simpa [prefixWord, tailWord_1475037, baseEnd_1475037] using wordTrace_append hprefix tailTrace_1475037
  have hstable : (prefixWord ++ tailWord_1475037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475037).length < 2 ^ (prefixWord ++ tailWord_1475037).sum := by decide
  have hdescent : baseEnd_1475037 < baseStart_1475037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475050 : List Nat := [3, 1, 3, 1, 3, 3, 1, 7]
def baseStart_1475050 : Nat := 118140960795 + 1475050 * 2 ^ 59
def prefixEnd_1475050 : Nat := 4983230072969 + 3 ^ 40 * 1475050 * 2
def baseEnd_1475050 : Nat := 56104417734411784725287

theorem tailTrace_1475050 : CollatzResearch.WordTrace tailWord_1475050 prefixEnd_1475050 56104417734411784725287 := by
  unfold tailWord_1475050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449873326538310832213651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35866328870768828885903069 13449873326538310832213651)
  ·
    refine ⟨20174809989807466248320477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449873326538310832213651 20174809989807466248320477)
    ·
      refine ⟨7565553746177799843120179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20174809989807466248320477 7565553746177799843120179)
      ·
        refine ⟨11348330619266699764680269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565553746177799843120179 11348330619266699764680269)
        ·
          refine ⟨4255623982225012411755101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11348330619266699764680269 4255623982225012411755101)
          ·
            refine ⟨1595858993334379654408163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4255623982225012411755101 1595858993334379654408163)
            ·
              refine ⟨2393788490001569481612245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595858993334379654408163 2393788490001569481612245)
              ·
                refine ⟨56104417734411784725287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2393788490001569481612245 56104417734411784725287)
                ·
                  rfl

theorem cell22_1475050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_1475050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475050 prefixEnd_1475050 := by exact prefixLift 1475050
  have htrace : WordTrace (prefixWord ++ tailWord_1475050) baseStart_1475050 baseEnd_1475050 := by
    simpa [prefixWord, tailWord_1475050, baseEnd_1475050] using wordTrace_append hprefix tailTrace_1475050
  have hstable : (prefixWord ++ tailWord_1475050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475050).length < 2 ^ (prefixWord ++ tailWord_1475050).sum := by decide
  have hdescent : baseEnd_1475050 < baseStart_1475050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475093 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1475093 : Nat := 118140960795 + 1475093 * 2 ^ 59
def prefixEnd_1475093 : Nat := 4983230072969 + 3 ^ 40 * 1475093 * 2
def baseEnd_1475093 : Nat := 504954479388468283702451

theorem tailTrace_1475093 : CollatzResearch.WordTrace tailWord_1475093 prefixEnd_1475093 504954479388468283702451 := by
  unfold tailWord_1475093
  simp only [CollatzResearch.WordTrace]
  refine ⟨53801061644997461672669933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35867374429998307781779955 53801061644997461672669933)
  ·
    refine ⟨20175398116874048127251225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53801061644997461672669933 20175398116874048127251225)
    ·
      refine ⟨15131548587655536095438419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20175398116874048127251225 15131548587655536095438419)
      ·
        refine ⟨22697322881483304143157629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131548587655536095438419 22697322881483304143157629)
        ·
          refine ⟨8511496080556239053684111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22697322881483304143157629 8511496080556239053684111)
          ·
            refine ⟨12767244120834358580526167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511496080556239053684111 12767244120834358580526167)
            ·
              refine ⟨19150866181251537870789251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767244120834358580526167 19150866181251537870789251)
              ·
                refine ⟨28726299271877306806183877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19150866181251537870789251 28726299271877306806183877)
                ·
                  refine ⟨5386181113476995026159477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28726299271877306806183877 5386181113476995026159477)
                  ·
                    refine ⟨504954479388468283702451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5386181113476995026159477 504954479388468283702451)
                    ·
                      rfl

theorem cell22_1475093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1475093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475093 prefixEnd_1475093 := by exact prefixLift 1475093
  have htrace : WordTrace (prefixWord ++ tailWord_1475093) baseStart_1475093 baseEnd_1475093 := by
    simpa [prefixWord, tailWord_1475093, baseEnd_1475093] using wordTrace_append hprefix tailTrace_1475093
  have hstable : (prefixWord ++ tailWord_1475093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475093).length < 2 ^ (prefixWord ++ tailWord_1475093).sum := by decide
  have hdescent : baseEnd_1475093 < baseStart_1475093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475123 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 6]
def baseStart_1475123 : Nat := 118140960795 + 1475123 * 2 ^ 59
def prefixEnd_1475123 : Nat := 4983230072969 + 3 ^ 40 * 1475123 * 2
def baseEnd_1475123 : Nat := 168321583000519401817453

theorem tailTrace_1475123 : CollatzResearch.WordTrace tailWord_1475123 prefixEnd_1475123 168321583000519401817453 := by
  unfold tailWord_1475123
  simp only [CollatzResearch.WordTrace]
  refine ⟨53802155834888776796262023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35868103889925851197508015 53802155834888776796262023)
  ·
    refine ⟨80703233752333165194393035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53802155834888776796262023 80703233752333165194393035)
    ·
      refine ⟨121054850628499747791589553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80703233752333165194393035 121054850628499747791589553)
      ·
        refine ⟨90791137971374810843692165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121054850628499747791589553 90791137971374810843692165)
        ·
          refine ⟨17023338369632777033192281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90791137971374810843692165 17023338369632777033192281)
          ·
            refine ⟨12767503777224582774894211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023338369632777033192281 12767503777224582774894211)
            ·
              refine ⟨19151255665836874162341317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767503777224582774894211 19151255665836874162341317)
              ·
                refine ⟨3590860437344413905438997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19151255665836874162341317 3590860437344413905438997)
                ·
                  refine ⟨168321583000519401817453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3590860437344413905438997 168321583000519401817453)
                  ·
                    rfl

theorem cell22_1475123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_1475123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475123 prefixEnd_1475123 := by exact prefixLift 1475123
  have htrace : WordTrace (prefixWord ++ tailWord_1475123) baseStart_1475123 baseEnd_1475123 := by
    simpa [prefixWord, tailWord_1475123, baseEnd_1475123] using wordTrace_append hprefix tailTrace_1475123
  have hstable : (prefixWord ++ tailWord_1475123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475123).length < 2 ^ (prefixWord ++ tailWord_1475123).sum := by decide
  have hdescent : baseEnd_1475123 < baseStart_1475123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475168 : List Nat := [2, 1, 1, 3, 2, 1, 3, 9]
def baseStart_1475168 : Nat := 118140960795 + 1475168 * 2 ^ 59
def prefixEnd_1475168 : Nat := 4983230072969 + 3 ^ 40 * 1475168 * 2
def baseEnd_1475168 : Nat := 56108905935688120897469

theorem tailTrace_1475168 : CollatzResearch.WordTrace tailWord_1475168 prefixEnd_1475168 56108905935688120897469 := by
  unfold tailWord_1475168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901898559862874740825079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35869198079817166321100105 26901898559862874740825079)
  ·
    refine ⟨40352847839794312111237619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26901898559862874740825079 40352847839794312111237619)
    ·
      refine ⟨60529271759691468166856429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40352847839794312111237619 60529271759691468166856429)
      ·
        refine ⟨22698476909884300562571161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60529271759691468166856429 22698476909884300562571161)
        ·
          refine ⟨17023857682413225421928371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22698476909884300562571161 17023857682413225421928371)
          ·
            refine ⟨25535786523619838132892557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17023857682413225421928371 25535786523619838132892557)
            ·
              refine ⟨9575919946357439299834709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25535786523619838132892557 9575919946357439299834709)
              ·
                refine ⟨56108905935688120897469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9575919946357439299834709 56108905935688120897469)
                ·
                  rfl

theorem cell22_1475168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_1475168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475168 prefixEnd_1475168 := by exact prefixLift 1475168
  have htrace : WordTrace (prefixWord ++ tailWord_1475168) baseStart_1475168 baseEnd_1475168 := by
    simpa [prefixWord, tailWord_1475168, baseEnd_1475168] using wordTrace_append hprefix tailTrace_1475168
  have hstable : (prefixWord ++ tailWord_1475168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475168).length < 2 ^ (prefixWord ++ tailWord_1475168).sum := by decide
  have hdescent : baseEnd_1475168 < baseStart_1475168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475172 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1475172 : Nat := 118140960795 + 1475172 * 2 ^ 59
def prefixEnd_1475172 : Nat := 4983230072969 + 3 ^ 40 * 1475172 * 2
def baseEnd_1475172 : Nat := 504981522702938410977209

theorem tailTrace_1475172 : CollatzResearch.WordTrace tailWord_1475172 prefixEnd_1475172 504981522702938410977209 := by
  unfold tailWord_1475172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901971505855629082397885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35869295341140838776530513 26901971505855629082397885)
  ·
    refine ⟨10088239314695860905899207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26901971505855629082397885 10088239314695860905899207)
    ·
      refine ⟨15132358972043791358848811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088239314695860905899207 15132358972043791358848811)
      ·
        refine ⟨22698538458065687038273217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132358972043791358848811 22698538458065687038273217)
        ·
          refine ⟨17023903843549265278704913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22698538458065687038273217 17023903843549265278704913)
          ·
            refine ⟨12767927882661948959028685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023903843549265278704913 12767927882661948959028685)
            ·
              refine ⟨4787972955998230859635757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12767927882661948959028685 4787972955998230859635757)
              ·
                refine ⟨1795489858499336572363409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4787972955998230859635757 1795489858499336572363409)
                ·
                  refine ⟨1346617393874502429272557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795489858499336572363409 1346617393874502429272557)
                  ·
                    refine ⟨504981522702938410977209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346617393874502429272557 504981522702938410977209)
                    ·
                      rfl

theorem cell22_1475172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1475172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475172 prefixEnd_1475172 := by exact prefixLift 1475172
  have htrace : WordTrace (prefixWord ++ tailWord_1475172) baseStart_1475172 baseEnd_1475172 := by
    simpa [prefixWord, tailWord_1475172, baseEnd_1475172] using wordTrace_append hprefix tailTrace_1475172
  have hstable : (prefixWord ++ tailWord_1475172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475172).length < 2 ^ (prefixWord ++ tailWord_1475172).sum := by decide
  have hdescent : baseEnd_1475172 < baseStart_1475172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475176 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1475176 : Nat := 118140960795 + 1475176 * 2 ^ 59
def prefixEnd_1475176 : Nat := 4983230072969 + 3 ^ 40 * 1475176 * 2
def baseEnd_1475176 : Nat := 504982891984683733877197

theorem tailTrace_1475176 : CollatzResearch.WordTrace tailWord_1475176 prefixEnd_1475176 504982891984683733877197 := by
  unfold tailWord_1475176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26902044451848383423970691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35869392602464511231960921 26902044451848383423970691)
  ·
    refine ⟨40353066677772575135956037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26902044451848383423970691 40353066677772575135956037)
    ·
      refine ⟨7566200002082357837991757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40353066677772575135956037 7566200002082357837991757)
      ·
        refine ⟨2837325000780884189246909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7566200002082357837991757 2837325000780884189246909)
        ·
          refine ⟨1063996875292831570967591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2837325000780884189246909 1063996875292831570967591)
          ·
            refine ⟨1595995312939247356451387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063996875292831570967591 1595995312939247356451387)
            ·
              refine ⟨2393992969408871034677081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595995312939247356451387 2393992969408871034677081)
              ·
                refine ⟨1795494727056653276007811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393992969408871034677081 1795494727056653276007811)
                ·
                  refine ⟨2693242090584979914011717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795494727056653276007811 2693242090584979914011717)
                  ·
                    refine ⟨504982891984683733877197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693242090584979914011717 504982891984683733877197)
                    ·
                      rfl

theorem cell22_1475176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1475176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475176 prefixEnd_1475176 := by exact prefixLift 1475176
  have htrace : WordTrace (prefixWord ++ tailWord_1475176) baseStart_1475176 baseEnd_1475176 := by
    simpa [prefixWord, tailWord_1475176, baseEnd_1475176] using wordTrace_append hprefix tailTrace_1475176
  have hstable : (prefixWord ++ tailWord_1475176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475176).length < 2 ^ (prefixWord ++ tailWord_1475176).sum := by decide
  have hdescent : baseEnd_1475176 < baseStart_1475176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475183 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1475183 : Nat := 118140960795 + 1475183 * 2 ^ 59
def prefixEnd_1475183 : Nat := 4983230072969 + 3 ^ 40 * 1475183 * 2
def baseEnd_1475183 : Nat := 504985288227738048952175

theorem tailTrace_1475183 : CollatzResearch.WordTrace tailWord_1475183 prefixEnd_1475183 504985288227738048952175 := by
  unfold tailWord_1475183
  simp only [CollatzResearch.WordTrace]
  refine ⟨53804344214671407043446203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35869562809780938028964135 53804344214671407043446203)
  ·
    refine ⟨80706516322007110565169305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53804344214671407043446203 80706516322007110565169305)
    ·
      refine ⟨60529887241505332923876979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80706516322007110565169305 60529887241505332923876979)
      ·
        refine ⟨90794830862257999385815469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60529887241505332923876979 90794830862257999385815469)
        ·
          refine ⟨34048061573346749769680801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90794830862257999385815469 34048061573346749769680801)
          ·
            refine ⟨25536046180010062327260601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34048061573346749769680801 25536046180010062327260601)
            ·
              refine ⟨19152034635007546745445451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25536046180010062327260601 19152034635007546745445451)
              ·
                refine ⟨28728051952511320118168177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19152034635007546745445451 28728051952511320118168177)
                ·
                  refine ⟨21546038964383490088626133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28728051952511320118168177 21546038964383490088626133)
                  ·
                    refine ⟨504985288227738048952175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21546038964383490088626133 504985288227738048952175)
                    ·
                      rfl

theorem cell22_1475183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1475183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475183 prefixEnd_1475183 := by exact prefixLift 1475183
  have htrace : WordTrace (prefixWord ++ tailWord_1475183) baseStart_1475183 baseEnd_1475183 := by
    simpa [prefixWord, tailWord_1475183, baseEnd_1475183] using wordTrace_append hprefix tailTrace_1475183
  have hstable : (prefixWord ++ tailWord_1475183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475183).length < 2 ^ (prefixWord ++ tailWord_1475183).sum := by decide
  have hdescent : baseEnd_1475183 < baseStart_1475183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475305 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_1475305 : Nat := 118140960795 + 1475305 * 2 ^ 59
def prefixEnd_1475305 : Nat := 4983230072969 + 3 ^ 40 * 1475305 * 2
def baseEnd_1475305 : Nat := 505027051320970397401801

theorem tailTrace_1475305 : CollatzResearch.WordTrace tailWord_1475305 prefixEnd_1475305 505027051320970397401801 := by
  unfold tailWord_1475305
  simp only [CollatzResearch.WordTrace]
  refine ⟨53808793920229421879387369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35872529280152947919591579 53808793920229421879387369)
  ·
    refine ⟨40356595440172066409540527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53808793920229421879387369 40356595440172066409540527)
    ·
      refine ⟨60534893160258099614310791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40356595440172066409540527 60534893160258099614310791)
      ·
        refine ⟨90802339740387149421466187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60534893160258099614310791 90802339740387149421466187)
        ·
          refine ⟨136203509610580724132199281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90802339740387149421466187 136203509610580724132199281)
          ·
            refine ⟨102152632207935543099149461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136203509610580724132199281 102152632207935543099149461)
            ·
              refine ⟨4788404634746978582772631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102152632207935543099149461 4788404634746978582772631)
              ·
                refine ⟨7182606952120467874158947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788404634746978582772631 7182606952120467874158947)
                ·
                  refine ⟨10773910428180701811238421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182606952120467874158947 10773910428180701811238421)
                  ·
                    refine ⟨505027051320970397401801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10773910428180701811238421 505027051320970397401801)
                    ·
                      rfl

theorem cell22_1475305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_1475305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475305 prefixEnd_1475305 := by exact prefixLift 1475305
  have htrace : WordTrace (prefixWord ++ tailWord_1475305) baseStart_1475305 baseEnd_1475305 := by
    simpa [prefixWord, tailWord_1475305, baseEnd_1475305] using wordTrace_append hprefix tailTrace_1475305
  have hstable : (prefixWord ++ tailWord_1475305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475305).length < 2 ^ (prefixWord ++ tailWord_1475305).sum := by decide
  have hdescent : baseEnd_1475305 < baseStart_1475305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475352 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1475352 : Nat := 118140960795 + 1475352 * 2 ^ 59
def prefixEnd_1475352 : Nat := 4983230072969 + 3 ^ 40 * 1475352 * 2
def baseEnd_1475352 : Nat := 505043140381477941476657

theorem tailTrace_1475352 : CollatzResearch.WordTrace tailWord_1475352 prefixEnd_1475352 505043140381477941476657 := by
  unfold tailWord_1475352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26905254075529574453174155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35873672100706099270898873 26905254075529574453174155)
  ·
    refine ⟨40357881113294361679761233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26905254075529574453174155 40357881113294361679761233)
    ·
      refine ⟨30268410834970771259820925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40357881113294361679761233 30268410834970771259820925)
      ·
        refine ⟨11350654063114039222432847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30268410834970771259820925 11350654063114039222432847)
        ·
          refine ⟨17025981094671058833649271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11350654063114039222432847 17025981094671058833649271)
          ·
            refine ⟨25538971642006588250473907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17025981094671058833649271 25538971642006588250473907)
            ·
              refine ⟨38308457463009882375710861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25538971642006588250473907 38308457463009882375710861)
              ·
                refine ⟨14365671548628705890891573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38308457463009882375710861 14365671548628705890891573)
                ·
                  refine ⟨1346781707683941177271085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14365671548628705890891573 1346781707683941177271085)
                  ·
                    refine ⟨505043140381477941476657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346781707683941177271085 505043140381477941476657)
                    ·
                      rfl

theorem cell22_1475352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1475352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475352 prefixEnd_1475352 := by exact prefixLift 1475352
  have htrace : WordTrace (prefixWord ++ tailWord_1475352) baseStart_1475352 baseEnd_1475352 := by
    simpa [prefixWord, tailWord_1475352, baseEnd_1475352] using wordTrace_append hprefix tailTrace_1475352
  have hstable : (prefixWord ++ tailWord_1475352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475352).length < 2 ^ (prefixWord ++ tailWord_1475352).sum := by decide
  have hdescent : baseEnd_1475352 < baseStart_1475352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475442 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1475442 : Nat := 118140960795 + 1475442 * 2 ^ 59
def prefixEnd_1475442 : Nat := 4983230072969 + 3 ^ 40 * 1475442 * 2
def baseEnd_1475442 : Nat := 505073949220747706726381

theorem tailTrace_1475442 : CollatzResearch.WordTrace tailWord_1475442 prefixEnd_1475442 505073949220747706726381 := by
  unfold tailWord_1475442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453447680183273569281145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35875860480488729518083053 13453447680183273569281145)
  ·
    refine ⟨10090085760137455176960859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13453447680183273569281145 10090085760137455176960859)
    ·
      refine ⟨15135128640206182765441289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090085760137455176960859 15135128640206182765441289)
      ·
        refine ⟨11351346480154637074080967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15135128640206182765441289 11351346480154637074080967)
        ·
          refine ⟨17027019720231955611121451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351346480154637074080967 17027019720231955611121451)
          ·
            refine ⟨25540529580347933416682177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17027019720231955611121451 25540529580347933416682177)
            ·
              refine ⟨19155397185260950062511633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25540529580347933416682177 19155397185260950062511633)
              ·
                refine ⟨14366547888945712546883725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19155397185260950062511633 14366547888945712546883725)
                ·
                  refine ⟨5387455458354642205081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14366547888945712546883725 5387455458354642205081397)
                  ·
                    refine ⟨505073949220747706726381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5387455458354642205081397 505073949220747706726381)
                    ·
                      rfl

theorem cell22_1475442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1475442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475442 prefixEnd_1475442 := by exact prefixLift 1475442
  have htrace : WordTrace (prefixWord ++ tailWord_1475442) baseStart_1475442 baseEnd_1475442 := by
    simpa [prefixWord, tailWord_1475442, baseEnd_1475442] using wordTrace_append hprefix tailTrace_1475442
  have hstable : (prefixWord ++ tailWord_1475442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475442).length < 2 ^ (prefixWord ++ tailWord_1475442).sum := by decide
  have hdescent : baseEnd_1475442 < baseStart_1475442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475489 : List Nat := [1, 2, 3, 4, 1, 3, 8]
def baseStart_1475489 : Nat := 118140960795 + 1475489 * 2 ^ 59
def prefixEnd_1475489 : Nat := 4983230072969 + 3 ^ 40 * 1475489 * 2
def baseEnd_1475489 : Nat := 18707038454861305585231

theorem tailTrace_1475489 : CollatzResearch.WordTrace tailWord_1475489 prefixEnd_1475489 18707038454861305585231 := by
  unfold tailWord_1475489
  simp only [CollatzResearch.WordTrace]
  refine ⟨53815504951562821304085521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35877003301041880869390347 53815504951562821304085521)
  ·
    refine ⟨40361628713672115978064141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53815504951562821304085521 40361628713672115978064141)
    ·
      refine ⟨15135610767627043491774053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40361628713672115978064141 15135610767627043491774053)
      ·
        refine ⟨2837927018930070654707635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15135610767627043491774053 2837927018930070654707635)
        ·
          refine ⟨4256890528395105982061453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837927018930070654707635 4256890528395105982061453)
          ·
            refine ⟨1596333948148164743273045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4256890528395105982061453 1596333948148164743273045)
            ·
              refine ⟨18707038454861305585231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1596333948148164743273045 18707038454861305585231)
              ·
                rfl

theorem cell22_1475489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 8].length) (baseStart_1475489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475489 prefixEnd_1475489 := by exact prefixLift 1475489
  have htrace : WordTrace (prefixWord ++ tailWord_1475489) baseStart_1475489 baseEnd_1475489 := by
    simpa [prefixWord, tailWord_1475489, baseEnd_1475489] using wordTrace_append hprefix tailTrace_1475489
  have hstable : (prefixWord ++ tailWord_1475489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475489).length < 2 ^ (prefixWord ++ tailWord_1475489).sum := by decide
  have hdescent : baseEnd_1475489 < baseStart_1475489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475551 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 5]
def baseStart_1475551 : Nat := 118140960795 + 1475551 * 2 ^ 59
def prefixEnd_1475551 : Nat := 4983230072969 + 3 ^ 40 * 1475551 * 2
def baseEnd_1475551 : Nat := 168370420716102585250349

theorem tailTrace_1475551 : CollatzResearch.WordTrace tailWord_1475551 prefixEnd_1475551 168370420716102585250349 := by
  unfold tailWord_1475551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53817766277338205892842507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35878510851558803928561671 53817766277338205892842507)
  ·
    refine ⟨80726649416007308839263761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53817766277338205892842507 80726649416007308839263761)
    ·
      refine ⟨60544987062005481629447821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80726649416007308839263761 60544987062005481629447821)
      ·
        refine ⟨22704370148252055611042933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60544987062005481629447821 22704370148252055611042933)
        ·
          refine ⟨2128534701398630213535275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22704370148252055611042933 2128534701398630213535275)
          ·
            refine ⟨3192802052097945320302913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128534701398630213535275 3192802052097945320302913)
            ·
              refine ⟨2394601539073458990227185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192802052097945320302913 2394601539073458990227185)
              ·
                refine ⟨1795951154305094242670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394601539073458990227185 1795951154305094242670389)
                ·
                  refine ⟨168370420716102585250349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795951154305094242670389 168370420716102585250349)
                  ·
                    rfl

theorem cell22_1475551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].length) (baseStart_1475551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475551 prefixEnd_1475551 := by exact prefixLift 1475551
  have htrace : WordTrace (prefixWord ++ tailWord_1475551) baseStart_1475551 baseEnd_1475551 := by
    simpa [prefixWord, tailWord_1475551, baseEnd_1475551] using wordTrace_append hprefix tailTrace_1475551
  have hstable : (prefixWord ++ tailWord_1475551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475551).length < 2 ^ (prefixWord ++ tailWord_1475551).sum := by decide
  have hdescent : baseEnd_1475551 < baseStart_1475551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475566 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1475566 : Nat := 118140960795 + 1475566 * 2 ^ 59
def prefixEnd_1475566 : Nat := 4983230072969 + 3 ^ 40 * 1475566 * 2
def baseEnd_1475566 : Nat := 505116396954852716626001

theorem tailTrace_1475566 : CollatzResearch.WordTrace tailWord_1475566 prefixEnd_1475566 505116396954852716626001 := by
  unfold tailWord_1475566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727289171535482931829819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35878875581522575636425701 6727289171535482931829819)
  ·
    refine ⟨10090933757303224397744729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727289171535482931829819 10090933757303224397744729)
    ·
      refine ⟨7568200317977418298308547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10090933757303224397744729 7568200317977418298308547)
      ·
        refine ⟨11352300476966127447462821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568200317977418298308547 11352300476966127447462821)
        ·
          refine ⟨2128556339431148896399279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11352300476966127447462821 2128556339431148896399279)
          ·
            refine ⟨3192834509146723344598919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128556339431148896399279 3192834509146723344598919)
            ·
              refine ⟨4789251763720085016898379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192834509146723344598919 4789251763720085016898379)
              ·
                refine ⟨7183877645580127525347569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789251763720085016898379 7183877645580127525347569)
                ·
                  refine ⟨5387908234185095644010677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183877645580127525347569 5387908234185095644010677)
                  ·
                    refine ⟨505116396954852716626001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5387908234185095644010677 505116396954852716626001)
                    ·
                      rfl

theorem cell22_1475566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1475566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475566 prefixEnd_1475566 := by exact prefixLift 1475566
  have htrace : WordTrace (prefixWord ++ tailWord_1475566) baseStart_1475566 baseEnd_1475566 := by
    simpa [prefixWord, tailWord_1475566, baseEnd_1475566] using wordTrace_append hprefix tailTrace_1475566
  have hstable : (prefixWord ++ tailWord_1475566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475566).length < 2 ^ (prefixWord ++ tailWord_1475566).sum := by decide
  have hdescent : baseEnd_1475566 < baseStart_1475566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475596 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1475596 : Nat := 118140960795 + 1475596 * 2 ^ 59
def prefixEnd_1475596 : Nat := 4983230072969 + 3 ^ 40 * 1475596 * 2
def baseEnd_1475596 : Nat := 168375555522647546125303

theorem tailTrace_1475596 : CollatzResearch.WordTrace tailWord_1475596 prefixEnd_1475596 168375555522647546125303 := by
  unfold tailWord_1475596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909703781087589289115321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35879605041450119052153761 26909703781087589289115321)
  ·
    refine ⟨20182277835815691966836491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26909703781087589289115321 20182277835815691966836491)
    ·
      refine ⟨30273416753723537950254737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20182277835815691966836491 30273416753723537950254737)
      ·
        refine ⟨22705062565292653462691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30273416753723537950254737 22705062565292653462691053)
        ·
          refine ⟨8514398461984745048509145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22705062565292653462691053 8514398461984745048509145)
          ·
            refine ⟨6385798846488558786381859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8514398461984745048509145 6385798846488558786381859)
            ·
              refine ⟨9578698269732838179572789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385798846488558786381859 9578698269732838179572789)
              ·
                refine ⟨898002962787453579334949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9578698269732838179572789 898002962787453579334949)
                ·
                  refine ⟨168375555522647546125303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898002962787453579334949 168375555522647546125303)
                  ·
                    rfl

theorem cell22_1475596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1475596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475596 prefixEnd_1475596 := by exact prefixLift 1475596
  have htrace : WordTrace (prefixWord ++ tailWord_1475596) baseStart_1475596 baseEnd_1475596 := by
    simpa [prefixWord, tailWord_1475596, baseEnd_1475596] using wordTrace_append hprefix tailTrace_1475596
  have hstable : (prefixWord ++ tailWord_1475596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475596).length < 2 ^ (prefixWord ++ tailWord_1475596).sum := by decide
  have hdescent : baseEnd_1475596 < baseStart_1475596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475598 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1475598 : Nat := 118140960795 + 1475598 * 2 ^ 59
def prefixEnd_1475598 : Nat := 4983230072969 + 3 ^ 40 * 1475598 * 2
def baseEnd_1475598 : Nat := 505127351208815299825903

theorem tailTrace_1475598 : CollatzResearch.WordTrace tailWord_1475598 prefixEnd_1475598 505127351208815299825903 := by
  unfold tailWord_1475598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727435063520991614975431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35879653672111955279868965 6727435063520991614975431)
  ·
    refine ⟨10091152595281487422463147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727435063520991614975431 10091152595281487422463147)
    ·
      refine ⟨15136728892922231133694721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091152595281487422463147 15136728892922231133694721)
      ·
        refine ⟨11352546669691673350271041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15136728892922231133694721 11352546669691673350271041)
        ·
          refine ⟨8514410002268755012703281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11352546669691673350271041 8514410002268755012703281)
          ·
            refine ⟨6385807501701566259527461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8514410002268755012703281 6385807501701566259527461)
            ·
              refine ⟨1197338906569043673661399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6385807501701566259527461 1197338906569043673661399)
              ·
                refine ⟨1796008359853565510492099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197338906569043673661399 1796008359853565510492099)
                ·
                  refine ⟨2694012539780348265738149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796008359853565510492099 2694012539780348265738149)
                  ·
                    refine ⟨505127351208815299825903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694012539780348265738149 505127351208815299825903)
                    ·
                      rfl

theorem cell22_1475598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1475598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475598 prefixEnd_1475598 := by exact prefixLift 1475598
  have htrace : WordTrace (prefixWord ++ tailWord_1475598) baseStart_1475598 baseEnd_1475598 := by
    simpa [prefixWord, tailWord_1475598, baseEnd_1475598] using wordTrace_append hprefix tailTrace_1475598
  have hstable : (prefixWord ++ tailWord_1475598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475598).length < 2 ^ (prefixWord ++ tailWord_1475598).sum := by decide
  have hdescent : baseEnd_1475598 < baseStart_1475598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475602 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1475602 : Nat := 118140960795 + 1475602 * 2 ^ 59
def prefixEnd_1475602 : Nat := 4983230072969 + 3 ^ 40 * 1475602 * 2
def baseEnd_1475602 : Nat := 168376240163520207575297

theorem tailTrace_1475602 : CollatzResearch.WordTrace tailWord_1475602 prefixEnd_1475602 168376240163520207575297 := by
  unfold tailWord_1475602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13454906600038360400737265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35879750933435627735299373 13454906600038360400737265)
  ·
    refine ⟨10091179950028770300552949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13454906600038360400737265 10091179950028770300552949)
    ·
      refine ⟨946048120315197215676839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10091179950028770300552949 946048120315197215676839)
      ·
        refine ⟨1419072180472795823515259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946048120315197215676839 1419072180472795823515259)
        ·
          refine ⟨2128608270709193735272889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419072180472795823515259 2128608270709193735272889)
          ·
            refine ⟨1596456203031895301454667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2128608270709193735272889 1596456203031895301454667)
            ·
              refine ⟨2394684304547842952182001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596456203031895301454667 2394684304547842952182001)
              ·
                refine ⟨1796013228410882214136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394684304547842952182001 1796013228410882214136501)
                ·
                  refine ⟨168376240163520207575297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1796013228410882214136501 168376240163520207575297)
                  ·
                    rfl

theorem cell22_1475602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1475602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475602 prefixEnd_1475602 := by exact prefixLift 1475602
  have htrace : WordTrace (prefixWord ++ tailWord_1475602) baseStart_1475602 baseEnd_1475602 := by
    simpa [prefixWord, tailWord_1475602, baseEnd_1475602] using wordTrace_append hprefix tailTrace_1475602
  have hstable : (prefixWord ++ tailWord_1475602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475602).length < 2 ^ (prefixWord ++ tailWord_1475602).sum := by decide
  have hdescent : baseEnd_1475602 < baseStart_1475602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475609 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_1475609 : Nat := 118140960795 + 1475609 * 2 ^ 59
def prefixEnd_1475609 : Nat := 4983230072969 + 3 ^ 40 * 1475609 * 2
def baseEnd_1475609 : Nat := 505131116733614937800869

theorem tailTrace_1475609 : CollatzResearch.WordTrace tailWord_1475609 prefixEnd_1475609 505131116733614937800869 := by
  unfold tailWord_1475609
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819881711128081798453881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35879921140752054532302587 53819881711128081798453881)
  ·
    refine ⟨40364911283346061348840411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53819881711128081798453881 40364911283346061348840411)
    ·
      refine ⟨60547366925019092023260617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40364911283346061348840411 60547366925019092023260617)
      ·
        refine ⟨45410525193764319017445463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60547366925019092023260617 45410525193764319017445463)
        ·
          refine ⟨68115787790646478526168195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45410525193764319017445463 68115787790646478526168195)
          ·
            refine ⟨102173681685969717789252293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68115787790646478526168195 102173681685969717789252293)
            ·
              refine ⟨19157565316119322085484805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102173681685969717789252293 19157565316119322085484805)
              ·
                refine ⟨3592043496772372891028401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19157565316119322085484805 3592043496772372891028401)
                ·
                  refine ⟨2694032622579279668271301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592043496772372891028401 2694032622579279668271301)
                  ·
                    refine ⟨505131116733614937800869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694032622579279668271301 505131116733614937800869)
                    ·
                      rfl

theorem cell22_1475609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_1475609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475609 prefixEnd_1475609 := by exact prefixLift 1475609
  have htrace : WordTrace (prefixWord ++ tailWord_1475609) baseStart_1475609 baseEnd_1475609 := by
    simpa [prefixWord, tailWord_1475609, baseEnd_1475609] using wordTrace_append hprefix tailTrace_1475609
  have hstable : (prefixWord ++ tailWord_1475609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475609).length < 2 ^ (prefixWord ++ tailWord_1475609).sum := by decide
  have hdescent : baseEnd_1475609 < baseStart_1475609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475628 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_1475628 : Nat := 118140960795 + 1475628 * 2 ^ 59
def prefixEnd_1475628 : Nat := 4983230072969 + 3 ^ 40 * 1475628 * 2
def baseEnd_1475628 : Nat := 505137620821905221575811

theorem tailTrace_1475628 : CollatzResearch.WordTrace tailWord_1475628 prefixEnd_1475628 505137620821905221575811 := by
  unfold tailWord_1475628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26910287349029624021697769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35880383132039498695597025 26910287349029624021697769)
  ·
    refine ⟨20182715511772218016273327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26910287349029624021697769 20182715511772218016273327)
    ·
      refine ⟨30274073267658327024409991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20182715511772218016273327 30274073267658327024409991)
      ·
        refine ⟨45411109901487490536614987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30274073267658327024409991 45411109901487490536614987)
        ·
          refine ⟨68116664852231235804922481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45411109901487490536614987 68116664852231235804922481)
          ·
            refine ⟨51087498639173426853691861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68116664852231235804922481 51087498639173426853691861)
            ·
              refine ⟨1197363249355627191883403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51087498639173426853691861 1197363249355627191883403)
              ·
                refine ⟨1796044874033440787825105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197363249355627191883403 1796044874033440787825105)
                ·
                  refine ⟨1347033655525080590868829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796044874033440787825105 1347033655525080590868829)
                  ·
                    refine ⟨505137620821905221575811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347033655525080590868829 505137620821905221575811)
                    ·
                      rfl

theorem cell22_1475628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_1475628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475628 prefixEnd_1475628 := by exact prefixLift 1475628
  have htrace : WordTrace (prefixWord ++ tailWord_1475628) baseStart_1475628 baseEnd_1475628 := by
    simpa [prefixWord, tailWord_1475628, baseEnd_1475628] using wordTrace_append hprefix tailTrace_1475628
  have hstable : (prefixWord ++ tailWord_1475628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475628).length < 2 ^ (prefixWord ++ tailWord_1475628).sum := by decide
  have hdescent : baseEnd_1475628 < baseStart_1475628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475641 : List Nat := [1, 2, 1, 5, 2, 1, 4, 6]
def baseStart_1475641 : Nat := 118140960795 + 1475641 * 2 ^ 59
def prefixEnd_1475641 : Nat := 4983230072969 + 3 ^ 40 * 1475641 * 2
def baseEnd_1475641 : Nat := 56126896776397502333419

theorem tailTrace_1475641 : CollatzResearch.WordTrace tailWord_1475641 prefixEnd_1475641 56126896776397502333419 := by
  unfold tailWord_1475641
  simp only [CollatzResearch.WordTrace]
  refine ⟨53821048847012151263618777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35880699231341434175745851 53821048847012151263618777)
  ·
    refine ⟨40365786635259113447714083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53821048847012151263618777 40365786635259113447714083)
    ·
      refine ⟨60548679952888670171571125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40365786635259113447714083 60548679952888670171571125)
      ·
        refine ⟨5676438745583312828584793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60548679952888670171571125 5676438745583312828584793)
        ·
          refine ⟨4257329059187484621438595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5676438745583312828584793 4257329059187484621438595)
          ·
            refine ⟨6385993588781226932157893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257329059187484621438595 6385993588781226932157893)
            ·
              refine ⟨1197373797896480049779605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6385993588781226932157893 1197373797896480049779605)
              ·
                refine ⟨56126896776397502333419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1197373797896480049779605 56126896776397502333419)
                ·
                  rfl

theorem cell22_1475641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 6].length) (baseStart_1475641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475641 prefixEnd_1475641 := by exact prefixLift 1475641
  have htrace : WordTrace (prefixWord ++ tailWord_1475641) baseStart_1475641 baseEnd_1475641 := by
    simpa [prefixWord, tailWord_1475641, baseEnd_1475641] using wordTrace_append hprefix tailTrace_1475641
  have hstable : (prefixWord ++ tailWord_1475641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475641).length < 2 ^ (prefixWord ++ tailWord_1475641).sum := by decide
  have hdescent : baseEnd_1475641 < baseStart_1475641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475669 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 7]
def baseStart_1475669 : Nat := 118140960795 + 1475669 * 2 ^ 59
def prefixEnd_1475669 : Nat := 4983230072969 + 3 ^ 40 * 1475669 * 2
def baseEnd_1475669 : Nat := 168383885319931593766895

theorem tailTrace_1475669 : CollatzResearch.WordTrace tailWord_1475669 prefixEnd_1475669 168383885319931593766895 := by
  unfold tailWord_1475669
  simp only [CollatzResearch.WordTrace]
  refine ⟨53822070090910712045638061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35881380060607141363758707 53822070090910712045638061)
  ·
    refine ⟨20183276284091517017114273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53822070090910712045638061 20183276284091517017114273)
    ·
      refine ⟨15137457213068637762835705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20183276284091517017114273 15137457213068637762835705)
      ·
        refine ⟨11353092909801478322126779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15137457213068637762835705 11353092909801478322126779)
        ·
          refine ⟨17029639364702217483190169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353092909801478322126779 17029639364702217483190169)
          ·
            refine ⟨12772229523526663112392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17029639364702217483190169 12772229523526663112392627)
            ·
              refine ⟨19158344285289994668588941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772229523526663112392627 19158344285289994668588941)
              ·
                refine ⟨7184379106983748000720853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19158344285289994668588941 7184379106983748000720853)
                ·
                  refine ⟨168383885319931593766895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7184379106983748000720853 168383885319931593766895)
                  ·
                    rfl

theorem cell22_1475669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_1475669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475669 prefixEnd_1475669 := by exact prefixLift 1475669
  have htrace : WordTrace (prefixWord ++ tailWord_1475669) baseStart_1475669 baseEnd_1475669 := by
    simpa [prefixWord, tailWord_1475669, baseEnd_1475669] using wordTrace_append hprefix tailTrace_1475669
  have hstable : (prefixWord ++ tailWord_1475669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475669).length < 2 ^ (prefixWord ++ tailWord_1475669).sum := by decide
  have hdescent : baseEnd_1475669 < baseStart_1475669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475684 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1475684 : Nat := 118140960795 + 1475684 * 2 ^ 59
def prefixEnd_1475684 : Nat := 4983230072969 + 3 ^ 40 * 1475684 * 2
def baseEnd_1475684 : Nat := 505156790766339742175639

theorem tailTrace_1475684 : CollatzResearch.WordTrace tailWord_1475684 prefixEnd_1475684 505156790766339742175639 := by
  unfold tailWord_1475684
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911308592928184803717053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35881744790570913071622737 26911308592928184803717053)
  ·
    refine ⟨10091740722348069301393895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26911308592928184803717053 10091740722348069301393895)
    ·
      refine ⟨15137611083522103952090843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091740722348069301393895 15137611083522103952090843)
      ·
        refine ⟨22706416625283155928136265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15137611083522103952090843 22706416625283155928136265)
        ·
          refine ⟨17029812468962366946102199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22706416625283155928136265 17029812468962366946102199)
          ·
            refine ⟨25544718703443550419153299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029812468962366946102199 25544718703443550419153299)
            ·
              refine ⟨38317078055165325628729949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25544718703443550419153299 38317078055165325628729949)
              ·
                refine ⟨14368904270686997110773731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38317078055165325628729949 14368904270686997110773731)
                ·
                  refine ⟨21553356406030495666160597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14368904270686997110773731 21553356406030495666160597)
                  ·
                    refine ⟨505156790766339742175639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21553356406030495666160597 505156790766339742175639)
                    ·
                      rfl

theorem cell22_1475684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1475684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475684 prefixEnd_1475684 := by exact prefixLift 1475684
  have htrace : WordTrace (prefixWord ++ tailWord_1475684) baseStart_1475684 baseEnd_1475684 := by
    simpa [prefixWord, tailWord_1475684, baseEnd_1475684] using wordTrace_append hprefix tailTrace_1475684
  have hstable : (prefixWord ++ tailWord_1475684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475684).length < 2 ^ (prefixWord ++ tailWord_1475684).sum := by decide
  have hdescent : baseEnd_1475684 < baseStart_1475684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475759 : List Nat := [1, 1, 2, 1, 2, 3, 2, 10]
def baseStart_1475759 : Nat := 118140960795 + 1475759 * 2 ^ 59
def prefixEnd_1475759 : Nat := 4983230072969 + 3 ^ 40 * 1475759 * 2
def baseEnd_1475759 : Nat := 56131384977673838505601

theorem tailTrace_1475759 : CollatzResearch.WordTrace tailWord_1475759 prefixEnd_1475759 56131384977673838505601 := by
  unfold tailWord_1475759
  simp only [CollatzResearch.WordTrace]
  refine ⟨53825352660584657416414331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35883568440389771610942887 53825352660584657416414331)
  ·
    refine ⟨80738028990876986124621497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53825352660584657416414331 80738028990876986124621497)
    ·
      refine ⟨60553521743157739593466123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80738028990876986124621497 60553521743157739593466123)
      ·
        refine ⟨90830282614736609390199185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60553521743157739593466123 90830282614736609390199185)
        ·
          refine ⟨68122711961052457042649389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90830282614736609390199185 68122711961052457042649389)
          ·
            refine ⟨25546016985394671390993521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68122711961052457042649389 25546016985394671390993521)
            ·
              refine ⟨19159512739046003543245141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25546016985394671390993521 19159512739046003543245141)
              ·
                refine ⟨56131384977673838505601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19159512739046003543245141 56131384977673838505601)
                ·
                  rfl

theorem cell22_1475759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 10].length) (baseStart_1475759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475759 prefixEnd_1475759 := by exact prefixLift 1475759
  have htrace : WordTrace (prefixWord ++ tailWord_1475759) baseStart_1475759 baseEnd_1475759 := by
    simpa [prefixWord, tailWord_1475759, baseEnd_1475759] using wordTrace_append hprefix tailTrace_1475759
  have hstable : (prefixWord ++ tailWord_1475759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475759).length < 2 ^ (prefixWord ++ tailWord_1475759).sum := by decide
  have hdescent : baseEnd_1475759 < baseStart_1475759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475776 : List Nat := [2, 1, 1, 2, 6, 1, 9]
def baseStart_1475776 : Nat := 118140960795 + 1475776 * 2 ^ 59
def prefixEnd_1475776 : Nat := 4983230072969 + 3 ^ 40 * 1475776 * 2
def baseEnd_1475776 : Nat := 18710677194314154402791

theorem tailTrace_1475776 : CollatzResearch.WordTrace tailWord_1475776 prefixEnd_1475776 18710677194314154402791 := by
  unfold tailWord_1475776
  simp only [CollatzResearch.WordTrace]
  refine ⟨26912986350761534659891591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35883981801015379546522121 26912986350761534659891591)
  ·
    refine ⟨40369479526142301989837387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26912986350761534659891591 40369479526142301989837387)
    ·
      refine ⟨60554219289213452984756081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40369479526142301989837387 60554219289213452984756081)
      ·
        refine ⟨45415664466910089738567061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60554219289213452984756081 45415664466910089738567061)
        ·
          refine ⟨2128859271886410456495331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45415664466910089738567061 2128859271886410456495331)
          ·
            refine ⟨3193288907829615684742997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128859271886410456495331 3193288907829615684742997)
            ·
              refine ⟨18710677194314154402791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3193288907829615684742997 18710677194314154402791)
              ·
                rfl

theorem cell22_1475776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 9].length) (baseStart_1475776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475776 prefixEnd_1475776 := by exact prefixLift 1475776
  have htrace : WordTrace (prefixWord ++ tailWord_1475776) baseStart_1475776 baseEnd_1475776 := by
    simpa [prefixWord, tailWord_1475776, baseEnd_1475776] using wordTrace_append hprefix tailTrace_1475776
  have hstable : (prefixWord ++ tailWord_1475776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475776).length < 2 ^ (prefixWord ++ tailWord_1475776).sum := by decide
  have hdescent : baseEnd_1475776 < baseStart_1475776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475780 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1475780 : Nat := 118140960795 + 1475780 * 2 ^ 59
def prefixEnd_1475780 : Nat := 4983230072969 + 3 ^ 40 * 1475780 * 2
def baseEnd_1475780 : Nat := 505189653528227491775345

theorem tailTrace_1475780 : CollatzResearch.WordTrace tailWord_1475780 prefixEnd_1475780 505189653528227491775345 := by
  unfold tailWord_1475780
  simp only [CollatzResearch.WordTrace]
  refine ⟨26913059296754289001464397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35884079062339052001952529 26913059296754289001464397)
  ·
    refine ⟨10092397236282858375549149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26913059296754289001464397 10092397236282858375549149)
    ·
      refine ⟨3784648963606071890830931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10092397236282858375549149 3784648963606071890830931)
      ·
        refine ⟨5676973445409107836246397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784648963606071890830931 5676973445409107836246397)
        ·
          refine ⟨2128865042028415438592399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5676973445409107836246397 2128865042028415438592399)
          ·
            refine ⟨3193297563042623157888599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128865042028415438592399 3193297563042623157888599)
            ·
              refine ⟨4789946344563934736832899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193297563042623157888599 4789946344563934736832899)
              ·
                refine ⟨7184919516845902105249349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789946344563934736832899 7184919516845902105249349)
                ·
                  refine ⟨1347172409408606644734253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7184919516845902105249349 1347172409408606644734253)
                  ·
                    refine ⟨505189653528227491775345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347172409408606644734253 505189653528227491775345)
                    ·
                      rfl

theorem cell22_1475780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1475780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475780 prefixEnd_1475780 := by exact prefixLift 1475780
  have htrace : WordTrace (prefixWord ++ tailWord_1475780) baseStart_1475780 baseEnd_1475780 := by
    simpa [prefixWord, tailWord_1475780, baseEnd_1475780] using wordTrace_append hprefix tailTrace_1475780
  have hstable : (prefixWord ++ tailWord_1475780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475780).length < 2 ^ (prefixWord ++ tailWord_1475780).sum := by decide
  have hdescent : baseEnd_1475780 < baseStart_1475780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475797 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1475797 : Nat := 118140960795 + 1475797 * 2 ^ 59
def prefixEnd_1475797 : Nat := 4983230072969 + 3 ^ 40 * 1475797 * 2
def baseEnd_1475797 : Nat := 505195472975645114100293

theorem tailTrace_1475797 : CollatzResearch.WordTrace tailWord_1475797 prefixEnd_1475797 505195472975645114100293 := by
  unfold tailWord_1475797
  simp only [CollatzResearch.WordTrace]
  refine ⟨53826738634446989906297645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35884492422964659937531763 53826738634446989906297645)
  ·
    refine ⟨20185026987917621214861617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53826738634446989906297645 20185026987917621214861617)
    ·
      refine ⟨15138770240938215911146213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20185026987917621214861617 15138770240938215911146213)
      ·
        refine ⟨2838519420175915483339915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15138770240938215911146213 2838519420175915483339915)
        ·
          refine ⟨4257779130263873225009873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838519420175915483339915 4257779130263873225009873)
          ·
            refine ⟨3193334347697904918757405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257779130263873225009873 3193334347697904918757405)
            ·
              refine ⟨1197500380386714344534027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3193334347697904918757405 1197500380386714344534027)
              ·
                refine ⟨1796250570580071516801041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197500380386714344534027 1796250570580071516801041)
                ·
                  refine ⟨1347187927935053637600781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796250570580071516801041 1347187927935053637600781)
                  ·
                    refine ⟨505195472975645114100293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347187927935053637600781 505195472975645114100293)
                    ·
                      rfl

theorem cell22_1475797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1475797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475797 prefixEnd_1475797 := by exact prefixLift 1475797
  have htrace : WordTrace (prefixWord ++ tailWord_1475797) baseStart_1475797 baseEnd_1475797 := by
    simpa [prefixWord, tailWord_1475797, baseEnd_1475797] using wordTrace_append hprefix tailTrace_1475797
  have hstable : (prefixWord ++ tailWord_1475797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475797).length < 2 ^ (prefixWord ++ tailWord_1475797).sum := by decide
  have hdescent : baseEnd_1475797 < baseStart_1475797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475808 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_1475808 : Nat := 118140960795 + 1475808 * 2 ^ 59
def prefixEnd_1475808 : Nat := 4983230072969 + 3 ^ 40 * 1475808 * 2
def baseEnd_1475808 : Nat := 505199238500444752075259

theorem tailTrace_1475808 : CollatzResearch.WordTrace tailWord_1475808 prefixEnd_1475808 505199238500444752075259 := by
  unfold tailWord_1475808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26913569918703569392474039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35884759891604759189965385 26913569918703569392474039)
  ·
    refine ⟨40370354878055354088711059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26913569918703569392474039 40370354878055354088711059)
    ·
      refine ⟨60555532317083031133066589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40370354878055354088711059 60555532317083031133066589)
      ·
        refine ⟨22708324618906136674899971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60555532317083031133066589 22708324618906136674899971)
        ·
          refine ⟨34062486928359205012349957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22708324618906136674899971 34062486928359205012349957)
          ·
            refine ⟨6386716299067350939815617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34062486928359205012349957 6386716299067350939815617)
            ·
              refine ⟨4790037224300513204861713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386716299067350939815617 4790037224300513204861713)
              ·
                refine ⟨3592527918225384903646285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790037224300513204861713 3592527918225384903646285)
                ·
                  refine ⟨1347197969334519338867357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3592527918225384903646285 1347197969334519338867357)
                  ·
                    refine ⟨505199238500444752075259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347197969334519338867357 505199238500444752075259)
                    ·
                      rfl

theorem cell22_1475808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_1475808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475808 prefixEnd_1475808 := by exact prefixLift 1475808
  have htrace : WordTrace (prefixWord ++ tailWord_1475808) baseStart_1475808 baseEnd_1475808 := by
    simpa [prefixWord, tailWord_1475808, baseEnd_1475808] using wordTrace_append hprefix tailTrace_1475808
  have hstable : (prefixWord ++ tailWord_1475808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475808).length < 2 ^ (prefixWord ++ tailWord_1475808).sum := by decide
  have hdescent : baseEnd_1475808 < baseStart_1475808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475838 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1475838 : Nat := 118140960795 + 1475838 * 2 ^ 59
def prefixEnd_1475838 : Nat := 4983230072969 + 3 ^ 40 * 1475838 * 2
def baseEnd_1475838 : Nat := 168403169371178224608389

theorem tailTrace_1475838 : CollatzResearch.WordTrace tailWord_1475838 prefixEnd_1475838 168403169371178224608389 := by
  unfold tailWord_1475838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728529253412306738567521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35885489351532302605693445 6728529253412306738567521)
  ·
    refine ⟨5046396940059230053925641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6728529253412306738567521 5046396940059230053925641)
    ·
      refine ⟨3784797705044422540444231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5046396940059230053925641 3784797705044422540444231)
      ·
        refine ⟨5677196557566633810666347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784797705044422540444231 5677196557566633810666347)
        ·
          refine ⟨8515794836349950715999521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677196557566633810666347 8515794836349950715999521)
          ·
            refine ⟨6386846127262463036999641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515794836349950715999521 6386846127262463036999641)
            ·
              refine ⟨4790134595446847277749731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386846127262463036999641 4790134595446847277749731)
              ·
                refine ⟨7185201893170270916624597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790134595446847277749731 7185201893170270916624597)
                ·
                  refine ⟨168403169371178224608389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7185201893170270916624597 168403169371178224608389)
                  ·
                    rfl

theorem cell22_1475838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1475838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475838 prefixEnd_1475838 := by exact prefixLift 1475838
  have htrace : WordTrace (prefixWord ++ tailWord_1475838) baseStart_1475838 baseEnd_1475838 := by
    simpa [prefixWord, tailWord_1475838, baseEnd_1475838] using wordTrace_append hprefix tailTrace_1475838
  have hstable : (prefixWord ++ tailWord_1475838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475838).length < 2 ^ (prefixWord ++ tailWord_1475838).sum := by decide
  have hdescent : baseEnd_1475838 < baseStart_1475838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475896 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1475896 : Nat := 118140960795 + 1475896 * 2 ^ 59
def prefixEnd_1475896 : Nat := 4983230072969 + 3 ^ 40 * 1475896 * 2
def baseEnd_1475896 : Nat := 505229362698841855874989

theorem tailTrace_1475896 : CollatzResearch.WordTrace tailWord_1475896 prefixEnd_1475896 505229362698841855874989 := by
  unfold tailWord_1475896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915174730544164907075771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35886899640725553209434361 26915174730544164907075771)
  ·
    refine ⟨40372762095816247360613657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26915174730544164907075771 40372762095816247360613657)
    ·
      refine ⟨30279571571862185520460243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40372762095816247360613657 30279571571862185520460243)
      ·
        refine ⟨45419357357793278280690365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30279571571862185520460243 45419357357793278280690365)
        ·
          refine ⟨17032259009172479355258887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45419357357793278280690365 17032259009172479355258887)
          ·
            refine ⟨25548388513758719032888331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17032259009172479355258887 25548388513758719032888331)
            ·
              refine ⟨38322582770638078549332497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548388513758719032888331 38322582770638078549332497)
              ·
                refine ⟨28741937077978558911999373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38322582770638078549332497 28741937077978558911999373)
                ·
                  refine ⟨10778226404241959591999765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28741937077978558911999373 10778226404241959591999765)
                  ·
                    refine ⟨505229362698841855874989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10778226404241959591999765 505229362698841855874989)
                    ·
                      rfl

theorem cell22_1475896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1475896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475896 prefixEnd_1475896 := by exact prefixLift 1475896
  have htrace : WordTrace (prefixWord ++ tailWord_1475896) baseStart_1475896 baseEnd_1475896 := by
    simpa [prefixWord, tailWord_1475896, baseEnd_1475896] using wordTrace_append hprefix tailTrace_1475896
  have hstable : (prefixWord ++ tailWord_1475896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475896).length < 2 ^ (prefixWord ++ tailWord_1475896).sum := by decide
  have hdescent : baseEnd_1475896 < baseStart_1475896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475900 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_1475900 : Nat := 118140960795 + 1475900 * 2 ^ 59
def prefixEnd_1475900 : Nat := 4983230072969 + 3 ^ 40 * 1475900 * 2
def baseEnd_1475900 : Nat := 168410243993529059591659

theorem tailTrace_1475900 : CollatzResearch.WordTrace tailWord_1475900 prefixEnd_1475900 168410243993529059591659 := by
  unfold tailWord_1475900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915247676536919248648577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35886996902049225664864769 26915247676536919248648577)
  ·
    refine ⟨20186435757402689436486433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26915247676536919248648577 20186435757402689436486433)
    ·
      refine ⟨15139826818052017077364825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20186435757402689436486433 15139826818052017077364825)
      ·
        refine ⟨11354870113539012808023619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15139826818052017077364825 11354870113539012808023619)
        ·
          refine ⟨17032305170308519212035429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354870113539012808023619 17032305170308519212035429)
          ·
            refine ⟨3193557219432847352256643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17032305170308519212035429 3193557219432847352256643)
            ·
              refine ⟨4790335829149271028384965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193557219432847352256643 4790335829149271028384965)
              ·
                refine ⟨898187967965488317822181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4790335829149271028384965 898187967965488317822181)
                ·
                  refine ⟨168410243993529059591659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898187967965488317822181 168410243993529059591659)
                  ·
                    rfl

theorem cell22_1475900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_1475900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475900 prefixEnd_1475900 := by exact prefixLift 1475900
  have htrace : WordTrace (prefixWord ++ tailWord_1475900) baseStart_1475900 baseEnd_1475900 := by
    simpa [prefixWord, tailWord_1475900, baseEnd_1475900] using wordTrace_append hprefix tailTrace_1475900
  have hstable : (prefixWord ++ tailWord_1475900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475900).length < 2 ^ (prefixWord ++ tailWord_1475900).sum := by decide
  have hdescent : baseEnd_1475900 < baseStart_1475900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475917 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1475917 : Nat := 118140960795 + 1475917 * 2 ^ 59
def prefixEnd_1475917 : Nat := 4983230072969 + 3 ^ 40 * 1475917 * 2
def baseEnd_1475917 : Nat := 168412183809334933699975

theorem tailTrace_1475917 : CollatzResearch.WordTrace tailWord_1475917 prefixEnd_1475917 168412183809334933699975 := by
  unfold tailWord_1475917
  simp only [CollatzResearch.WordTrace]
  refine ⟨53831115394012250400666005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35887410262674833600444003 53831115394012250400666005)
  ·
    refine ⟨2523333534094324237531219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53831115394012250400666005 2523333534094324237531219)
    ·
      refine ⟨3785000301141486356296829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523333534094324237531219 3785000301141486356296829)
      ·
        refine ⟨1419375112928057383611311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3785000301141486356296829 1419375112928057383611311)
        ·
          refine ⟨2129062669392086075416967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419375112928057383611311 2129062669392086075416967)
          ·
            refine ⟨3193594004088129113125451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129062669392086075416967 3193594004088129113125451)
            ·
              refine ⟨4790391006132193669688177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193594004088129113125451 4790391006132193669688177)
              ·
                refine ⟨3592793254599145252266133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790391006132193669688177 3592793254599145252266133)
                ·
                  refine ⟨168412183809334933699975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3592793254599145252266133 168412183809334933699975)
                  ·
                    rfl

theorem cell22_1475917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1475917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475917 prefixEnd_1475917 := by exact prefixLift 1475917
  have htrace : WordTrace (prefixWord ++ tailWord_1475917) baseStart_1475917 baseEnd_1475917 := by
    simpa [prefixWord, tailWord_1475917, baseEnd_1475917] using wordTrace_append hprefix tailTrace_1475917
  have hstable : (prefixWord ++ tailWord_1475917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475917).length < 2 ^ (prefixWord ++ tailWord_1475917).sum := by decide
  have hdescent : baseEnd_1475917 < baseStart_1475917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475928 : List Nat := [2, 1, 2, 2, 1, 1, 7, 6]
def baseStart_1475928 : Nat := 118140960795 + 1475928 * 2 ^ 59
def prefixEnd_1475928 : Nat := 4983230072969 + 3 ^ 40 * 1475928 * 2
def baseEnd_1475928 : Nat := 56137812994756048786099

theorem tailTrace_1475928 : CollatzResearch.WordTrace tailWord_1475928 prefixEnd_1475928 56137812994756048786099 := by
  unfold tailWord_1475928
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915758298486199639658219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35887677731314932852877625 26915758298486199639658219)
  ·
    refine ⟨40373637447729299459487329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26915758298486199639658219 40373637447729299459487329)
    ·
      refine ⟨30280228085796974594615497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40373637447729299459487329 30280228085796974594615497)
      ·
        refine ⟨22710171064347730945961623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30280228085796974594615497 22710171064347730945961623)
        ·
          refine ⟨34065256596521596418942435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22710171064347730945961623 34065256596521596418942435)
          ·
            refine ⟨51097884894782394628413653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34065256596521596418942435 51097884894782394628413653)
            ·
              refine ⟨1197606677221462374103445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51097884894782394628413653 1197606677221462374103445)
              ·
                refine ⟨56137812994756048786099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1197606677221462374103445 56137812994756048786099)
                ·
                  rfl

theorem cell22_1475928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_1475928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475928 prefixEnd_1475928 := by exact prefixLift 1475928
  have htrace : WordTrace (prefixWord ++ tailWord_1475928) baseStart_1475928 baseEnd_1475928 := by
    simpa [prefixWord, tailWord_1475928, baseEnd_1475928] using wordTrace_append hprefix tailTrace_1475928
  have hstable : (prefixWord ++ tailWord_1475928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475928).length < 2 ^ (prefixWord ++ tailWord_1475928).sum := by decide
  have hdescent : baseEnd_1475928 < baseStart_1475928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475966 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1475966 : Nat := 118140960795 + 1475966 * 2 ^ 59
def prefixEnd_1475966 : Nat := 4983230072969 + 3 ^ 40 * 1475966 * 2
def baseEnd_1475966 : Nat := 505253325129385006624775

theorem tailTrace_1475966 : CollatzResearch.WordTrace tailWord_1475966 prefixEnd_1475966 505253325129385006624775 := by
  unfold tailWord_1475966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6729112821354341471149969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35888601713889821179466501 6729112821354341471149969)
  ·
    refine ⟨5046834616015756103362477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6729112821354341471149969 5046834616015756103362477)
    ·
      refine ⟨1892562981005908538760929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5046834616015756103362477 1892562981005908538760929)
      ·
        refine ⟨1419422235754431404070697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892562981005908538760929 1419422235754431404070697)
        ·
          refine ⟨1064566676815823553053023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419422235754431404070697 1064566676815823553053023)
          ·
            refine ⟨1596850015223735329579535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064566676815823553053023 1596850015223735329579535)
            ·
              refine ⟨2395275022835602994369303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596850015223735329579535 2395275022835602994369303)
              ·
                refine ⟨3592912534253404491553955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395275022835602994369303 3592912534253404491553955)
                ·
                  refine ⟨5389368801380106737330933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592912534253404491553955 5389368801380106737330933)
                  ·
                    refine ⟨505253325129385006624775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5389368801380106737330933 505253325129385006624775)
                    ·
                      rfl

theorem cell22_1475966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1475966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475966 prefixEnd_1475966 := by exact prefixLift 1475966
  have htrace : WordTrace (prefixWord ++ tailWord_1475966) baseStart_1475966 baseEnd_1475966 := by
    simpa [prefixWord, tailWord_1475966, baseEnd_1475966] using wordTrace_append hprefix tailTrace_1475966
  have hstable : (prefixWord ++ tailWord_1475966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475966).length < 2 ^ (prefixWord ++ tailWord_1475966).sum := by decide
  have hdescent : baseEnd_1475966 < baseStart_1475966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475973 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 5]
def baseStart_1475973 : Nat := 118140960795 + 1475973 * 2 ^ 59
def prefixEnd_1475973 : Nat := 4983230072969 + 3 ^ 40 * 1475973 * 2
def baseEnd_1475973 : Nat := 168418573790813107233251

theorem tailTrace_1475973 : CollatzResearch.WordTrace tailWord_1475973 prefixEnd_1475973 168418573790813107233251 := by
  unfold tailWord_1475973
  simp only [CollatzResearch.WordTrace]
  refine ⟨53833157881809371964704573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35888771921206247976469715 53833157881809371964704573)
  ·
    refine ⟨20187434205678514486764215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53833157881809371964704573 20187434205678514486764215)
    ·
      refine ⟨30281151308517771730146323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20187434205678514486764215 30281151308517771730146323)
      ·
        refine ⟨45421726962776657595219485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30281151308517771730146323 45421726962776657595219485)
        ·
          refine ⟨17033147611041246598207307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45421726962776657595219485 17033147611041246598207307)
          ·
            refine ⟨25549721416561869897310961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17033147611041246598207307 25549721416561869897310961)
            ·
              refine ⟨19162291062421402422983221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25549721416561869897310961 19162291062421402422983221)
              ·
                refine ⟨1796464787102006477154677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19162291062421402422983221 1796464787102006477154677)
                ·
                  refine ⟨168418573790813107233251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1796464787102006477154677 168418573790813107233251)
                  ·
                    rfl

theorem cell22_1475973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_1475973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1475973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1475973 prefixEnd_1475973 := by exact prefixLift 1475973
  have htrace : WordTrace (prefixWord ++ tailWord_1475973) baseStart_1475973 baseEnd_1475973 := by
    simpa [prefixWord, tailWord_1475973, baseEnd_1475973] using wordTrace_append hprefix tailTrace_1475973
  have hstable : (prefixWord ++ tailWord_1475973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475973).length < 2 ^ (prefixWord ++ tailWord_1475973).sum := by decide
  have hdescent : baseEnd_1475973 < baseStart_1475973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476018 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1476018 : Nat := 118140960795 + 1476018 * 2 ^ 59
def prefixEnd_1476018 : Nat := 4983230072969 + 3 ^ 40 * 1476018 * 2
def baseEnd_1476018 : Nat := 168423708597358068108205

theorem tailTrace_1476018 : CollatzResearch.WordTrace tailWord_1476018 prefixEnd_1476018 168423708597358068108205 := by
  unfold tailWord_1476018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458699791661586162523177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35889866111097563100061805 13458699791661586162523177)
  ·
    refine ⟨10094024843746189621892383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13458699791661586162523177 10094024843746189621892383)
    ·
      refine ⟨15141037265619284432838575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10094024843746189621892383 15141037265619284432838575)
      ·
        refine ⟨22711555898428926649257863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15141037265619284432838575 22711555898428926649257863)
        ·
          refine ⟨34067333847643389973886795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22711555898428926649257863 34067333847643389973886795)
          ·
            refine ⟨51101000771465084960830193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34067333847643389973886795 51101000771465084960830193)
            ·
              refine ⟨38325750578598813720622645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51101000771465084960830193 38325750578598813720622645)
              ·
                refine ⟨3593039116743638786308373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38325750578598813720622645 3593039116743638786308373)
                ·
                  refine ⟨168423708597358068108205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3593039116743638786308373 168423708597358068108205)
                  ·
                    rfl

theorem cell22_1476018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1476018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476018 prefixEnd_1476018 := by exact prefixLift 1476018
  have htrace : WordTrace (prefixWord ++ tailWord_1476018) baseStart_1476018 baseEnd_1476018 := by
    simpa [prefixWord, tailWord_1476018, baseEnd_1476018] using wordTrace_append hprefix tailTrace_1476018
  have hstable : (prefixWord ++ tailWord_1476018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476018).length < 2 ^ (prefixWord ++ tailWord_1476018).sum := by decide
  have hdescent : baseEnd_1476018 < baseStart_1476018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_1476048 : Nat := 118140960795 + 1476048 * 2 ^ 59
def prefixEnd_1476048 : Nat := 4983230072969 + 3 ^ 40 * 1476048 * 2
def baseEnd_1476048 : Nat := 505281395405164126074523

theorem tailTrace_1476048 : CollatzResearch.WordTrace tailWord_1476048 prefixEnd_1476048 505281395405164126074523 := by
  unfold tailWord_1476048
  simp only [CollatzResearch.WordTrace]
  refine ⟨26917946678268829886842399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35890595571025106515789865 26917946678268829886842399)
  ·
    refine ⟨40376920017403244830263599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26917946678268829886842399 40376920017403244830263599)
    ·
      refine ⟨60565380026104867245395399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40376920017403244830263599 60565380026104867245395399)
      ·
        refine ⟨90848070039157300868093099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60565380026104867245395399 90848070039157300868093099)
        ·
          refine ⟨136272105058735951302139649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90848070039157300868093099 136272105058735951302139649)
          ·
            refine ⟨102204078794051963476604737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136272105058735951302139649 102204078794051963476604737)
            ·
              refine ⟨76653059095538972607453553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102204078794051963476604737 76653059095538972607453553)
              ·
                refine ⟨57489794321654229455590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76653059095538972607453553 57489794321654229455590165)
                ·
                  refine ⟨2694834108827542005730789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57489794321654229455590165 2694834108827542005730789)
                  ·
                    refine ⟨505281395405164126074523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694834108827542005730789 505281395405164126074523)
                    ·
                      rfl

theorem cell22_1476048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_1476048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476048 prefixEnd_1476048 := by exact prefixLift 1476048
  have htrace : WordTrace (prefixWord ++ tailWord_1476048) baseStart_1476048 baseEnd_1476048 := by
    simpa [prefixWord, tailWord_1476048, baseEnd_1476048] using wordTrace_append hprefix tailTrace_1476048
  have hstable : (prefixWord ++ tailWord_1476048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476048).length < 2 ^ (prefixWord ++ tailWord_1476048).sum := by decide
  have hdescent : baseEnd_1476048 < baseStart_1476048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476065 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1476065 : Nat := 118140960795 + 1476065 * 2 ^ 59
def prefixEnd_1476065 : Nat := 4983230072969 + 3 ^ 40 * 1476065 * 2
def baseEnd_1476065 : Nat := 505287214852581748399471

theorem tailTrace_1476065 : CollatzResearch.WordTrace tailWord_1476065 prefixEnd_1476065 505287214852581748399471 := by
  unfold tailWord_1476065
  simp only [CollatzResearch.WordTrace]
  refine ⟨53836513397476071677053649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35891008931650714451369099 53836513397476071677053649)
  ·
    refine ⟨40377385048107053757790237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53836513397476071677053649 40377385048107053757790237)
    ·
      refine ⟨15141519393040145159171339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40377385048107053757790237 15141519393040145159171339)
      ·
        refine ⟨22712279089560217738757009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15141519393040145159171339 22712279089560217738757009)
        ·
          refine ⟨17034209317170163304067757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22712279089560217738757009 17034209317170163304067757)
          ·
            refine ⟨6387828493938811239025409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17034209317170163304067757 6387828493938811239025409)
            ·
              refine ⟨4790871370454108429269057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6387828493938811239025409 4790871370454108429269057)
              ·
                refine ⟨3593153527840581321951793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790871370454108429269057 3593153527840581321951793)
                ·
                  refine ⟨2694865145880435991463845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593153527840581321951793 2694865145880435991463845)
                  ·
                    refine ⟨505287214852581748399471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694865145880435991463845 505287214852581748399471)
                    ·
                      rfl

theorem cell22_1476065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1476065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476065 prefixEnd_1476065 := by exact prefixLift 1476065
  have htrace : WordTrace (prefixWord ++ tailWord_1476065) baseStart_1476065 baseEnd_1476065 := by
    simpa [prefixWord, tailWord_1476065, baseEnd_1476065] using wordTrace_append hprefix tailTrace_1476065
  have hstable : (prefixWord ++ tailWord_1476065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476065).length < 2 ^ (prefixWord ++ tailWord_1476065).sum := by decide
  have hdescent : baseEnd_1476065 < baseStart_1476065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476067 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 2, 3]
def baseStart_1476067 : Nat := 118140960795 + 1476067 * 2 ^ 59
def prefixEnd_1476067 : Nat := 4983230072969 + 3 ^ 40 * 1476067 * 2
def baseEnd_1476067 : Nat := 505287899493454409849465

theorem tailTrace_1476067 : CollatzResearch.WordTrace tailWord_1476067 prefixEnd_1476067 505287899493454409849465 := by
  unfold tailWord_1476067
  simp only [CollatzResearch.WordTrace]
  refine ⟨53836586343468826018626455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35891057562312550679084303 53836586343468826018626455)
  ·
    refine ⟨80754879515203239027939683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53836586343468826018626455 80754879515203239027939683)
    ·
      refine ⟨121132319272804858541909525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80754879515203239027939683 121132319272804858541909525)
      ·
        refine ⟨5678077465912727744152009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121132319272804858541909525 5678077465912727744152009)
        ·
          refine ⟨4258558099434545808114007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5678077465912727744152009 4258558099434545808114007)
          ·
            refine ⟨6387837149151818712171011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258558099434545808114007 6387837149151818712171011)
            ·
              refine ⟨9581755723727728068256517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387837149151818712171011 9581755723727728068256517)
              ·
                refine ⟨1796579198198949012798097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9581755723727728068256517 1796579198198949012798097)
                ·
                  refine ⟨1347434398649211759598573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796579198198949012798097 1347434398649211759598573)
                  ·
                    refine ⟨505287899493454409849465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347434398649211759598573 505287899493454409849465)
                    ·
                      rfl

theorem cell22_1476067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].length) (baseStart_1476067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476067 prefixEnd_1476067 := by exact prefixLift 1476067
  have htrace : WordTrace (prefixWord ++ tailWord_1476067) baseStart_1476067 baseEnd_1476067 := by
    simpa [prefixWord, tailWord_1476067, baseEnd_1476067] using wordTrace_append hprefix tailTrace_1476067
  have hstable : (prefixWord ++ tailWord_1476067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476067).length < 2 ^ (prefixWord ++ tailWord_1476067).sum := by decide
  have hdescent : baseEnd_1476067 < baseStart_1476067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476069 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 4]
def baseStart_1476069 : Nat := 118140960795 + 1476069 * 2 ^ 59
def prefixEnd_1476069 : Nat := 4983230072969 + 3 ^ 40 * 1476069 * 2
def baseEnd_1476069 : Nat := 168429528044775690433153

theorem tailTrace_1476069 : CollatzResearch.WordTrace tailWord_1476069 prefixEnd_1476069 168429528044775690433153 := by
  unfold tailWord_1476069
  simp only [CollatzResearch.WordTrace]
  refine ⟨53836659289461580360199261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35891106192974386906799507 53836659289461580360199261)
  ·
    refine ⟨20188747233548092635074723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53836659289461580360199261 20188747233548092635074723)
    ·
      refine ⟨30283120850322138952612085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188747233548092635074723 30283120850322138952612085)
      ·
        refine ⟨2839042579717700526807383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30283120850322138952612085 2839042579717700526807383)
        ·
          refine ⟨4258563869576550790211075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839042579717700526807383 4258563869576550790211075)
          ·
            refine ⟨6387845804364826185316613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258563869576550790211075 6387845804364826185316613)
            ·
              refine ⟨1197721088318404909746865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6387845804364826185316613 1197721088318404909746865)
              ·
                refine ⟨898290816238803682310149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197721088318404909746865 898290816238803682310149)
                ·
                  refine ⟨168429528044775690433153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898290816238803682310149 168429528044775690433153)
                  ·
                    rfl

theorem cell22_1476069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_1476069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476069 prefixEnd_1476069 := by exact prefixLift 1476069
  have htrace : WordTrace (prefixWord ++ tailWord_1476069) baseStart_1476069 baseEnd_1476069 := by
    simpa [prefixWord, tailWord_1476069, baseEnd_1476069] using wordTrace_append hprefix tailTrace_1476069
  have hstable : (prefixWord ++ tailWord_1476069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476069).length < 2 ^ (prefixWord ++ tailWord_1476069).sum := by decide
  have hdescent : baseEnd_1476069 < baseStart_1476069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476080 : List Nat := [2, 1, 1, 1, 3, 6, 1, 7]
def baseStart_1476080 : Nat := 118140960795 + 1476080 * 2 ^ 59
def prefixEnd_1476080 : Nat := 4983230072969 + 3 ^ 40 * 1476080 * 2
def baseEnd_1476080 : Nat := 56143594406569634363825

theorem tailTrace_1476080 : CollatzResearch.WordTrace tailWord_1476080 prefixEnd_1476080 56143594406569634363825 := by
  unfold tailWord_1476080
  simp only [CollatzResearch.WordTrace]
  refine ⟨26918530246210864619424847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35891373661614486159233129 26918530246210864619424847)
  ·
    refine ⟨40377795369316296929137271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26918530246210864619424847 40377795369316296929137271)
    ·
      refine ⟨60566693053974445393705907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40377795369316296929137271 60566693053974445393705907)
      ·
        refine ⟨90850039580961668090558861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60566693053974445393705907 90850039580961668090558861)
        ·
          refine ⟨34068764842860625533959573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90850039580961668090558861 34068764842860625533959573)
          ·
            refine ⟨1596973352009091821904355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34068764842860625533959573 1596973352009091821904355)
            ·
              refine ⟨2395460028013637732856533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596973352009091821904355 2395460028013637732856533)
              ·
                refine ⟨56143594406569634363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2395460028013637732856533 56143594406569634363825)
                ·
                  rfl

theorem cell22_1476080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_1476080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476080 prefixEnd_1476080 := by exact prefixLift 1476080
  have htrace : WordTrace (prefixWord ++ tailWord_1476080) baseStart_1476080 baseEnd_1476080 := by
    simpa [prefixWord, tailWord_1476080, baseEnd_1476080] using wordTrace_append hprefix tailTrace_1476080
  have hstable : (prefixWord ++ tailWord_1476080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476080).length < 2 ^ (prefixWord ++ tailWord_1476080).sum := by decide
  have hdescent : baseEnd_1476080 < baseStart_1476080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476097 : List Nat := [1, 2, 4, 1, 4, 1, 3, 6]
def baseStart_1476097 : Nat := 118140960795 + 1476097 * 2 ^ 59
def prefixEnd_1476097 : Nat := 4983230072969 + 3 ^ 40 * 1476097 * 2
def baseEnd_1476097 : Nat := 56144241011838259066597

theorem tailTrace_1476097 : CollatzResearch.WordTrace tailWord_1476097 prefixEnd_1476097 56144241011838259066597 := by
  unfold tailWord_1476097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53837680533360141142218545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35891787022240094094812363 53837680533360141142218545)
  ·
    refine ⟨40378260400020105856663909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53837680533360141142218545 40378260400020105856663909)
    ·
      refine ⟨7570923825003769848124483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40378260400020105856663909 7570923825003769848124483)
      ·
        refine ⟨11356385737505654772186725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7570923825003769848124483 11356385737505654772186725)
        ·
          refine ⟨2129322325782310269785011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11356385737505654772186725 2129322325782310269785011)
          ·
            refine ⟨3193983488673465404677517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129322325782310269785011 3193983488673465404677517)
            ·
              refine ⟨1197743808252549526754069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3193983488673465404677517 1197743808252549526754069)
              ·
                refine ⟨56144241011838259066597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1197743808252549526754069 56144241011838259066597)
                ·
                  rfl

theorem cell22_1476097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 6].length) (baseStart_1476097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476097 prefixEnd_1476097 := by exact prefixLift 1476097
  have htrace : WordTrace (prefixWord ++ tailWord_1476097) baseStart_1476097 baseEnd_1476097 := by
    simpa [prefixWord, tailWord_1476097, baseEnd_1476097] using wordTrace_append hprefix tailTrace_1476097
  have hstable : (prefixWord ++ tailWord_1476097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476097).length < 2 ^ (prefixWord ++ tailWord_1476097).sum := by decide
  have hdescent : baseEnd_1476097 < baseStart_1476097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476125 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 7]
def baseStart_1476125 : Nat := 118140960795 + 1476125 * 2 ^ 59
def prefixEnd_1476125 : Nat := 4983230072969 + 3 ^ 40 * 1476125 * 2
def baseEnd_1476125 : Nat := 168435918026253863966429

theorem tailTrace_1476125 : CollatzResearch.WordTrace tailWord_1476125 prefixEnd_1476125 168435918026253863966429 := by
  unfold tailWord_1476125
  simp only [CollatzResearch.WordTrace]
  refine ⟨53838701777258701924237829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35892467851505801282825219 53838701777258701924237829)
  ·
    refine ⟨10094756583236006610794593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53838701777258701924237829 10094756583236006610794593)
    ·
      refine ⟨7571067437427004958095945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10094756583236006610794593 7571067437427004958095945)
      ·
        refine ⟨5678300578070253718571959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7571067437427004958095945 5678300578070253718571959)
        ·
          refine ⟨8517450867105380577857939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678300578070253718571959 8517450867105380577857939)
          ·
            refine ⟨12776176300658070866786909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517450867105380577857939 12776176300658070866786909)
            ·
              refine ⟨4791066112746776575045091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12776176300658070866786909 4791066112746776575045091)
              ·
                refine ⟨7186599169120164862567637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791066112746776575045091 7186599169120164862567637)
                ·
                  refine ⟨168435918026253863966429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7186599169120164862567637 168435918026253863966429)
                  ·
                    rfl

theorem cell22_1476125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_1476125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476125 prefixEnd_1476125 := by exact prefixLift 1476125
  have htrace : WordTrace (prefixWord ++ tailWord_1476125) baseStart_1476125 baseEnd_1476125 := by
    simpa [prefixWord, tailWord_1476125, baseEnd_1476125] using wordTrace_append hprefix tailTrace_1476125
  have hstable : (prefixWord ++ tailWord_1476125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476125).length < 2 ^ (prefixWord ++ tailWord_1476125).sum := by decide
  have hdescent : baseEnd_1476125 < baseStart_1476125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476129 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1476129 : Nat := 118140960795 + 1476129 * 2 ^ 59
def prefixEnd_1476129 : Nat := 4983230072969 + 3 ^ 40 * 1476129 * 2
def baseEnd_1476129 : Nat := 505309123360506914799275

theorem tailTrace_1476129 : CollatzResearch.WordTrace tailWord_1476129 prefixEnd_1476129 505309123360506914799275 := by
  unfold tailWord_1476129
  simp only [CollatzResearch.WordTrace]
  refine ⟨53838847669244210607383441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35892565112829473738255627 53838847669244210607383441)
  ·
    refine ⟨40379135751933157955537581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53838847669244210607383441 40379135751933157955537581)
    ·
      refine ⟨15142175906974934233326593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40379135751933157955537581 15142175906974934233326593)
      ·
        refine ⟨11356631930231200674994945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15142175906974934233326593 11356631930231200674994945)
        ·
          refine ⟨8517473947673400506246209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11356631930231200674994945 8517473947673400506246209)
          ·
            refine ⟨6388105460755050379684657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8517473947673400506246209 6388105460755050379684657)
            ·
              refine ⟨4791079095566287784763493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388105460755050379684657 4791079095566287784763493)
              ·
                refine ⟨898327330418678959643155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4791079095566287784763493 898327330418678959643155)
                ·
                  refine ⟨1347490995628018439464733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898327330418678959643155 1347490995628018439464733)
                  ·
                    refine ⟨505309123360506914799275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347490995628018439464733 505309123360506914799275)
                    ·
                      rfl

theorem cell22_1476129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1476129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476129 prefixEnd_1476129 := by exact prefixLift 1476129
  have htrace : WordTrace (prefixWord ++ tailWord_1476129) baseStart_1476129 baseEnd_1476129 := by
    simpa [prefixWord, tailWord_1476129, baseEnd_1476129] using wordTrace_append hprefix tailTrace_1476129
  have hstable : (prefixWord ++ tailWord_1476129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476129).length < 2 ^ (prefixWord ++ tailWord_1476129).sum := by decide
  have hdescent : baseEnd_1476129 < baseStart_1476129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476172 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1476172 : Nat := 118140960795 + 1476172 * 2 ^ 59
def prefixEnd_1476172 : Nat := 4983230072969 + 3 ^ 40 * 1476172 * 2
def baseEnd_1476172 : Nat := 505323843139269135974143

theorem tailTrace_1476172 : CollatzResearch.WordTrace tailWord_1476172 prefixEnd_1476172 505323843139269135974143 := by
  unfold tailWord_1476172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26920208004044214475599385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35893610672058952634132513 26920208004044214475599385)
  ·
    refine ⟨20190156003033160856699539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26920208004044214475599385 20190156003033160856699539)
    ·
      refine ⟨30285234004549741285049309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20190156003033160856699539 30285234004549741285049309)
      ·
        refine ⟨11356962751706152981893491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30285234004549741285049309 11356962751706152981893491)
        ·
          refine ⟨17035444127559229472840237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356962751706152981893491 17035444127559229472840237)
          ·
            refine ⟨6388291547834711052315089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17035444127559229472840237 6388291547834711052315089)
            ·
              refine ⟨4791218660876033289236317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388291547834711052315089 4791218660876033289236317)
              ·
                refine ⟨1796706997828512483463619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4791218660876033289236317 1796706997828512483463619)
                ·
                  refine ⟨2695060496742768725195429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796706997828512483463619 2695060496742768725195429)
                  ·
                    refine ⟨505323843139269135974143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695060496742768725195429 505323843139269135974143)
                    ·
                      rfl

theorem cell22_1476172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1476172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476172 prefixEnd_1476172 := by exact prefixLift 1476172
  have htrace : WordTrace (prefixWord ++ tailWord_1476172) baseStart_1476172 baseEnd_1476172 := by
    simpa [prefixWord, tailWord_1476172, baseEnd_1476172] using wordTrace_append hprefix tailTrace_1476172
  have hstable : (prefixWord ++ tailWord_1476172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476172).length < 2 ^ (prefixWord ++ tailWord_1476172).sum := by decide
  have hdescent : baseEnd_1476172 < baseStart_1476172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476206 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1476206 : Nat := 118140960795 + 1476206 * 2 ^ 59
def prefixEnd_1476206 : Nat := 4983230072969 + 3 ^ 40 * 1476206 * 2
def baseEnd_1476206 : Nat := 505335482034104380624039

theorem tailTrace_1476206 : CollatzResearch.WordTrace tailWord_1476206 prefixEnd_1476206 505335482034104380624039 := by
  unfold tailWord_1476206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730207011245656594742059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35894437393310168505290981 6730207011245656594742059)
  ·
    refine ⟨10095310516868484892113089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6730207011245656594742059 10095310516868484892113089)
    ·
      refine ⟨7571482887651363669084817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10095310516868484892113089 7571482887651363669084817)
      ·
        refine ⟨5678612165738522751813613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7571482887651363669084817 5678612165738522751813613)
        ·
          refine ⟨2129479562151946031930105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5678612165738522751813613 2129479562151946031930105)
          ·
            refine ⟨1597109671613959523947579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129479562151946031930105 1597109671613959523947579)
            ·
              refine ⟨2395664507420939285921369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597109671613959523947579 2395664507420939285921369)
              ·
                refine ⟨1796748380565704464441027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395664507420939285921369 1796748380565704464441027)
                ·
                  refine ⟨2695122570848556696661541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796748380565704464441027 2695122570848556696661541)
                  ·
                    refine ⟨505335482034104380624039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695122570848556696661541 505335482034104380624039)
                    ·
                      rfl

theorem cell22_1476206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1476206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476206 prefixEnd_1476206 := by exact prefixLift 1476206
  have htrace : WordTrace (prefixWord ++ tailWord_1476206) baseStart_1476206 baseEnd_1476206 := by
    simpa [prefixWord, tailWord_1476206, baseEnd_1476206] using wordTrace_append hprefix tailTrace_1476206
  have hstable : (prefixWord ++ tailWord_1476206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476206).length < 2 ^ (prefixWord ++ tailWord_1476206).sum := by decide
  have hdescent : baseEnd_1476206 < baseStart_1476206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476217 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_1476217 : Nat := 118140960795 + 1476217 * 2 ^ 59
def prefixEnd_1476217 : Nat := 4983230072969 + 3 ^ 40 * 1476217 * 2
def baseEnd_1476217 : Nat := 505339247558904018599005

theorem tailTrace_1476217 : CollatzResearch.WordTrace tailWord_1476217 prefixEnd_1476217 505339247558904018599005 := by
  unfold tailWord_1476217
  simp only [CollatzResearch.WordTrace]
  refine ⟨53842057292925401636586905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35894704861950267757724603 53842057292925401636586905)
  ·
    refine ⟨40381542969694051227440179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53842057292925401636586905 40381542969694051227440179)
    ·
      refine ⟨60572314454541076841160269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40381542969694051227440179 60572314454541076841160269)
      ·
        refine ⟨22714617920452903815435101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60572314454541076841160269 22714617920452903815435101)
        ·
          refine ⟨8517981720169838930788163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22714617920452903815435101 8517981720169838930788163)
          ·
            refine ⟨12776972580254758396182245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517981720169838930788163 12776972580254758396182245)
            ·
              refine ⟨2395682358797767199284171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12776972580254758396182245 2395682358797767199284171)
              ·
                refine ⟨3593523538196650798926257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395682358797767199284171 3593523538196650798926257)
                ·
                  refine ⟨2695142653647488099194693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593523538196650798926257 2695142653647488099194693)
                  ·
                    refine ⟨505339247558904018599005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695142653647488099194693 505339247558904018599005)
                    ·
                      rfl

theorem cell22_1476217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_1476217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476217 prefixEnd_1476217 := by exact prefixLift 1476217
  have htrace : WordTrace (prefixWord ++ tailWord_1476217) baseStart_1476217 baseEnd_1476217 := by
    simpa [prefixWord, tailWord_1476217, baseEnd_1476217] using wordTrace_append hprefix tailTrace_1476217
  have hstable : (prefixWord ++ tailWord_1476217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476217).length < 2 ^ (prefixWord ++ tailWord_1476217).sum := by decide
  have hdescent : baseEnd_1476217 < baseStart_1476217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476232 : List Nat := [2, 1, 3, 5, 1, 10]
def baseStart_1476232 : Nat := 118140960795 + 1476232 * 2 ^ 59
def prefixEnd_1476232 : Nat := 4983230072969 + 3 ^ 40 * 1476232 * 2
def baseEnd_1476232 : Nat := 6238819535375913326839

theorem tailTrace_1476232 : CollatzResearch.WordTrace tailWord_1476232 prefixEnd_1476232 6238819535375913326839 := by
  unfold tailWord_1476232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921302193935529599191475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35895069591914039465588633 26921302193935529599191475)
  ·
    refine ⟨40381953290903294398787213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26921302193935529599191475 40381953290903294398787213)
    ·
      refine ⟨15143232484088735399545205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40381953290903294398787213 15143232484088735399545205)
      ·
        refine ⟨1419678045383318943707363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15143232484088735399545205 1419678045383318943707363)
        ·
          refine ⟨2129517068074978415561045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419678045383318943707363 2129517068074978415561045)
          ·
            refine ⟨6238819535375913326839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2129517068074978415561045 6238819535375913326839)
            ·
              rfl

theorem cell22_1476232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 10].length) (baseStart_1476232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476232 prefixEnd_1476232 := by exact prefixLift 1476232
  have htrace : WordTrace (prefixWord ++ tailWord_1476232) baseStart_1476232 baseEnd_1476232 := by
    simpa [prefixWord, tailWord_1476232, baseEnd_1476232] using wordTrace_append hprefix tailTrace_1476232
  have hstable : (prefixWord ++ tailWord_1476232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476232).length < 2 ^ (prefixWord ++ tailWord_1476232).sum := by decide
  have hdescent : baseEnd_1476232 < baseStart_1476232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476275 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_1476275 : Nat := 118140960795 + 1476275 * 2 ^ 59
def prefixEnd_1476275 : Nat := 4983230072969 + 3 ^ 40 * 1476275 * 2
def baseEnd_1476275 : Nat := 505359102144211200648827

theorem tailTrace_1476275 : CollatzResearch.WordTrace tailWord_1476275 prefixEnd_1476275 505359102144211200648827 := by
  unfold tailWord_1476275
  simp only [CollatzResearch.WordTrace]
  refine ⟨53844172726715277542198279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35896115151143518361465519 53844172726715277542198279)
  ·
    refine ⟨80766259090072916313297419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53844172726715277542198279 80766259090072916313297419)
    ·
      refine ⟨121149388635109374469946129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80766259090072916313297419 121149388635109374469946129)
      ·
        refine ⟨90862041476332030852459597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121149388635109374469946129 90862041476332030852459597)
        ·
          refine ⟨34073265553624511569672349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90862041476332030852459597 34073265553624511569672349)
          ·
            refine ⟨12777474582609191838627131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34073265553624511569672349 12777474582609191838627131)
            ·
              refine ⟨19166211873913787757940697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12777474582609191838627131 19166211873913787757940697)
              ·
                refine ⟨14374658905435340818455523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19166211873913787757940697 14374658905435340818455523)
                ·
                  refine ⟨21561988358153011227683285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14374658905435340818455523 21561988358153011227683285)
                  ·
                    refine ⟨505359102144211200648827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21561988358153011227683285 505359102144211200648827)
                    ·
                      rfl

theorem cell22_1476275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_1476275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476275 prefixEnd_1476275 := by exact prefixLift 1476275
  have htrace : WordTrace (prefixWord ++ tailWord_1476275) baseStart_1476275 baseEnd_1476275 := by
    simpa [prefixWord, tailWord_1476275, baseEnd_1476275] using wordTrace_append hprefix tailTrace_1476275
  have hstable : (prefixWord ++ tailWord_1476275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476275).length < 2 ^ (prefixWord ++ tailWord_1476275).sum := by decide
  have hdescent : baseEnd_1476275 < baseStart_1476275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476292 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1476292 : Nat := 118140960795 + 1476292 * 2 ^ 59
def prefixEnd_1476292 : Nat := 4983230072969 + 3 ^ 40 * 1476292 * 2
def baseEnd_1476292 : Nat := 505364921591628822973775

theorem tailTrace_1476292 : CollatzResearch.WordTrace tailWord_1476292 prefixEnd_1476292 505364921591628822973775 := by
  unfold tailWord_1476292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26922396383826844722783565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35896528511769126297044753 26922396383826844722783565)
  ·
    refine ⟨10095898643935066771043837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26922396383826844722783565 10095898643935066771043837)
    ·
      refine ⟨3785961991475650039141439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10095898643935066771043837 3785961991475650039141439)
      ·
        refine ⟨5678942987213475058712159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785961991475650039141439 5678942987213475058712159)
        ·
          refine ⟨8518414480820212588068239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678942987213475058712159 8518414480820212588068239)
          ·
            refine ⟨12777621721230318882102359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518414480820212588068239 12777621721230318882102359)
            ·
              refine ⟨19166432581845478323153539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12777621721230318882102359 19166432581845478323153539)
              ·
                refine ⟨28749648872768217484730309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19166432581845478323153539 28749648872768217484730309)
                ·
                  refine ⟨5390559163644040778386933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28749648872768217484730309 5390559163644040778386933)
                  ·
                    refine ⟨505364921591628822973775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5390559163644040778386933 505364921591628822973775)
                    ·
                      rfl

theorem cell22_1476292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1476292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476292 prefixEnd_1476292 := by exact prefixLift 1476292
  have htrace : WordTrace (prefixWord ++ tailWord_1476292) baseStart_1476292 baseEnd_1476292 := by
    simpa [prefixWord, tailWord_1476292, baseEnd_1476292] using wordTrace_append hprefix tailTrace_1476292
  have hstable : (prefixWord ++ tailWord_1476292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476292).length < 2 ^ (prefixWord ++ tailWord_1476292).sum := by decide
  have hdescent : baseEnd_1476292 < baseStart_1476292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476324 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1476324 : Nat := 118140960795 + 1476324 * 2 ^ 59
def prefixEnd_1476324 : Nat := 4983230072969 + 3 ^ 40 * 1476324 * 2
def baseEnd_1476324 : Nat := 505375875845591406173677

theorem tailTrace_1476324 : CollatzResearch.WordTrace tailWord_1476324 prefixEnd_1476324 505375875845591406173677 := by
  unfold tailWord_1476324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26922979951768879455366013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35897306602358505940488017 26922979951768879455366013)
  ·
    refine ⟨10096117481913329795762255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26922979951768879455366013 10096117481913329795762255)
    ·
      refine ⟨15144176222869994693643383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10096117481913329795762255 15144176222869994693643383)
      ·
        refine ⟨22716264334304992040465075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15144176222869994693643383 22716264334304992040465075)
        ·
          refine ⟨34074396501457488060697613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22716264334304992040465075 34074396501457488060697613)
          ·
            refine ⟨12777898688046558022761605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34074396501457488060697613 12777898688046558022761605)
            ·
              refine ⟨2395856004008729629267801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12777898688046558022761605 2395856004008729629267801)
              ·
                refine ⟨1796892003006547221950851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395856004008729629267801 1796892003006547221950851)
                ·
                  refine ⟨2695338004509820832926277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796892003006547221950851 2695338004509820832926277)
                  ·
                    refine ⟨505375875845591406173677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695338004509820832926277 505375875845591406173677)
                    ·
                      rfl

theorem cell22_1476324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1476324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476324 prefixEnd_1476324 := by exact prefixLift 1476324
  have htrace : WordTrace (prefixWord ++ tailWord_1476324) baseStart_1476324 baseEnd_1476324 := by
    simpa [prefixWord, tailWord_1476324, baseEnd_1476324] using wordTrace_append hprefix tailTrace_1476324
  have hstable : (prefixWord ++ tailWord_1476324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476324).length < 2 ^ (prefixWord ++ tailWord_1476324).sum := by decide
  have hdescent : baseEnd_1476324 < baseStart_1476324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476339 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 4]
def baseStart_1476339 : Nat := 118140960795 + 1476339 * 2 ^ 59
def prefixEnd_1476339 : Nat := 4983230072969 + 3 ^ 40 * 1476339 * 2
def baseEnd_1476339 : Nat := 168460336884045455682877

theorem tailTrace_1476339 : CollatzResearch.WordTrace tailWord_1476339 prefixEnd_1476339 168460336884045455682877 := by
  unfold tailWord_1476339
  simp only [CollatzResearch.WordTrace]
  refine ⟨53846506998483416472528071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35897671332322277648352047 53846506998483416472528071)
  ·
    refine ⟨80769760497725124708792107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53846506998483416472528071 80769760497725124708792107)
    ·
      refine ⟨121154640746587687063188161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80769760497725124708792107 121154640746587687063188161)
      ·
        refine ⟨90865980559940765297391121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121154640746587687063188161 90865980559940765297391121)
        ·
          refine ⟨68149485419955573973043341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90865980559940765297391121 68149485419955573973043341)
          ·
            refine ⟨25556057032483340239891253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68149485419955573973043341 25556057032483340239891253)
            ·
              refine ⟨2395880346795313147489805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25556057032483340239891253 2395880346795313147489805)
              ·
                refine ⟨898455130048242430308677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2395880346795313147489805 898455130048242430308677)
                ·
                  refine ⟨168460336884045455682877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898455130048242430308677 168460336884045455682877)
                  ·
                    rfl

theorem cell22_1476339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 4].length) (baseStart_1476339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476339 prefixEnd_1476339 := by exact prefixLift 1476339
  have htrace : WordTrace (prefixWord ++ tailWord_1476339) baseStart_1476339 baseEnd_1476339 := by
    simpa [prefixWord, tailWord_1476339, baseEnd_1476339] using wordTrace_append hprefix tailTrace_1476339
  have hstable : (prefixWord ++ tailWord_1476339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476339).length < 2 ^ (prefixWord ++ tailWord_1476339).sum := by decide
  have hdescent : baseEnd_1476339 < baseStart_1476339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476352 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_1476352 : Nat := 118140960795 + 1476352 * 2 ^ 59
def prefixEnd_1476352 : Nat := 4983230072969 + 3 ^ 40 * 1476352 * 2
def baseEnd_1476352 : Nat := 505385460817808666473591

theorem tailTrace_1476352 : CollatzResearch.WordTrace tailWord_1476352 prefixEnd_1476352 505385460817808666473591 := by
  unfold tailWord_1476352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26923490573718159846375655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35897987431624213128500873 26923490573718159846375655)
  ·
    refine ⟨40385235860577239769563483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26923490573718159846375655 40385235860577239769563483)
    ·
      refine ⟨60577853790865859654345225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40385235860577239769563483 60577853790865859654345225)
      ·
        refine ⟨45433390343149394740758919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60577853790865859654345225 45433390343149394740758919)
        ·
          refine ⟨68150085514724092111138379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45433390343149394740758919 68150085514724092111138379)
          ·
            refine ⟨102225128272086138166707569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68150085514724092111138379 102225128272086138166707569)
            ·
              refine ⟨76668846204064603625030677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102225128272086138166707569 76668846204064603625030677)
              ·
                refine ⟨3593852165815528294923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76668846204064603625030677 3593852165815528294923313)
                ·
                  refine ⟨2695389124361646221192485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593852165815528294923313 2695389124361646221192485)
                  ·
                    refine ⟨505385460817808666473591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2695389124361646221192485 505385460817808666473591)
                    ·
                      rfl

theorem cell22_1476352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_1476352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476352 prefixEnd_1476352 := by exact prefixLift 1476352
  have htrace : WordTrace (prefixWord ++ tailWord_1476352) baseStart_1476352 baseEnd_1476352 := by
    simpa [prefixWord, tailWord_1476352, baseEnd_1476352] using wordTrace_append hprefix tailTrace_1476352
  have hstable : (prefixWord ++ tailWord_1476352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476352).length < 2 ^ (prefixWord ++ tailWord_1476352).sum := by decide
  have hdescent : baseEnd_1476352 < baseStart_1476352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476412 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1476412 : Nat := 118140960795 + 1476412 * 2 ^ 59
def prefixEnd_1476412 : Nat := 4983230072969 + 3 ^ 40 * 1476412 * 2
def baseEnd_1476412 : Nat := 168468666681329503324469

theorem tailTrace_1476412 : CollatzResearch.WordTrace tailWord_1476412 prefixEnd_1476412 168468666681329503324469 := by
  unfold tailWord_1476412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26924584763609474969967745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35899446351479299959956993 26924584763609474969967745)
  ·
    refine ⟨20193438572707106227475809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26924584763609474969967745 20193438572707106227475809)
    ·
      refine ⟨15145078929530329670606857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20193438572707106227475809 15145078929530329670606857)
      ·
        refine ⟨11358809197147747252955143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15145078929530329670606857 11358809197147747252955143)
        ·
          refine ⟨17038213795721620879432715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358809197147747252955143 17038213795721620879432715)
          ·
            refine ⟨25557320693582431319149073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17038213795721620879432715 25557320693582431319149073)
            ·
              refine ⟨19167990520186823489361805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25557320693582431319149073 19167990520186823489361805)
              ·
                refine ⟨7187996445070058808510677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19167990520186823489361805 7187996445070058808510677)
                ·
                  refine ⟨168468666681329503324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7187996445070058808510677 168468666681329503324469)
                  ·
                    rfl

theorem cell22_1476412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1476412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476412 prefixEnd_1476412 := by exact prefixLift 1476412
  have htrace : WordTrace (prefixWord ++ tailWord_1476412) baseStart_1476412 baseEnd_1476412 := by
    simpa [prefixWord, tailWord_1476412, baseEnd_1476412] using wordTrace_append hprefix tailTrace_1476412
  have hstable : (prefixWord ++ tailWord_1476412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476412).length < 2 ^ (prefixWord ++ tailWord_1476412).sum := by decide
  have hdescent : baseEnd_1476412 < baseStart_1476412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476414 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1476414 : Nat := 118140960795 + 1476414 * 2 ^ 59
def prefixEnd_1476414 : Nat := 4983230072969 + 3 ^ 40 * 1476414 * 2
def baseEnd_1476414 : Nat := 505406684684861171423401

theorem tailTrace_1476414 : CollatzResearch.WordTrace tailWord_1476414 prefixEnd_1476414 505406684684861171423401 := by
  unfold tailWord_1476414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731155309151463035188537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35899494982141136187672197 6731155309151463035188537)
  ·
    refine ⟨5048366481863597276391403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6731155309151463035188537 5048366481863597276391403)
    ·
      refine ⟨7572549722795395914587105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048366481863597276391403 7572549722795395914587105)
      ·
        refine ⟨5679412292096546935940329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7572549722795395914587105 5679412292096546935940329)
        ·
          refine ⟨4259559219072410201955247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679412292096546935940329 4259559219072410201955247)
          ·
            refine ⟨6389338828608615302932871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259559219072410201955247 6389338828608615302932871)
            ·
              refine ⟨9584008242912922954399307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389338828608615302932871 9584008242912922954399307)
              ·
                refine ⟨14376012364369384431598961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584008242912922954399307 14376012364369384431598961)
                ·
                  refine ⟨10782009273277038323699221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14376012364369384431598961 10782009273277038323699221)
                  ·
                    refine ⟨505406684684861171423401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10782009273277038323699221 505406684684861171423401)
                    ·
                      rfl

theorem cell22_1476414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1476414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476414 prefixEnd_1476414 := by exact prefixLift 1476414
  have htrace : WordTrace (prefixWord ++ tailWord_1476414) baseStart_1476414 baseEnd_1476414 := by
    simpa [prefixWord, tailWord_1476414, baseEnd_1476414] using wordTrace_append hprefix tailTrace_1476414
  have hstable : (prefixWord ++ tailWord_1476414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476414).length < 2 ^ (prefixWord ++ tailWord_1476414).sum := by decide
  have hdescent : baseEnd_1476414 < baseStart_1476414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476450 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1476450 : Nat := 118140960795 + 1476450 * 2 ^ 59
def prefixEnd_1476450 : Nat := 4983230072969 + 3 ^ 40 * 1476450 * 2
def baseEnd_1476450 : Nat := 505419008220569077523291

theorem tailTrace_1476450 : CollatzResearch.WordTrace tailWord_1476450 prefixEnd_1476450 505419008220569077523291 := by
  unfold tailWord_1476450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462638875270320607454701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35900370334054188286545869 13462638875270320607454701)
  ·
    refine ⟨5048489578226370227795513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13462638875270320607454701 5048489578226370227795513)
    ·
      refine ⟨3786367183669777670846635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048489578226370227795513 3786367183669777670846635)
      ·
        refine ⟨5679550775504666506269953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786367183669777670846635 5679550775504666506269953)
        ·
          refine ⟨4259663081628499879702465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679550775504666506269953 4259663081628499879702465)
          ·
            refine ⟨3194747311221374909776849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4259663081628499879702465 3194747311221374909776849)
            ·
              refine ⟨2396060483416031182332637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194747311221374909776849 2396060483416031182332637)
              ·
                refine ⟨898522681281011693374739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396060483416031182332637 898522681281011693374739)
                ·
                  refine ⟨1347784021921517540062109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898522681281011693374739 1347784021921517540062109)
                  ·
                    refine ⟨505419008220569077523291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347784021921517540062109 505419008220569077523291)
                    ·
                      rfl

theorem cell22_1476450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1476450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476450 prefixEnd_1476450 := by exact prefixLift 1476450
  have htrace : WordTrace (prefixWord ++ tailWord_1476450) baseStart_1476450 baseEnd_1476450 := by
    simpa [prefixWord, tailWord_1476450, baseEnd_1476450] using wordTrace_append hprefix tailTrace_1476450
  have hstable : (prefixWord ++ tailWord_1476450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476450).length < 2 ^ (prefixWord ++ tailWord_1476450).sum := by decide
  have hdescent : baseEnd_1476450 < baseStart_1476450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476506 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_1476506 : Nat := 118140960795 + 1476506 * 2 ^ 59
def prefixEnd_1476506 : Nat := 4983230072969 + 3 ^ 40 * 1476506 * 2
def baseEnd_1476506 : Nat := 505438178165003598123119

theorem tailTrace_1476506 : CollatzResearch.WordTrace tailWord_1476506 prefixEnd_1476506 505438178165003598123119 := by
  unfold tailWord_1476506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463149497219600998464343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35901731992585602662571581 13463149497219600998464343)
  ·
    refine ⟨20194724245829401497696515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13463149497219600998464343 20194724245829401497696515)
    ·
      refine ⟨30292086368744102246544773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20194724245829401497696515 30292086368744102246544773)
      ·
        refine ⟨5679766194139519171227145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30292086368744102246544773 5679766194139519171227145)
        ·
          refine ⟨4259824645604639378420359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679766194139519171227145 4259824645604639378420359)
          ·
            refine ⟨6389736968406959067630539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259824645604639378420359 6389736968406959067630539)
            ·
              refine ⟨9584605452610438601445809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389736968406959067630539 9584605452610438601445809)
              ·
                refine ⟨7188454089457828951084357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584605452610438601445809 7188454089457828951084357)
                ·
                  refine ⟨1347835141773342928328317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7188454089457828951084357 1347835141773342928328317)
                  ·
                    refine ⟨505438178165003598123119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347835141773342928328317 505438178165003598123119)
                    ·
                      rfl

theorem cell22_1476506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_1476506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476506 prefixEnd_1476506 := by exact prefixLift 1476506
  have htrace : WordTrace (prefixWord ++ tailWord_1476506) baseStart_1476506 baseEnd_1476506 := by
    simpa [prefixWord, tailWord_1476506, baseEnd_1476506] using wordTrace_append hprefix tailTrace_1476506
  have hstable : (prefixWord ++ tailWord_1476506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476506).length < 2 ^ (prefixWord ++ tailWord_1476506).sum := by decide
  have hdescent : baseEnd_1476506 < baseStart_1476506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476508 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_1476508 : Nat := 118140960795 + 1476508 * 2 ^ 59
def prefixEnd_1476508 : Nat := 4983230072969 + 3 ^ 40 * 1476508 * 2
def baseEnd_1476508 : Nat := 168479620935292086524371

theorem tailTrace_1476508 : CollatzResearch.WordTrace tailWord_1476508 prefixEnd_1476508 168479620935292086524371 := by
  unfold tailWord_1476508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926335467435579167715089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35901780623247438890286785 26926335467435579167715089)
  ·
    refine ⟨20194751600576684375786317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26926335467435579167715089 20194751600576684375786317)
    ·
      refine ⟨7573031850216256640919869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20194751600576684375786317 7573031850216256640919869)
      ·
        refine ⟨2839886943831096240344951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7573031850216256640919869 2839886943831096240344951)
        ·
          refine ⟨4259830415746644360517427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839886943831096240344951 4259830415746644360517427)
          ·
            refine ⟨6389745623619966540776141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259830415746644360517427 6389745623619966540776141)
            ·
              refine ⟨2396154608857487452791053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6389745623619966540776141 2396154608857487452791053)
              ·
                refine ⟨898557978321557794796645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396154608857487452791053 898557978321557794796645)
                ·
                  refine ⟨168479620935292086524371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898557978321557794796645 168479620935292086524371)
                  ·
                    rfl

theorem cell22_1476508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_1476508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476508 prefixEnd_1476508 := by exact prefixLift 1476508
  have htrace : WordTrace (prefixWord ++ tailWord_1476508) baseStart_1476508 baseEnd_1476508 := by
    simpa [prefixWord, tailWord_1476508, baseEnd_1476508] using wordTrace_append hprefix tailTrace_1476508
  have hstable : (prefixWord ++ tailWord_1476508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476508).length < 2 ^ (prefixWord ++ tailWord_1476508).sum := by decide
  have hdescent : baseEnd_1476508 < baseStart_1476508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476519 : List Nat := [1, 1, 6, 1, 2, 1, 10]
def baseStart_1476519 : Nat := 118140960795 + 1476519 * 2 ^ 59
def prefixEnd_1476519 : Nat := 4983230072969 + 3 ^ 40 * 1476519 * 2
def baseEnd_1476519 : Nat := 18720097345580588798077

theorem tailTrace_1476519 : CollatzResearch.WordTrace tailWord_1476519 prefixEnd_1476519 18720097345580588798077 := by
  unfold tailWord_1476519
  simp only [CollatzResearch.WordTrace]
  refine ⟨53853072137831307214080611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35902048091887538142720407 53853072137831307214080611)
  ·
    refine ⟨80779608206746960821120917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53853072137831307214080611 80779608206746960821120917)
    ·
      refine ⟨3786544134691263788490043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80779608206746960821120917 3786544134691263788490043)
      ·
        refine ⟨5679816202036895682735065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786544134691263788490043 5679816202036895682735065)
        ·
          refine ⟨4259862151527671762051299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679816202036895682735065 4259862151527671762051299)
          ·
            refine ⟨6389793227291507643076949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259862151527671762051299 6389793227291507643076949)
            ·
              refine ⟨18720097345580588798077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6389793227291507643076949 18720097345580588798077)
              ·
                rfl

theorem cell22_1476519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 10].length) (baseStart_1476519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476519 prefixEnd_1476519 := by exact prefixLift 1476519
  have htrace : WordTrace (prefixWord ++ tailWord_1476519) baseStart_1476519 baseEnd_1476519 := by
    simpa [prefixWord, tailWord_1476519, baseEnd_1476519] using wordTrace_append hprefix tailTrace_1476519
  have hstable : (prefixWord ++ tailWord_1476519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476519).length < 2 ^ (prefixWord ++ tailWord_1476519).sum := by decide
  have hdescent : baseEnd_1476519 < baseStart_1476519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476540 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1476540 : Nat := 118140960795 + 1476540 * 2 ^ 59
def prefixEnd_1476540 : Nat := 4983230072969 + 3 ^ 40 * 1476540 * 2
def baseEnd_1476540 : Nat := 505449817059838842773015

theorem tailTrace_1476540 : CollatzResearch.WordTrace tailWord_1476540 prefixEnd_1476540 505449817059838842773015 := by
  unfold tailWord_1476540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926919035377613900297537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35902558713836818533730049 26926919035377613900297537)
  ·
    refine ⟨20195189276533210425223153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26926919035377613900297537 20195189276533210425223153)
    ·
      refine ⟨15146391957399907818917365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20195189276533210425223153 15146391957399907818917365)
      ·
        refine ⟨1419974246006241358023503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15146391957399907818917365 1419974246006241358023503)
        ·
          refine ⟨2129961369009362037035255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419974246006241358023503 2129961369009362037035255)
          ·
            refine ⟨3194942053514043055552883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129961369009362037035255 3194942053514043055552883)
            ·
              refine ⟨4792413080271064583329325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194942053514043055552883 4792413080271064583329325)
              ·
                refine ⟨1797154905101649218748497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792413080271064583329325 1797154905101649218748497)
                ·
                  refine ⟨1347866178826236914061373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797154905101649218748497 1347866178826236914061373)
                  ·
                    refine ⟨505449817059838842773015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347866178826236914061373 505449817059838842773015)
                    ·
                      rfl

theorem cell22_1476540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1476540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476540 prefixEnd_1476540 := by exact prefixLift 1476540
  have htrace : WordTrace (prefixWord ++ tailWord_1476540) baseStart_1476540 baseEnd_1476540 := by
    simpa [prefixWord, tailWord_1476540, baseEnd_1476540] using wordTrace_append hprefix tailTrace_1476540
  have hstable : (prefixWord ++ tailWord_1476540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476540).length < 2 ^ (prefixWord ++ tailWord_1476540).sum := by decide
  have hdescent : baseEnd_1476540 < baseStart_1476540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476568 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_1476568 : Nat := 118140960795 + 1476568 * 2 ^ 59
def prefixEnd_1476568 : Nat := 4983230072969 + 3 ^ 40 * 1476568 * 2
def baseEnd_1476568 : Nat := 505459402032056103072929

theorem tailTrace_1476568 : CollatzResearch.WordTrace tailWord_1476568 prefixEnd_1476568 505459402032056103072929 := by
  unfold tailWord_1476568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927429657326894291307179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35903239543102525721742905 26927429657326894291307179)
  ·
    refine ⟨40391144485990341436960769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26927429657326894291307179 40391144485990341436960769)
    ·
      refine ⟨30293358364492756077720577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40391144485990341436960769 30293358364492756077720577)
      ·
        refine ⟨22720018773369567058290433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30293358364492756077720577 22720018773369567058290433)
        ·
          refine ⟨17040014080027175293717825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22720018773369567058290433 17040014080027175293717825)
          ·
            refine ⟨12780010560020381470288369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17040014080027175293717825 12780010560020381470288369)
            ·
              refine ⟨9585007920015286102716277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12780010560020381470288369 9585007920015286102716277)
              ·
                refine ⟨898594492501433072129651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9585007920015286102716277 898594492501433072129651)
                ·
                  refine ⟨1347891738752149608194477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898594492501433072129651 1347891738752149608194477)
                  ·
                    refine ⟨505459402032056103072929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347891738752149608194477 505459402032056103072929)
                    ·
                      rfl

theorem cell22_1476568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_1476568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476568 prefixEnd_1476568 := by exact prefixLift 1476568
  have htrace : WordTrace (prefixWord ++ tailWord_1476568) baseStart_1476568 baseEnd_1476568 := by
    simpa [prefixWord, tailWord_1476568, baseEnd_1476568] using wordTrace_append hprefix tailTrace_1476568
  have hstable : (prefixWord ++ tailWord_1476568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476568).length < 2 ^ (prefixWord ++ tailWord_1476568).sum := by decide
  have hdescent : baseEnd_1476568 < baseStart_1476568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476658 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_1476658 : Nat := 118140960795 + 1476658 * 2 ^ 59
def prefixEnd_1476658 : Nat := 4983230072969 + 3 ^ 40 * 1476658 * 2
def baseEnd_1476658 : Nat := 505490210871325868322653

theorem tailTrace_1476658 : CollatzResearch.WordTrace tailWord_1476658 prefixEnd_1476658 505490210871325868322653 := by
  unfold tailWord_1476658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13464535471081933488347657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35905427922885155968927085 13464535471081933488347657)
  ·
    refine ⟨10098401603311450116260743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13464535471081933488347657 10098401603311450116260743)
    ·
      refine ⟨15147602404967175174391115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098401603311450116260743 15147602404967175174391115)
      ·
        refine ⟨22721403607450762761586673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147602404967175174391115 22721403607450762761586673)
        ·
          refine ⟨17041052705588072071190005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22721403607450762761586673 17041052705588072071190005)
          ·
            refine ⟨1597598691148881756674063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17041052705588072071190005 1597598691148881756674063)
            ·
              refine ⟨2396398036723322635011095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597598691148881756674063 2396398036723322635011095)
              ·
                refine ⟨3594597055084983952516643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396398036723322635011095 3594597055084983952516643)
                ·
                  refine ⟨5391895582627475928774965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594597055084983952516643 5391895582627475928774965)
                  ·
                    refine ⟨505490210871325868322653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5391895582627475928774965 505490210871325868322653)
                    ·
                      rfl

theorem cell22_1476658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_1476658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476658 prefixEnd_1476658 := by exact prefixLift 1476658
  have htrace : WordTrace (prefixWord ++ tailWord_1476658) baseStart_1476658 baseEnd_1476658 := by
    simpa [prefixWord, tailWord_1476658, baseEnd_1476658] using wordTrace_append hprefix tailTrace_1476658
  have hstable : (prefixWord ++ tailWord_1476658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476658).length < 2 ^ (prefixWord ++ tailWord_1476658).sum := by decide
  have hdescent : baseEnd_1476658 < baseStart_1476658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476671 : List Nat := [1, 1, 2, 2, 3, 1, 6, 6]
def baseStart_1476671 : Nat := 118140960795 + 1476671 * 2 ^ 59
def prefixEnd_1476671 : Nat := 4983230072969 + 3 ^ 40 * 1476671 * 2
def baseEnd_1476671 : Nat := 56166073448555351971957

theorem tailTrace_1476671 : CollatzResearch.WordTrace tailWord_1476671 prefixEnd_1476671 56166073448555351971957 := by
  unfold tailWord_1476671
  simp only [CollatzResearch.WordTrace]
  refine ⟨53858616033280637173613867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35905744022187091449075911 53858616033280637173613867)
  ·
    refine ⟨80787924049920955760420801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53858616033280637173613867 80787924049920955760420801)
    ·
      refine ⟨60590943037440716820315601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80787924049920955760420801 60590943037440716820315601)
      ·
        refine ⟨45443207278080537615236701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60590943037440716820315601 45443207278080537615236701)
        ·
          refine ⟨17041202729280201605713763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45443207278080537615236701 17041202729280201605713763)
          ·
            refine ⟨25561804093920302408570645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17041202729280201605713763 25561804093920302408570645)
            ·
              refine ⟨1198209566902514175401749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25561804093920302408570645 1198209566902514175401749)
              ·
                refine ⟨56166073448555351971957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198209566902514175401749 56166073448555351971957)
                ·
                  rfl

theorem cell22_1476671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 6].length) (baseStart_1476671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476671 prefixEnd_1476671 := by exact prefixLift 1476671
  have htrace : WordTrace (prefixWord ++ tailWord_1476671) baseStart_1476671 baseEnd_1476671 := by
    simpa [prefixWord, tailWord_1476671, baseEnd_1476671] using wordTrace_append hprefix tailTrace_1476671
  have hstable : (prefixWord ++ tailWord_1476671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476671).length < 2 ^ (prefixWord ++ tailWord_1476671).sum := by decide
  have hdescent : baseEnd_1476671 < baseStart_1476671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476694 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1476694 : Nat := 118140960795 + 1476694 * 2 ^ 59
def prefixEnd_1476694 : Nat := 4983230072969 + 3 ^ 40 * 1476694 * 2
def baseEnd_1476694 : Nat := 168500844802344591474181

theorem tailTrace_1476694 : CollatzResearch.WordTrace tailWord_1476694 prefixEnd_1476694 168500844802344591474181 := by
  unfold tailWord_1476694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366215932012332006356321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35906303274798208067800757 3366215932012332006356321)
  ·
    refine ⟨2524661949009249004767241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3366215932012332006356321 2524661949009249004767241)
    ·
      refine ⟨1893496461756936753575431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2524661949009249004767241 1893496461756936753575431)
      ·
        refine ⟨2840244692635405130363147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893496461756936753575431 2840244692635405130363147)
        ·
          refine ⟨4260367038953107695544721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840244692635405130363147 4260367038953107695544721)
          ·
            refine ⟨3195275279214830771658541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260367038953107695544721 3195275279214830771658541)
            ·
              refine ⟨1198228229705561539371953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195275279214830771658541 1198228229705561539371953)
              ·
                refine ⟨898671172279171154528965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198228229705561539371953 898671172279171154528965)
                ·
                  refine ⟨168500844802344591474181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898671172279171154528965 168500844802344591474181)
                  ·
                    rfl

theorem cell22_1476694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1476694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476694 prefixEnd_1476694 := by exact prefixLift 1476694
  have htrace : WordTrace (prefixWord ++ tailWord_1476694) baseStart_1476694 baseEnd_1476694 := by
    simpa [prefixWord, tailWord_1476694, baseEnd_1476694] using wordTrace_append hprefix tailTrace_1476694
  have hstable : (prefixWord ++ tailWord_1476694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476694).length < 2 ^ (prefixWord ++ tailWord_1476694).sum := by decide
  have hdescent : baseEnd_1476694 < baseStart_1476694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476750 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_1476750 : Nat := 118140960795 + 1476750 * 2 ^ 59
def prefixEnd_1476750 : Nat := 4983230072969 + 3 ^ 40 * 1476750 * 2
def baseEnd_1476750 : Nat := 168507234783822765007457

theorem tailTrace_1476750 : CollatzResearch.WordTrace tailWord_1476750 prefixEnd_1476750 168507234783822765007457 := by
  unfold tailWord_1476750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732687174999304208217463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35907664933329622443826469 6732687174999304208217463)
  ·
    refine ⟨10099030762498956312326195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732687174999304208217463 10099030762498956312326195)
    ·
      refine ⟨15148546143748434468489293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099030762498956312326195 15148546143748434468489293)
      ·
        refine ⟨5680704803905662925683485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15148546143748434468489293 5680704803905662925683485)
        ·
          refine ⟨2130264301464623597131307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5680704803905662925683485 2130264301464623597131307)
          ·
            refine ⟨3195396452196935395696961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130264301464623597131307 3195396452196935395696961)
            ·
              refine ⟨2396547339147701546772721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195396452196935395696961 2396547339147701546772721)
              ·
                refine ⟨1797410504360776160079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396547339147701546772721 1797410504360776160079541)
                ·
                  refine ⟨168507234783822765007457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1797410504360776160079541 168507234783822765007457)
                  ·
                    rfl

theorem cell22_1476750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_1476750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476750 prefixEnd_1476750 := by exact prefixLift 1476750
  have htrace : WordTrace (prefixWord ++ tailWord_1476750) baseStart_1476750 baseEnd_1476750 := by
    simpa [prefixWord, tailWord_1476750, baseEnd_1476750] using wordTrace_append hprefix tailTrace_1476750
  have hstable : (prefixWord ++ tailWord_1476750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476750).length < 2 ^ (prefixWord ++ tailWord_1476750).sum := by decide
  have hdescent : baseEnd_1476750 < baseStart_1476750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476788 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1476788 : Nat := 118140960795 + 1476788 * 2 ^ 59
def prefixEnd_1476788 : Nat := 4983230072969 + 3 ^ 40 * 1476788 * 2
def baseEnd_1476788 : Nat := 505534712528048862572255

theorem tailTrace_1476788 : CollatzResearch.WordTrace tailWord_1476788 prefixEnd_1476788 505534712528048862572255 := by
  unfold tailWord_1476788
  simp only [CollatzResearch.WordTrace]
  refine ⟨26931441686928383077811509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35908588915904510770415345 26931441686928383077811509)
  ·
    refine ⟨2524822658149535913544829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26931441686928383077811509 2524822658149535913544829)
    ·
      refine ⟨946808496806075967579311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2524822658149535913544829 946808496806075967579311)
      ·
        refine ⟨1420212745209113951368967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946808496806075967579311 1420212745209113951368967)
        ·
          refine ⟨2130319117813670927053451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420212745209113951368967 2130319117813670927053451)
          ·
            refine ⟨3195478676720506390580177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130319117813670927053451 3195478676720506390580177)
            ·
              refine ⟨2396609007540379792935133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195478676720506390580177 2396609007540379792935133)
              ·
                refine ⟨898728377827642422350675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396609007540379792935133 898728377827642422350675)
                ·
                  refine ⟨1348092566741463633526013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898728377827642422350675 1348092566741463633526013)
                  ·
                    refine ⟨505534712528048862572255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348092566741463633526013 505534712528048862572255)
                    ·
                      rfl

theorem cell22_1476788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1476788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476788 prefixEnd_1476788 := by exact prefixLift 1476788
  have htrace : WordTrace (prefixWord ++ tailWord_1476788) baseStart_1476788 baseEnd_1476788 := by
    simpa [prefixWord, tailWord_1476788, baseEnd_1476788] using wordTrace_append hprefix tailTrace_1476788
  have hstable : (prefixWord ++ tailWord_1476788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476788).length < 2 ^ (prefixWord ++ tailWord_1476788).sum := by decide
  have hdescent : baseEnd_1476788 < baseStart_1476788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476793 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_1476793 : Nat := 118140960795 + 1476793 * 2 ^ 59
def prefixEnd_1476793 : Nat := 4983230072969 + 3 ^ 40 * 1476793 * 2
def baseEnd_1476793 : Nat := 505536424130230516197239

theorem tailTrace_1476793 : CollatzResearch.WordTrace tailWord_1476793 prefixEnd_1476793 505536424130230516197239 := by
  unfold tailWord_1476793
  simp only [CollatzResearch.WordTrace]
  refine ⟨53863065738838652009555033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35908710492559101339703355 53863065738838652009555033)
  ·
    refine ⟨40397299304128989007166275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53863065738838652009555033 40397299304128989007166275)
    ·
      refine ⟨60595948956193483510749413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40397299304128989007166275 60595948956193483510749413)
      ·
        refine ⟨11361740429286278158265515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60595948956193483510749413 11361740429286278158265515)
        ·
          refine ⟨17042610643929417237398273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11361740429286278158265515 17042610643929417237398273)
          ·
            refine ⟨12781957982947062928048705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17042610643929417237398273 12781957982947062928048705)
            ·
              refine ⟨9586468487210297196036529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12781957982947062928048705 9586468487210297196036529)
              ·
                refine ⟨7189851365407722897027397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9586468487210297196036529 7189851365407722897027397)
                ·
                  refine ⟨1348097131013948043192637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7189851365407722897027397 1348097131013948043192637)
                  ·
                    refine ⟨505536424130230516197239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348097131013948043192637 505536424130230516197239)
                    ·
                      rfl

theorem cell22_1476793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_1476793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476793 prefixEnd_1476793 := by exact prefixLift 1476793
  have htrace : WordTrace (prefixWord ++ tailWord_1476793) baseStart_1476793 baseEnd_1476793 := by
    simpa [prefixWord, tailWord_1476793, baseEnd_1476793] using wordTrace_append hprefix tailTrace_1476793
  have hstable : (prefixWord ++ tailWord_1476793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476793).length < 2 ^ (prefixWord ++ tailWord_1476793).sum := by decide
  have hdescent : baseEnd_1476793 < baseStart_1476793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476840 : List Nat := [2, 1, 4, 1, 2, 4, 2, 6]
def baseStart_1476840 : Nat := 118140960795 + 1476840 * 2 ^ 59
def prefixEnd_1476840 : Nat := 4983230072969 + 3 ^ 40 * 1476840 * 2
def baseEnd_1476840 : Nat := 56172501465637562252455

theorem tailTrace_1476840 : CollatzResearch.WordTrace tailWord_1476840 prefixEnd_1476840 56172501465637562252455 := by
  unfold tailWord_1476840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932389984834189518257987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35909853313112252691010649 26932389984834189518257987)
  ·
    refine ⟨40398584977251284277386981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26932389984834189518257987 40398584977251284277386981)
    ·
      refine ⟨7574734683234615802010059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40398584977251284277386981 7574734683234615802010059)
      ·
        refine ⟨11362102024851923703015089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574734683234615802010059 11362102024851923703015089)
        ·
          refine ⟨8521576518638942777261317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11362102024851923703015089 8521576518638942777261317)
          ·
            refine ⟨1597795597244801770736497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8521576518638942777261317 1597795597244801770736497)
            ·
              refine ⟨1198346697933601328052373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597795597244801770736497 1198346697933601328052373)
              ·
                refine ⟨56172501465637562252455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1198346697933601328052373 56172501465637562252455)
                ·
                  rfl

theorem cell22_1476840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_1476840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476840 prefixEnd_1476840 := by exact prefixLift 1476840
  have htrace : WordTrace (prefixWord ++ tailWord_1476840) baseStart_1476840 baseEnd_1476840 := by
    simpa [prefixWord, tailWord_1476840, baseEnd_1476840] using wordTrace_append hprefix tailTrace_1476840
  have hstable : (prefixWord ++ tailWord_1476840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476840).length < 2 ^ (prefixWord ++ tailWord_1476840).sum := by decide
  have hdescent : baseEnd_1476840 < baseStart_1476840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476851 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 9]
def baseStart_1476851 : Nat := 118140960795 + 1476851 * 2 ^ 59
def prefixEnd_1476851 : Nat := 4983230072969 + 3 ^ 40 * 1476851 * 2
def baseEnd_1476851 : Nat := 168518759571845899415687

theorem tailTrace_1476851 : CollatzResearch.WordTrace tailWord_1476851 prefixEnd_1476851 168518759571845899415687 := by
  unfold tailWord_1476851
  simp only [CollatzResearch.WordTrace]
  refine ⟨53865181172628527915166407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35910120781752351943444271 53865181172628527915166407)
  ·
    refine ⟨80797771758942791872749611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53865181172628527915166407 80797771758942791872749611)
    ·
      refine ⟨121196657638414187809124417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80797771758942791872749611 121196657638414187809124417)
      ·
        refine ⟨90897493228810640856843313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121196657638414187809124417 90897493228810640856843313)
        ·
          refine ⟨68173119921607980642632485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90897493228810640856843313 68173119921607980642632485)
          ·
            refine ⟨12782459985301496370493591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68173119921607980642632485 12782459985301496370493591)
            ·
              refine ⟨19173689977952244555740387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12782459985301496370493591 19173689977952244555740387)
              ·
                refine ⟨28760534966928366833610581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19173689977952244555740387 28760534966928366833610581)
                ·
                  refine ⟨168518759571845899415687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28760534966928366833610581 168518759571845899415687)
                  ·
                    rfl

theorem cell22_1476851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_1476851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476851 prefixEnd_1476851 := by exact prefixLift 1476851
  have htrace : WordTrace (prefixWord ++ tailWord_1476851) baseStart_1476851 baseEnd_1476851 := by
    simpa [prefixWord, tailWord_1476851, baseEnd_1476851] using wordTrace_append hprefix tailTrace_1476851
  have hstable : (prefixWord ++ tailWord_1476851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476851).length < 2 ^ (prefixWord ++ tailWord_1476851).sum := by decide
  have hdescent : baseEnd_1476851 < baseStart_1476851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476872 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1476872 : Nat := 118140960795 + 1476872 * 2 ^ 59
def prefixEnd_1476872 : Nat := 4983230072969 + 3 ^ 40 * 1476872 * 2
def baseEnd_1476872 : Nat := 505563467444700643471997

theorem tailTrace_1476872 : CollatzResearch.WordTrace tailWord_1476872 prefixEnd_1476872 505563467444700643471997 := by
  unfold tailWord_1476872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932973552776224250840435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35910631403701632334453913 26932973552776224250840435)
  ·
    refine ⟨40399460329164336376260653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26932973552776224250840435 40399460329164336376260653)
    ·
      refine ⟨15149797623436626141097745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40399460329164336376260653 15149797623436626141097745)
      ·
        refine ⟨11362348217577469605823309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15149797623436626141097745 11362348217577469605823309)
        ·
          refine ⟨4260880581591551102183741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11362348217577469605823309 4260880581591551102183741)
          ·
            refine ⟨1597830218096831663318903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4260880581591551102183741 1597830218096831663318903)
            ·
              refine ⟨2396745327145247494978355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597830218096831663318903 2396745327145247494978355)
              ·
                refine ⟨3595117990717871242467533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396745327145247494978355 3595117990717871242467533)
                ·
                  refine ⟨1348169246519201715925325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3595117990717871242467533 1348169246519201715925325)
                  ·
                    refine ⟨505563467444700643471997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348169246519201715925325 505563467444700643471997)
                    ·
                      rfl

theorem cell22_1476872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1476872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476872 prefixEnd_1476872 := by exact prefixLift 1476872
  have htrace : WordTrace (prefixWord ++ tailWord_1476872) baseStart_1476872 baseEnd_1476872 := by
    simpa [prefixWord, tailWord_1476872, baseEnd_1476872] using wordTrace_append hprefix tailTrace_1476872
  have hstable : (prefixWord ++ tailWord_1476872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476872).length < 2 ^ (prefixWord ++ tailWord_1476872).sum := by decide
  have hdescent : baseEnd_1476872 < baseStart_1476872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476885 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 5]
def baseStart_1476885 : Nat := 118140960795 + 1476885 * 2 ^ 59
def prefixEnd_1476885 : Nat := 4983230072969 + 3 ^ 40 * 1476885 * 2
def baseEnd_1476885 : Nat := 168522639203457647632319

theorem tailTrace_1476885 : CollatzResearch.WordTrace tailWord_1476885 prefixEnd_1476885 168522639203457647632319 := by
  unfold tailWord_1476885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53866421254505351721904109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35910947503003567814602739 53866421254505351721904109)
  ·
    refine ⟨20199907970439506895714041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53866421254505351721904109 20199907970439506895714041)
    ·
      refine ⟨15149930977829630171785531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20199907970439506895714041 15149930977829630171785531)
      ·
        refine ⟨22724896466744445257678297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149930977829630171785531 22724896466744445257678297)
        ·
          refine ⟨17043672350058333943258723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22724896466744445257678297 17043672350058333943258723)
          ·
            refine ⟨25565508525087500914888085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17043672350058333943258723 25565508525087500914888085)
            ·
              refine ⟨1198383212113476605385379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25565508525087500914888085 1198383212113476605385379)
              ·
                refine ⟨1797574818170214908078069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198383212113476605385379 1797574818170214908078069)
                ·
                  refine ⟨168522639203457647632319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1797574818170214908078069 168522639203457647632319)
                  ·
                    rfl

theorem cell22_1476885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_1476885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476885 prefixEnd_1476885 := by exact prefixLift 1476885
  have htrace : WordTrace (prefixWord ++ tailWord_1476885) baseStart_1476885 baseEnd_1476885 := by
    simpa [prefixWord, tailWord_1476885, baseEnd_1476885] using wordTrace_append hprefix tailTrace_1476885
  have hstable : (prefixWord ++ tailWord_1476885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476885).length < 2 ^ (prefixWord ++ tailWord_1476885).sum := by decide
  have hdescent : baseEnd_1476885 < baseStart_1476885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476945 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1476945 : Nat := 118140960795 + 1476945 * 2 ^ 59
def prefixEnd_1476945 : Nat := 4983230072969 + 3 ^ 40 * 1476945 * 2
def baseEnd_1476945 : Nat := 505588456836552786396773

theorem tailTrace_1476945 : CollatzResearch.WordTrace tailWord_1476945 prefixEnd_1476945 505588456836552786396773 := by
  unfold tailWord_1476945
  simp only [CollatzResearch.WordTrace]
  refine ⟨53868609634287981969088289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35912406422858654646058859 53868609634287981969088289)
  ·
    refine ⟨40401457225715986476816217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53868609634287981969088289 40401457225715986476816217)
    ·
      refine ⟨30301092919286989857612163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40401457225715986476816217 30301092919286989857612163)
      ·
        refine ⟨45451639378930484786418245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30301092919286989857612163 45451639378930484786418245)
        ·
          refine ⟨8522182383549465897453421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45451639378930484786418245 8522182383549465897453421)
          ·
            refine ⟨3195818393831049711545033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8522182383549465897453421 3195818393831049711545033)
            ·
              refine ⟨2396863795373287283658775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195818393831049711545033 2396863795373287283658775)
              ·
                refine ⟨3595295693059930925488163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396863795373287283658775 3595295693059930925488163)
                ·
                  refine ⟨5392943539589896388232245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595295693059930925488163 5392943539589896388232245)
                  ·
                    refine ⟨505588456836552786396773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5392943539589896388232245 505588456836552786396773)
                    ·
                      rfl

theorem cell22_1476945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1476945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476945 prefixEnd_1476945 := by exact prefixLift 1476945
  have htrace : WordTrace (prefixWord ++ tailWord_1476945) baseStart_1476945 baseEnd_1476945 := by
    simpa [prefixWord, tailWord_1476945, baseEnd_1476945] using wordTrace_append hprefix tailTrace_1476945
  have hstable : (prefixWord ++ tailWord_1476945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476945).length < 2 ^ (prefixWord ++ tailWord_1476945).sum := by decide
  have hdescent : baseEnd_1476945 < baseStart_1476945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476960 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_1476960 : Nat := 118140960795 + 1476960 * 2 ^ 59
def prefixEnd_1476960 : Nat := 4983230072969 + 3 ^ 40 * 1476960 * 2
def baseEnd_1476960 : Nat := 505593591643097747271727

theorem tailTrace_1476960 : CollatzResearch.WordTrace tailWord_1476960 prefixEnd_1476960 505593591643097747271727 := by
  unfold tailWord_1476960
  simp only [CollatzResearch.WordTrace]
  refine ⟨26934578364616819765442167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35912771152822426353922889 26934578364616819765442167)
  ·
    refine ⟨40401867546925229648163251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26934578364616819765442167 40401867546925229648163251)
    ·
      refine ⟨60602801320387844472244877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40401867546925229648163251 60602801320387844472244877)
      ·
        refine ⟨22726050495145441677091829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60602801320387844472244877 22726050495145441677091829)
        ·
          refine ⟨2130567233919885157227359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22726050495145441677091829 2130567233919885157227359)
          ·
            refine ⟨3195850850879827735841039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130567233919885157227359 3195850850879827735841039)
            ·
              refine ⟨4793776276319741603761559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195850850879827735841039 4793776276319741603761559)
              ·
                refine ⟨7190664414479612405642339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793776276319741603761559 7190664414479612405642339)
                ·
                  refine ⟨10785996621719418608463509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7190664414479612405642339 10785996621719418608463509)
                  ·
                    refine ⟨505593591643097747271727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10785996621719418608463509 505593591643097747271727)
                    ·
                      rfl

theorem cell22_1476960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_1476960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476960 prefixEnd_1476960 := by exact prefixLift 1476960
  have htrace : WordTrace (prefixWord ++ tailWord_1476960) baseStart_1476960 baseEnd_1476960 := by
    simpa [prefixWord, tailWord_1476960, baseEnd_1476960] using wordTrace_append hprefix tailTrace_1476960
  have hstable : (prefixWord ++ tailWord_1476960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476960).length < 2 ^ (prefixWord ++ tailWord_1476960).sum := by decide
  have hdescent : baseEnd_1476960 < baseStart_1476960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476988 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1476988 : Nat := 118140960795 + 1476988 * 2 ^ 59
def prefixEnd_1476988 : Nat := 4983230072969 + 3 ^ 40 * 1476988 * 2
def baseEnd_1476988 : Nat := 505603176615315007571641

theorem tailTrace_1476988 : CollatzResearch.WordTrace tailWord_1476988 prefixEnd_1476988 505603176615315007571641 := by
  unfold tailWord_1476988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935088986566100156451809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35913451982088133541935745 26935088986566100156451809)
  ·
    refine ⟨20201316739924575117338857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26935088986566100156451809 20201316739924575117338857)
    ·
      refine ⟨15150987554943431338004143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20201316739924575117338857 15150987554943431338004143)
      ·
        refine ⟨22726481332415147007006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150987554943431338004143 22726481332415147007006215)
        ·
          refine ⟨34089721998622720510509323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22726481332415147007006215 34089721998622720510509323)
          ·
            refine ⟨51134582997934080765763985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34089721998622720510509323 51134582997934080765763985)
            ·
              refine ⟨38350937248450560574322989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51134582997934080765763985 38350937248450560574322989)
              ·
                refine ⟨14381601468168960215371121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38350937248450560574322989 14381601468168960215371121)
                ·
                  refine ⟨10786201101126720161528341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14381601468168960215371121 10786201101126720161528341)
                  ·
                    refine ⟨505603176615315007571641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10786201101126720161528341 505603176615315007571641)
                    ·
                      rfl

theorem cell22_1476988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1476988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1476988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1476988 prefixEnd_1476988 := by exact prefixLift 1476988
  have htrace : WordTrace (prefixWord ++ tailWord_1476988) baseStart_1476988 baseEnd_1476988 := by
    simpa [prefixWord, tailWord_1476988, baseEnd_1476988] using wordTrace_append hprefix tailTrace_1476988
  have hstable : (prefixWord ++ tailWord_1476988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476988).length < 2 ^ (prefixWord ++ tailWord_1476988).sum := by decide
  have hdescent : baseEnd_1476988 < baseStart_1476988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477024 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_1477024 : Nat := 118140960795 + 1477024 * 2 ^ 59
def prefixEnd_1477024 : Nat := 4983230072969 + 3 ^ 40 * 1477024 * 2
def baseEnd_1477024 : Nat := 505615500151022913671531

theorem tailTrace_1477024 : CollatzResearch.WordTrace tailWord_1477024 prefixEnd_1477024 505615500151022913671531 := by
  unfold tailWord_1477024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935745500500889230607063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35914327334001185640809417 26935745500500889230607063)
  ·
    refine ⟨40403618250751333845910595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26935745500500889230607063 40403618250751333845910595)
    ·
      refine ⟨60605427376127000768865893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40403618250751333845910595 60605427376127000768865893)
      ·
        refine ⟨11363517633023812644162355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60605427376127000768865893 11363517633023812644162355)
        ·
          refine ⟨17045276449535718966243533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11363517633023812644162355 17045276449535718966243533)
          ·
            refine ⟨6391978668575894612341325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17045276449535718966243533 6391978668575894612341325)
            ·
              refine ⟨2396992000715960479627997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6391978668575894612341325 2396992000715960479627997)
              ·
                refine ⟨898872000268485179860499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396992000715960479627997 898872000268485179860499)
                ·
                  refine ⟨1348308000402727769790749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898872000268485179860499 1348308000402727769790749)
                  ·
                    refine ⟨505615500151022913671531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348308000402727769790749 505615500151022913671531)
                    ·
                      rfl

theorem cell22_1477024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_1477024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477024 prefixEnd_1477024 := by exact prefixLift 1477024
  have htrace : WordTrace (prefixWord ++ tailWord_1477024) baseStart_1477024 baseEnd_1477024 := by
    simpa [prefixWord, tailWord_1477024, baseEnd_1477024] using wordTrace_append hprefix tailTrace_1477024
  have hstable : (prefixWord ++ tailWord_1477024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477024).length < 2 ^ (prefixWord ++ tailWord_1477024).sum := by decide
  have hdescent : baseEnd_1477024 < baseStart_1477024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477041 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_1477041 : Nat := 118140960795 + 1477041 * 2 ^ 59
def prefixEnd_1477041 : Nat := 4983230072969 + 3 ^ 40 * 1477041 * 2
def baseEnd_1477041 : Nat := 505621319598440535996479

theorem tailTrace_1477041 : CollatzResearch.WordTrace tailWord_1477041 prefixEnd_1477041 505621319598440535996479 := by
  unfold tailWord_1477041
  simp only [CollatzResearch.WordTrace]
  refine ⟨53872111041940190364582977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35914740694626793576388651 53872111041940190364582977)
  ·
    refine ⟨40404083281455142773437233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53872111041940190364582977 40404083281455142773437233)
    ·
      refine ⟨30303062461091357080077925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40404083281455142773437233 30303062461091357080077925)
      ·
        refine ⟨5681824211454629452514611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30303062461091357080077925 5681824211454629452514611)
        ·
          refine ⟨8522736317181944178771917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681824211454629452514611 8522736317181944178771917)
          ·
            refine ⟨3196026118943229067039469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8522736317181944178771917 3196026118943229067039469)
            ·
              refine ⟨1198509794603710900139801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3196026118943229067039469 1198509794603710900139801)
              ·
                refine ⟨898882345952783175104851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198509794603710900139801 898882345952783175104851)
                ·
                  refine ⟨1348323518929174762657277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898882345952783175104851 1348323518929174762657277)
                  ·
                    refine ⟨505621319598440535996479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348323518929174762657277 505621319598440535996479)
                    ·
                      rfl

theorem cell22_1477041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_1477041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477041 prefixEnd_1477041 := by exact prefixLift 1477041
  have htrace : WordTrace (prefixWord ++ tailWord_1477041) baseStart_1477041 baseEnd_1477041 := by
    simpa [prefixWord, tailWord_1477041, baseEnd_1477041] using wordTrace_append hprefix tailTrace_1477041
  have hstable : (prefixWord ++ tailWord_1477041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477041).length < 2 ^ (prefixWord ++ tailWord_1477041).sum := by decide
  have hdescent : baseEnd_1477041 < baseStart_1477041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477082 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_1477082 : Nat := 118140960795 + 1477082 * 2 ^ 59
def prefixEnd_1477082 : Nat := 4983230072969 + 3 ^ 40 * 1477082 * 2
def baseEnd_1477082 : Nat := 168545118245443365240451

theorem tailTrace_1477082 : CollatzResearch.WordTrace tailWord_1477082 prefixEnd_1477082 168545118245443365240451 := by
  unfold tailWord_1477082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468401608697913591706375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35915737623194436244550333 13468401608697913591706375)
  ·
    refine ⟨20202602413046870387559563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13468401608697913591706375 20202602413046870387559563)
    ·
      refine ⟨30303903619570305581339345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20202602413046870387559563 30303903619570305581339345)
      ·
        refine ⟨22727927714677729186004509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30303903619570305581339345 22727927714677729186004509)
        ·
          refine ⟨8522972893004148444751691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22727927714677729186004509 8522972893004148444751691)
          ·
            refine ⟨12784459339506222667127537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522972893004148444751691 12784459339506222667127537)
            ·
              refine ⟨9588344504629667000345653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784459339506222667127537 9588344504629667000345653)
              ·
                refine ⟨898907297309031281282405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9588344504629667000345653 898907297309031281282405)
                ·
                  refine ⟨168545118245443365240451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898907297309031281282405 168545118245443365240451)
                  ·
                    rfl

theorem cell22_1477082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_1477082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477082 prefixEnd_1477082 := by exact prefixLift 1477082
  have htrace : WordTrace (prefixWord ++ tailWord_1477082) baseStart_1477082 baseEnd_1477082 := by
    simpa [prefixWord, tailWord_1477082, baseEnd_1477082] using wordTrace_append hprefix tailTrace_1477082
  have hstable : (prefixWord ++ tailWord_1477082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477082).length < 2 ^ (prefixWord ++ tailWord_1477082).sum := by decide
  have hdescent : baseEnd_1477082 < baseStart_1477082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477133 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1477133 : Nat := 118140960795 + 1477133 * 2 ^ 59
def prefixEnd_1477133 : Nat := 4983230072969 + 3 ^ 40 * 1477133 * 2
def baseEnd_1477133 : Nat := 168550937692860987565399

theorem tailTrace_1477133 : CollatzResearch.WordTrace tailWord_1477133 prefixEnd_1477133 168550937692860987565399 := by
  unfold tailWord_1477133
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875466557606890076932053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35916977705071260051288035 53875466557606890076932053)
  ·
    refine ⟨1262706247443911486178095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 53875466557606890076932053 1262706247443911486178095)
    ·
      refine ⟨1894059371165867229267143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262706247443911486178095 1894059371165867229267143)
      ·
        refine ⟨2841089056748800843900715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894059371165867229267143 2841089056748800843900715)
        ·
          refine ⟨4261633585123201265851073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841089056748800843900715 4261633585123201265851073)
          ·
            refine ⟨3196225188842400949388305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261633585123201265851073 3196225188842400949388305)
            ·
              refine ⟨2397168891631800712041229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196225188842400949388305 2397168891631800712041229)
              ·
                refine ⟨898938334361925267015461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2397168891631800712041229 898938334361925267015461)
                ·
                  refine ⟨168550937692860987565399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 898938334361925267015461 168550937692860987565399)
                  ·
                    rfl

theorem cell22_1477133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1477133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477133 prefixEnd_1477133 := by exact prefixLift 1477133
  have htrace : WordTrace (prefixWord ++ tailWord_1477133) baseStart_1477133 baseEnd_1477133 := by
    simpa [prefixWord, tailWord_1477133, baseEnd_1477133] using wordTrace_append hprefix tailTrace_1477133
  have hstable : (prefixWord ++ tailWord_1477133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477133).length < 2 ^ (prefixWord ++ tailWord_1477133).sum := by decide
  have hdescent : baseEnd_1477133 < baseStart_1477133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477165 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1477165 : Nat := 118140960795 + 1477165 * 2 ^ 59
def prefixEnd_1477165 : Nat := 4983230072969 + 3 ^ 40 * 1477165 * 2
def baseEnd_1477165 : Nat := 505663767332545545896099

theorem tailTrace_1477165 : CollatzResearch.WordTrace tailWord_1477165 prefixEnd_1477165 505663767332545545896099 := by
  unfold tailWord_1477165
  simp only [CollatzResearch.WordTrace]
  refine ⟨53876633693490959542096949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35917755795660639694731299 53876633693490959542096949)
  ·
    refine ⟨5050934408764777457071589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53876633693490959542096949 5050934408764777457071589)
    ·
      refine ⟨947050201643395773200923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5050934408764777457071589 947050201643395773200923)
      ·
        refine ⟨1420575302465093659801385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947050201643395773200923 1420575302465093659801385)
        ·
          refine ⟨1065431476848820244851039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420575302465093659801385 1065431476848820244851039)
          ·
            refine ⟨1598147215273230367276559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065431476848820244851039 1598147215273230367276559)
            ·
              refine ⟨2397220822909845550914839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598147215273230367276559 2397220822909845550914839)
              ·
                refine ⟨3595831234364768326372259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397220822909845550914839 3595831234364768326372259)
                ·
                  refine ⟨5393746851547152489558389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595831234364768326372259 5393746851547152489558389)
                  ·
                    refine ⟨505663767332545545896099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5393746851547152489558389 505663767332545545896099)
                    ·
                      rfl

theorem cell22_1477165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1477165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477165 prefixEnd_1477165 := by exact prefixLift 1477165
  have htrace : WordTrace (prefixWord ++ tailWord_1477165) baseStart_1477165 baseEnd_1477165 := by
    simpa [prefixWord, tailWord_1477165, baseEnd_1477165] using wordTrace_append hprefix tailTrace_1477165
  have hstable : (prefixWord ++ tailWord_1477165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477165).length < 2 ^ (prefixWord ++ tailWord_1477165).sum := by decide
  have hdescent : baseEnd_1477165 < baseStart_1477165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477217 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 6]
def baseStart_1477217 : Nat := 118140960795 + 1477217 * 2 ^ 59
def prefixEnd_1477217 : Nat := 4983230072969 + 3 ^ 40 * 1477217 * 2
def baseEnd_1477217 : Nat := 168560522665078247865313

theorem tailTrace_1477217 : CollatzResearch.WordTrace tailWord_1477217 prefixEnd_1477217 168560522665078247865313 := by
  unfold tailWord_1477217
  simp only [CollatzResearch.WordTrace]
  refine ⟨53878530289302572422989905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35919020192868381615326603 53878530289302572422989905)
  ·
    refine ⟨40408897716976929317242429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53878530289302572422989905 40408897716976929317242429)
    ·
      refine ⟨15153336643866348493965911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40408897716976929317242429 15153336643866348493965911)
      ·
        refine ⟨22730004965799522740948867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15153336643866348493965911 22730004965799522740948867)
        ·
          refine ⟨34095007448699284111423301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22730004965799522740948867 34095007448699284111423301)
          ·
            refine ⟨6392813896631115770891869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34095007448699284111423301 6392813896631115770891869)
            ·
              refine ⟨2397305211236668414084451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6392813896631115770891869 2397305211236668414084451)
              ·
                refine ⟨3595957816855002621126677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397305211236668414084451 3595957816855002621126677)
                ·
                  refine ⟨168560522665078247865313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3595957816855002621126677 168560522665078247865313)
                  ·
                    rfl

theorem cell22_1477217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_1477217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477217 prefixEnd_1477217 := by exact prefixLift 1477217
  have htrace : WordTrace (prefixWord ++ tailWord_1477217) baseStart_1477217 baseEnd_1477217 := by
    simpa [prefixWord, tailWord_1477217, baseEnd_1477217] using wordTrace_append hprefix tailTrace_1477217
  have hstable : (prefixWord ++ tailWord_1477217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477217).length < 2 ^ (prefixWord ++ tailWord_1477217).sum := by decide
  have hdescent : baseEnd_1477217 < baseStart_1477217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477266 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1477266 : Nat := 118140960795 + 1477266 * 2 ^ 59
def prefixEnd_1477266 : Nat := 4983230072969 + 3 ^ 40 * 1477266 * 2
def baseEnd_1477266 : Nat := 505698341696614949120789

theorem tailTrace_1477266 : CollatzResearch.WordTrace tailWord_1477266 prefixEnd_1477266 505698341696614949120789 := by
  unfold tailWord_1477266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470079366531263447880913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35920211644083369194349101 13470079366531263447880913)
  ·
    refine ⟨10102559524898447585910685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13470079366531263447880913 10102559524898447585910685)
    ·
      refine ⟨3788459821836917844716507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10102559524898447585910685 3788459821836917844716507)
      ·
        refine ⟨5682689732755376767074761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788459821836917844716507 5682689732755376767074761)
        ·
          refine ⟨4262017299566532575306071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5682689732755376767074761 4262017299566532575306071)
          ·
            refine ⟨6393025949349798862959107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262017299566532575306071 6393025949349798862959107)
            ·
              refine ⟨9589538924024698294438661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393025949349798862959107 9589538924024698294438661)
              ·
                refine ⟨1798038548254630930207249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9589538924024698294438661 1798038548254630930207249)
                ·
                  refine ⟨1348528911190973197655437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798038548254630930207249 1348528911190973197655437)
                  ·
                    refine ⟨505698341696614949120789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348528911190973197655437 505698341696614949120789)
                    ·
                      rfl

theorem cell22_1477266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1477266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477266 prefixEnd_1477266 := by exact prefixLift 1477266
  have htrace : WordTrace (prefixWord ++ tailWord_1477266) baseStart_1477266 baseEnd_1477266 := by
    simpa [prefixWord, tailWord_1477266, baseEnd_1477266] using wordTrace_append hprefix tailTrace_1477266
  have hstable : (prefixWord ++ tailWord_1477266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477266).length < 2 ^ (prefixWord ++ tailWord_1477266).sum := by decide
  have hdescent : baseEnd_1477266 < baseStart_1477266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477268 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1477268 : Nat := 118140960795 + 1477268 * 2 ^ 59
def prefixEnd_1477268 : Nat := 4983230072969 + 3 ^ 40 * 1477268 * 2
def baseEnd_1477268 : Nat := 168566342112495870190261

theorem tailTrace_1477268 : CollatzResearch.WordTrace tailWord_1477268 prefixEnd_1477268 168566342112495870190261 := by
  unfold tailWord_1477268
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940195206058904066548229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35920260274745205422064305 26940195206058904066548229)
  ·
    refine ⟨5051286601136044512477793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26940195206058904066548229 5051286601136044512477793)
    ·
      refine ⟨3788464950852033384358345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051286601136044512477793 3788464950852033384358345)
      ·
        refine ⟨2841348713139025038268759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3788464950852033384358345 2841348713139025038268759)
        ·
          refine ⟨4262023069708537557403139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841348713139025038268759 4262023069708537557403139)
          ·
            refine ⟨6393034604562806336104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262023069708537557403139 6393034604562806336104709)
            ·
              refine ⟨1198693988355526188019633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6393034604562806336104709 1198693988355526188019633)
              ·
                refine ⟨899020491266644641014725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198693988355526188019633 899020491266644641014725)
                ·
                  refine ⟨168566342112495870190261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899020491266644641014725 168566342112495870190261)
                  ·
                    rfl

theorem cell22_1477268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1477268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477268 prefixEnd_1477268 := by exact prefixLift 1477268
  have htrace : WordTrace (prefixWord ++ tailWord_1477268) baseStart_1477268 baseEnd_1477268 := by
    simpa [prefixWord, tailWord_1477268, baseEnd_1477268] using wordTrace_append hprefix tailTrace_1477268
  have hstable : (prefixWord ++ tailWord_1477268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477268).length < 2 ^ (prefixWord ++ tailWord_1477268).sum := by decide
  have hdescent : baseEnd_1477268 < baseStart_1477268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477311 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 1, 3]
def baseStart_1477311 : Nat := 118140960795 + 1477311 * 2 ^ 59
def prefixEnd_1477311 : Nat := 4983230072969 + 3 ^ 40 * 1477311 * 2
def baseEnd_1477311 : Nat := 505713746116249831745651

theorem tailTrace_1477311 : CollatzResearch.WordTrace tailWord_1477311 prefixEnd_1477311 505713746116249831745651 := by
  unfold tailWord_1477311
  simp only [CollatzResearch.WordTrace]
  refine ⟨53881958750962026476911787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35921305833974684317941191 53881958750962026476911787)
  ·
    refine ⟨80822938126443039715367681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53881958750962026476911787 80822938126443039715367681)
    ·
      refine ⟨60617203594832279786525761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80822938126443039715367681 60617203594832279786525761)
      ·
        refine ⟨45462902696124209839894321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60617203594832279786525761 45462902696124209839894321)
        ·
          refine ⟨34097177022093157379920741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45462902696124209839894321 34097177022093157379920741)
          ·
            refine ⟨6393220691642467008735139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34097177022093157379920741 6393220691642467008735139)
            ·
              refine ⟨9589831037463700513102709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393220691642467008735139 9589831037463700513102709)
              ·
                refine ⟨899046659762221923103379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9589831037463700513102709 899046659762221923103379)
                ·
                  refine ⟨1348569989643332884655069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899046659762221923103379 1348569989643332884655069)
                  ·
                    refine ⟨505713746116249831745651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348569989643332884655069 505713746116249831745651)
                    ·
                      rfl

theorem cell22_1477311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_1477311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477311 prefixEnd_1477311 := by exact prefixLift 1477311
  have htrace : WordTrace (prefixWord ++ tailWord_1477311) baseStart_1477311 baseEnd_1477311 := by
    simpa [prefixWord, tailWord_1477311, baseEnd_1477311] using wordTrace_append hprefix tailTrace_1477311
  have hstable : (prefixWord ++ tailWord_1477311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477311).length < 2 ^ (prefixWord ++ tailWord_1477311).sum := by decide
  have hdescent : baseEnd_1477311 < baseStart_1477311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477324 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1477324 : Nat := 118140960795 + 1477324 * 2 ^ 59
def prefixEnd_1477324 : Nat := 4983230072969 + 3 ^ 40 * 1477324 * 2
def baseEnd_1477324 : Nat := 168572732093974043723537

theorem tailTrace_1477324 : CollatzResearch.WordTrace tailWord_1477324 prefixEnd_1477324 168572732093974043723537 := by
  unfold tailWord_1477324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26941216449957464848567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35921621933276619798090017 26941216449957464848567513)
  ·
    refine ⟨20205912337468098636425635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26941216449957464848567513 20205912337468098636425635)
    ·
      refine ⟨30308868506202147954638453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205912337468098636425635 30308868506202147954638453)
      ·
        refine ⟨2841456422456451370747355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30308868506202147954638453 2841456422456451370747355)
        ·
          refine ⟨4262184633684677056121033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841456422456451370747355 4262184633684677056121033)
          ·
            refine ⟨3196638475263507792090775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262184633684677056121033 3196638475263507792090775)
            ·
              refine ⟨4794957712895261688136163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196638475263507792090775 4794957712895261688136163)
              ·
                refine ⟨7192436569342892532204245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794957712895261688136163 7192436569342892532204245)
                ·
                  refine ⟨168572732093974043723537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7192436569342892532204245 168572732093974043723537)
                  ·
                    rfl

theorem cell22_1477324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1477324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477324 prefixEnd_1477324 := by exact prefixLift 1477324
  have htrace : WordTrace (prefixWord ++ tailWord_1477324) baseStart_1477324 baseEnd_1477324 := by
    simpa [prefixWord, tailWord_1477324, baseEnd_1477324] using wordTrace_append hprefix tailTrace_1477324
  have hstable : (prefixWord ++ tailWord_1477324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477324).length < 2 ^ (prefixWord ++ tailWord_1477324).sum := by decide
  have hdescent : baseEnd_1477324 < baseStart_1477324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477367 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1477367 : Nat := 118140960795 + 1477367 * 2 ^ 59
def prefixEnd_1477367 : Nat := 4983230072969 + 3 ^ 40 * 1477367 * 2
def baseEnd_1477367 : Nat := 505732916060684352345479

theorem tailTrace_1477367 : CollatzResearch.WordTrace tailWord_1477367 prefixEnd_1477367 505732916060684352345479 := by
  unfold tailWord_1477367
  simp only [CollatzResearch.WordTrace]
  refine ⟨53884001238759148040950355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35922667492506098693966903 53884001238759148040950355)
  ·
    refine ⟨80826001858138722061425533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53884001238759148040950355 80826001858138722061425533)
    ·
      refine ⟨30309750696802020773034575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80826001858138722061425533 30309750696802020773034575)
      ·
        refine ⟨45464626045203031159551863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30309750696802020773034575 45464626045203031159551863)
        ·
          refine ⟨68196939067804546739327795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45464626045203031159551863 68196939067804546739327795)
          ·
            refine ⟨102295408601706820108991693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68196939067804546739327795 102295408601706820108991693)
            ·
              refine ⟨38360778225640057540871885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102295408601706820108991693 38360778225640057540871885)
              ·
                refine ⟨14385291834615021577826957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38360778225640057540871885 14385291834615021577826957)
                ·
                  refine ⟨5394484437980633091685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14385291834615021577826957 5394484437980633091685109)
                  ·
                    refine ⟨505732916060684352345479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5394484437980633091685109 505732916060684352345479)
                    ·
                      rfl

theorem cell22_1477367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1477367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477367 prefixEnd_1477367 := by exact prefixLift 1477367
  have htrace : WordTrace (prefixWord ++ tailWord_1477367) baseStart_1477367 baseEnd_1477367 := by
    simpa [prefixWord, tailWord_1477367, baseEnd_1477367] using wordTrace_append hprefix tailTrace_1477367
  have hstable : (prefixWord ++ tailWord_1477367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477367).length < 2 ^ (prefixWord ++ tailWord_1477367).sum := by decide
  have hdescent : baseEnd_1477367 < baseStart_1477367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477405 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1477405 : Nat := 118140960795 + 1477405 * 2 ^ 59
def prefixEnd_1477405 : Nat := 4983230072969 + 3 ^ 40 * 1477405 * 2
def baseEnd_1477405 : Nat := 505745924237264919895363

theorem tailTrace_1477405 : CollatzResearch.WordTrace tailWord_1477405 prefixEnd_1477405 505745924237264919895363 := by
  unfold tailWord_1477405
  simp only [CollatzResearch.WordTrace]
  refine ⟨53885387212621480530833669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35923591475080987020555779 53885387212621480530833669)
  ·
    refine ⟨10103510102366527599531313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53885387212621480530833669 10103510102366527599531313)
    ·
      refine ⟨7577632576774895699648485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10103510102366527599531313 7577632576774895699648485)
      ·
        refine ⟨1420806108145292943684091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7577632576774895699648485 1420806108145292943684091)
        ·
          refine ⟨2131209162217939415526137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420806108145292943684091 2131209162217939415526137)
          ·
            refine ⟨1598406871663454561644603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131209162217939415526137 1598406871663454561644603)
            ·
              refine ⟨2397610307495181842466905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598406871663454561644603 2397610307495181842466905)
              ·
                refine ⟨1798207730621386381850179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397610307495181842466905 1798207730621386381850179)
                ·
                  refine ⟨2697311595932079572775269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798207730621386381850179 2697311595932079572775269)
                  ·
                    refine ⟨505745924237264919895363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697311595932079572775269 505745924237264919895363)
                    ·
                      rfl

theorem cell22_1477405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1477405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477405 prefixEnd_1477405 := by exact prefixLift 1477405
  have htrace : WordTrace (prefixWord ++ tailWord_1477405) baseStart_1477405 baseEnd_1477405 := by
    simpa [prefixWord, tailWord_1477405, baseEnd_1477405] using wordTrace_append hprefix tailTrace_1477405
  have hstable : (prefixWord ++ tailWord_1477405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477405).length < 2 ^ (prefixWord ++ tailWord_1477405).sum := by decide
  have hdescent : baseEnd_1477405 < baseStart_1477405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477416 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1477416 : Nat := 118140960795 + 1477416 * 2 ^ 59
def prefixEnd_1477416 : Nat := 4983230072969 + 3 ^ 40 * 1477416 * 2
def baseEnd_1477416 : Nat := 505749689762064557870329

theorem tailTrace_1477416 : CollatzResearch.WordTrace tailWord_1477416 prefixEnd_1477416 505749689762064557870329 := by
  unfold tailWord_1477416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942894207790814704742051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35923858943721086272989401 26942894207790814704742051)
  ·
    refine ⟨40414341311686222057113077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942894207790814704742051 40414341311686222057113077)
    ·
      refine ⟨3788844497970583317854351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40414341311686222057113077 3788844497970583317854351)
      ·
        refine ⟨5683266746955874976781527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788844497970583317854351 5683266746955874976781527)
        ·
          refine ⟨8524900120433812465172291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683266746955874976781527 8524900120433812465172291)
          ·
            refine ⟨12787350180650718697758437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8524900120433812465172291 12787350180650718697758437)
            ·
              refine ⟨2397628158872009755829707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12787350180650718697758437 2397628158872009755829707)
              ·
                refine ⟨3596442238308014633744561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397628158872009755829707 3596442238308014633744561)
                ·
                  refine ⟨2697331678731010975308421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596442238308014633744561 2697331678731010975308421)
                  ·
                    refine ⟨505749689762064557870329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697331678731010975308421 505749689762064557870329)
                    ·
                      rfl

theorem cell22_1477416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1477416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477416 prefixEnd_1477416 := by exact prefixLift 1477416
  have htrace : WordTrace (prefixWord ++ tailWord_1477416) baseStart_1477416 baseEnd_1477416 := by
    simpa [prefixWord, tailWord_1477416, baseEnd_1477416] using wordTrace_append hprefix tailTrace_1477416
  have hstable : (prefixWord ++ tailWord_1477416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477416).length < 2 ^ (prefixWord ++ tailWord_1477416).sum := by decide
  have hdescent : baseEnd_1477416 < baseStart_1477416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477418 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1477418 : Nat := 118140960795 + 1477418 * 2 ^ 59
def prefixEnd_1477418 : Nat := 4983230072969 + 3 ^ 40 * 1477418 * 2
def baseEnd_1477418 : Nat := 505750374402937219320323

theorem tailTrace_1477418 : CollatzResearch.WordTrace tailWord_1477418 prefixEnd_1477418 505750374402937219320323 := by
  unfold tailWord_1477418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471465340393595937764227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35923907574382922500704605 13471465340393595937764227)
  ·
    refine ⟨20207198010590393906646341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471465340393595937764227 20207198010590393906646341)
    ·
      refine ⟨3788849626985698857496189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20207198010590393906646341 3788849626985698857496189)
      ·
        refine ⟨1420818610119637071561071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3788849626985698857496189 1420818610119637071561071)
        ·
          refine ⟨2131227915179455607341607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420818610119637071561071 2131227915179455607341607)
          ·
            refine ⟨3196841872769183411012411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131227915179455607341607 3196841872769183411012411)
            ·
              refine ⟨4795262809153775116518617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196841872769183411012411 4795262809153775116518617)
              ·
                refine ⟨3596447106865331337388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795262809153775116518617 3596447106865331337388963)
                ·
                  refine ⟨5394670660297997006083445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596447106865331337388963 5394670660297997006083445)
                  ·
                    refine ⟨505750374402937219320323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5394670660297997006083445 505750374402937219320323)
                    ·
                      rfl

theorem cell22_1477418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1477418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477418 prefixEnd_1477418 := by exact prefixLift 1477418
  have htrace : WordTrace (prefixWord ++ tailWord_1477418) baseStart_1477418 baseEnd_1477418 := by
    simpa [prefixWord, tailWord_1477418, baseEnd_1477418] using wordTrace_append hprefix tailTrace_1477418
  have hstable : (prefixWord ++ tailWord_1477418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477418).length < 2 ^ (prefixWord ++ tailWord_1477418).sum := by decide
  have hdescent : baseEnd_1477418 < baseStart_1477418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477437 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1477437 : Nat := 118140960795 + 1477437 * 2 ^ 59
def prefixEnd_1477437 : Nat := 4983230072969 + 3 ^ 40 * 1477437 * 2
def baseEnd_1477437 : Nat := 168585626163742501031755

theorem tailTrace_1477437 : CollatzResearch.WordTrace tailWord_1477437 prefixEnd_1477437 168585626163742501031755 := by
  unfold tailWord_1477437
  simp only [CollatzResearch.WordTrace]
  refine ⟨53886554348505549995998565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35924369565670366663999043 53886554348505549995998565)
  ·
    refine ⟨10103728940344790624249731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53886554348505549995998565 10103728940344790624249731)
    ·
      refine ⟨15155593410517185936374597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10103728940344790624249731 15155593410517185936374597)
      ·
        refine ⟨2841673764471972363070237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15155593410517185936374597 2841673764471972363070237)
        ·
          refine ⟨1065627661676989636151339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2841673764471972363070237 1065627661676989636151339)
          ·
            refine ⟨1598441492515484454227009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065627661676989636151339 1598441492515484454227009)
            ·
              refine ⟨1198831119386613340670257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598441492515484454227009 1198831119386613340670257)
              ·
                refine ⟨899123339539960005502693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198831119386613340670257 899123339539960005502693)
                ·
                  refine ⟨168585626163742501031755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899123339539960005502693 168585626163742501031755)
                  ·
                    rfl

theorem cell22_1477437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1477437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477437 prefixEnd_1477437 := by exact prefixLift 1477437
  have htrace : WordTrace (prefixWord ++ tailWord_1477437) baseStart_1477437 baseEnd_1477437 := by
    simpa [prefixWord, tailWord_1477437, baseEnd_1477437] using wordTrace_append hprefix tailTrace_1477437
  have hstable : (prefixWord ++ tailWord_1477437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477437).length < 2 ^ (prefixWord ++ tailWord_1477437).sum := by decide
  have hdescent : baseEnd_1477437 < baseStart_1477437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477480 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1477480 : Nat := 118140960795 + 1477480 * 2 ^ 59
def prefixEnd_1477480 : Nat := 4983230072969 + 3 ^ 40 * 1477480 * 2
def baseEnd_1477480 : Nat := 505771598269989724270133

theorem tailTrace_1477480 : CollatzResearch.WordTrace tailWord_1477480 prefixEnd_1477480 505771598269989724270133 := by
  unfold tailWord_1477480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26944061343674884169906947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35925415124899845559875929 26944061343674884169906947)
  ·
    refine ⟨40416092015512326254860421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26944061343674884169906947 40416092015512326254860421)
    ·
      refine ⟨7578017252908561172786329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40416092015512326254860421 7578017252908561172786329)
      ·
        refine ⟨5683512939681420879589747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7578017252908561172786329 5683512939681420879589747)
        ·
          refine ⟨8525269409522131319384621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683512939681420879589747 8525269409522131319384621)
          ·
            refine ⟨3196976028570799244769233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8525269409522131319384621 3196976028570799244769233)
            ·
              refine ⟨2397732021428099433576925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196976028570799244769233 2397732021428099433576925)
              ·
                refine ⟨899149508035537287591347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2397732021428099433576925 899149508035537287591347)
                ·
                  refine ⟨1348724262053305931387021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899149508035537287591347 1348724262053305931387021)
                  ·
                    refine ⟨505771598269989724270133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348724262053305931387021 505771598269989724270133)
                    ·
                      rfl

theorem cell22_1477480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1477480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477480 prefixEnd_1477480 := by exact prefixLift 1477480
  have htrace : WordTrace (prefixWord ++ tailWord_1477480) baseStart_1477480 baseEnd_1477480 := by
    simpa [prefixWord, tailWord_1477480, baseEnd_1477480] using wordTrace_append hprefix tailTrace_1477480
  have hstable : (prefixWord ++ tailWord_1477480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477480).length < 2 ^ (prefixWord ++ tailWord_1477480).sum := by decide
  have hdescent : baseEnd_1477480 < baseStart_1477480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477493 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 5]
def baseStart_1477493 : Nat := 118140960795 + 1477493 * 2 ^ 59
def prefixEnd_1477493 : Nat := 4983230072969 + 3 ^ 40 * 1477493 * 2
def baseEnd_1477493 : Nat := 168592016145220674565031

theorem tailTrace_1477493 : CollatzResearch.WordTrace tailWord_1477493 prefixEnd_1477493 168592016145220674565031 := by
  unfold tailWord_1477493
  simp only [CollatzResearch.WordTrace]
  refine ⟨53888596836302671560037133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35925731224201781040024755 53888596836302671560037133)
  ·
    refine ⟨20208223813613501835013925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53888596836302671560037133 20208223813613501835013925)
    ·
      refine ⟨3789041965052531594065111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20208223813613501835013925 3789041965052531594065111)
      ·
        refine ⟨5683562947578797391097667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789041965052531594065111 5683562947578797391097667)
        ·
          refine ⟨8525344421368196086646501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683562947578797391097667 8525344421368196086646501)
          ·
            refine ⟨1598502079006536766246219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8525344421368196086646501 1598502079006536766246219)
            ·
              refine ⟨2397753118509805149369329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598502079006536766246219 2397753118509805149369329)
              ·
                refine ⟨1798314838882353862026997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397753118509805149369329 1798314838882353862026997)
                ·
                  refine ⟨168592016145220674565031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1798314838882353862026997 168592016145220674565031)
                  ·
                    rfl

theorem cell22_1477493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_1477493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477493 prefixEnd_1477493 := by exact prefixLift 1477493
  have htrace : WordTrace (prefixWord ++ tailWord_1477493) baseStart_1477493 baseEnd_1477493 := by
    simpa [prefixWord, tailWord_1477493, baseEnd_1477493] using wordTrace_append hprefix tailTrace_1477493
  have hstable : (prefixWord ++ tailWord_1477493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477493).length < 2 ^ (prefixWord ++ tailWord_1477493).sum := by decide
  have hdescent : baseEnd_1477493 < baseStart_1477493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477536 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_1477536 : Nat := 118140960795 + 1477536 * 2 ^ 59
def prefixEnd_1477536 : Nat := 4983230072969 + 3 ^ 40 * 1477536 * 2
def baseEnd_1477536 : Nat := 505790768214424244869961

theorem tailTrace_1477536 : CollatzResearch.WordTrace tailWord_1477536 prefixEnd_1477536 505790768214424244869961 := by
  unfold tailWord_1477536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945082587573444951926231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35926776783431259935901641 26945082587573444951926231)
  ·
    refine ⟨40417623881360167427889347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26945082587573444951926231 40417623881360167427889347)
    ·
      refine ⟨60626435822040251141834021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40417623881360167427889347 60626435822040251141834021)
      ·
        refine ⟨11367456716632547089093879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60626435822040251141834021 11367456716632547089093879)
        ·
          refine ⟨17051185074948820633640819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367456716632547089093879 17051185074948820633640819)
          ·
            refine ⟨25576777612423230950461229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17051185074948820633640819 25576777612423230950461229)
            ·
              refine ⟨9591291604658711606422961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25576777612423230950461229 9591291604658711606422961)
              ·
                refine ⟨7193468703494033704817221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9591291604658711606422961 7193468703494033704817221)
                ·
                  refine ⟨1348775381905131319653229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7193468703494033704817221 1348775381905131319653229)
                  ·
                    refine ⟨505790768214424244869961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348775381905131319653229 505790768214424244869961)
                    ·
                      rfl

theorem cell22_1477536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_1477536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477536 prefixEnd_1477536 := by exact prefixLift 1477536
  have htrace : WordTrace (prefixWord ++ tailWord_1477536) baseStart_1477536 baseEnd_1477536 := by
    simpa [prefixWord, tailWord_1477536, baseEnd_1477536] using wordTrace_append hprefix tailTrace_1477536
  have hstable : (prefixWord ++ tailWord_1477536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477536).length < 2 ^ (prefixWord ++ tailWord_1477536).sum := by decide
  have hdescent : baseEnd_1477536 < baseStart_1477536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477566 : List Nat := [4, 2, 1, 1, 1, 2, 4, 7]
def baseStart_1477566 : Nat := 118140960795 + 1477566 * 2 ^ 59
def prefixEnd_1477566 : Nat := 4983230072969 + 3 ^ 40 * 1477566 * 2
def baseEnd_1477566 : Nat := 56200115314168240735541

theorem tailTrace_1477566 : CollatzResearch.WordTrace tailWord_1477566 prefixEnd_1477566 56200115314168240735541 := by
  unfold tailWord_1477566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736407420629775628430569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35927506243358803351629701 6736407420629775628430569)
  ·
    refine ⟨5052305565472331721322927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6736407420629775628430569 5052305565472331721322927)
    ·
      refine ⟨7578458348208497581984391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052305565472331721322927 7578458348208497581984391)
      ·
        refine ⟨11367687522312746372976587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578458348208497581984391 11367687522312746372976587)
        ·
          refine ⟨17051531283469119559464881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367687522312746372976587 17051531283469119559464881)
          ·
            refine ⟨12788648462601839669598661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17051531283469119559464881 12788648462601839669598661)
            ·
              refine ⟨2397871586737844938049749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12788648462601839669598661 2397871586737844938049749)
              ·
                refine ⟨56200115314168240735541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2397871586737844938049749 56200115314168240735541)
                ·
                  rfl

theorem cell22_1477566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_1477566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477566 prefixEnd_1477566 := by exact prefixLift 1477566
  have htrace : WordTrace (prefixWord ++ tailWord_1477566) baseStart_1477566 baseEnd_1477566 := by
    simpa [prefixWord, tailWord_1477566, baseEnd_1477566] using wordTrace_append hprefix tailTrace_1477566
  have hstable : (prefixWord ++ tailWord_1477566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477566).length < 2 ^ (prefixWord ++ tailWord_1477566).sum := by decide
  have hdescent : baseEnd_1477566 < baseStart_1477566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477574 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1477574 : Nat := 118140960795 + 1477574 * 2 ^ 59
def prefixEnd_1477574 : Nat := 4983230072969 + 3 ^ 40 * 1477574 * 2
def baseEnd_1477574 : Nat := 505803776391004812419845

theorem tailTrace_1477574 : CollatzResearch.WordTrace tailWord_1477574 prefixEnd_1477574 505803776391004812419845 := by
  unfold tailWord_1477574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684110973406538199804243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35927700766006148262490517 1684110973406538199804243)
  ·
    refine ⟨2526166460109807299706365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684110973406538199804243 2526166460109807299706365)
    ·
      refine ⟨947312422541177737389887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2526166460109807299706365 947312422541177737389887)
      ·
        refine ⟨1420968633811766606084831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947312422541177737389887 1420968633811766606084831)
        ·
          refine ⟨2131452950717649909127247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420968633811766606084831 2131452950717649909127247)
          ·
            refine ⟨3197179426076474863690871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131452950717649909127247 3197179426076474863690871)
            ·
              refine ⟨4795769139114712295536307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197179426076474863690871 4795769139114712295536307)
              ·
                refine ⟨7193653708672068443304461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795769139114712295536307 7193653708672068443304461)
                ·
                  refine ⟨2697620140752025666239173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7193653708672068443304461 2697620140752025666239173)
                  ·
                    refine ⟨505803776391004812419845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697620140752025666239173 505803776391004812419845)
                    ·
                      rfl

theorem cell22_1477574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1477574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477574 prefixEnd_1477574 := by exact prefixLift 1477574
  have htrace : WordTrace (prefixWord ++ tailWord_1477574) baseStart_1477574 baseEnd_1477574 := by
    simpa [prefixWord, tailWord_1477574, baseEnd_1477574] using wordTrace_append hprefix tailTrace_1477574
  have hstable : (prefixWord ++ tailWord_1477574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477574).length < 2 ^ (prefixWord ++ tailWord_1477574).sum := by decide
  have hdescent : baseEnd_1477574 < baseStart_1477574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477609 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1477609 : Nat := 118140960795 + 1477609 * 2 ^ 59
def prefixEnd_1477609 : Nat := 4983230072969 + 3 ^ 40 * 1477609 * 2
def baseEnd_1477609 : Nat := 505815757606276387794737

theorem tailTrace_1477609 : CollatzResearch.WordTrace tailWord_1477609 prefixEnd_1477609 505815757606276387794737 := by
  unfold tailWord_1477609
  simp only [CollatzResearch.WordTrace]
  refine ⟨53892827703882423371259881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35928551802588282247506587 53892827703882423371259881)
  ·
    refine ⟨40419620777911817528444911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53892827703882423371259881 40419620777911817528444911)
    ·
      refine ⟨60629431166867726292667367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40419620777911817528444911 60629431166867726292667367)
      ·
        refine ⟨90944146750301589439001051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60629431166867726292667367 90944146750301589439001051)
        ·
          refine ⟨136416220125452384158501577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90944146750301589439001051 136416220125452384158501577)
          ·
            refine ⟨102312165094089288118876183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136416220125452384158501577 102312165094089288118876183)
            ·
              refine ⟨153468247641133932178314275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102312165094089288118876183 153468247641133932178314275)
              ·
                refine ⟨230202371461700898267471413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153468247641133932178314275 230202371461700898267471413)
                ·
                  refine ⟨21581472324534459212575445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230202371461700898267471413 21581472324534459212575445)
                  ·
                    refine ⟨505815757606276387794737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21581472324534459212575445 505815757606276387794737)
                    ·
                      rfl

theorem cell22_1477609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1477609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477609 prefixEnd_1477609 := by exact prefixLift 1477609
  have htrace : WordTrace (prefixWord ++ tailWord_1477609) baseStart_1477609 baseEnd_1477609 := by
    simpa [prefixWord, tailWord_1477609, baseEnd_1477609] using wordTrace_append hprefix tailTrace_1477609
  have hstable : (prefixWord ++ tailWord_1477609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477609).length < 2 ^ (prefixWord ++ tailWord_1477609).sum := by decide
  have hdescent : baseEnd_1477609 < baseStart_1477609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477615 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 1, 3]
def baseStart_1477615 : Nat := 118140960795 + 1477615 * 2 ^ 59
def prefixEnd_1477615 : Nat := 4983230072969 + 3 ^ 40 * 1477615 * 2
def baseEnd_1477615 : Nat := 505817811528894372144719

theorem tailTrace_1477615 : CollatzResearch.WordTrace tailWord_1477615 prefixEnd_1477615 505817811528894372144719 := by
  unfold tailWord_1477615
  simp only [CollatzResearch.WordTrace]
  refine ⟨53893046541860686395978299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35928697694573790930652199 53893046541860686395978299)
  ·
    refine ⟨80839569812791029593967449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53893046541860686395978299 80839569812791029593967449)
    ·
      refine ⟨60629677359593272195475587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80839569812791029593967449 60629677359593272195475587)
      ·
        refine ⟨90944516039389908293213381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60629677359593272195475587 90944516039389908293213381)
        ·
          refine ⟨17052096757385607804977509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90944516039389908293213381 17052096757385607804977509)
          ·
            refine ⟨3197268142009801463433283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17052096757385607804977509 3197268142009801463433283)
            ·
              refine ⟨4795902213014702195149925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197268142009801463433283 4795902213014702195149925)
              ·
                refine ⟨899231664940256661590611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4795902213014702195149925 899231664940256661590611)
                ·
                  refine ⟨1348847497410384992385917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899231664940256661590611 1348847497410384992385917)
                  ·
                    refine ⟨505817811528894372144719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348847497410384992385917 505817811528894372144719)
                    ·
                      rfl

theorem cell22_1477615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_1477615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477615 prefixEnd_1477615 := by exact prefixLift 1477615
  have htrace : WordTrace (prefixWord ++ tailWord_1477615) baseStart_1477615 baseEnd_1477615 := by
    simpa [prefixWord, tailWord_1477615, baseEnd_1477615] using wordTrace_append hprefix tailTrace_1477615
  have hstable : (prefixWord ++ tailWord_1477615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477615).length < 2 ^ (prefixWord ++ tailWord_1477615).sum := by decide
  have hdescent : baseEnd_1477615 < baseStart_1477615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477658 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_1477658 : Nat := 118140960795 + 1477658 * 2 ^ 59
def prefixEnd_1477658 : Nat := 4983230072969 + 3 ^ 40 * 1477658 * 2
def baseEnd_1477658 : Nat := 505832531307656593319587

theorem tailTrace_1477658 : CollatzResearch.WordTrace tailWord_1477658 prefixEnd_1477658 505832531307656593319587 := by
  unfold tailWord_1477658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473653720176226184948407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35929743253803269826529085 13473653720176226184948407)
  ·
    refine ⟨20210480580264339277422611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13473653720176226184948407 20210480580264339277422611)
    ·
      refine ⟨30315720870396508916133917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210480580264339277422611 30315720870396508916133917)
      ·
        refine ⟨11368395326398690843550219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30315720870396508916133917 11368395326398690843550219)
        ·
          refine ⟨17052592989598036265325329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368395326398690843550219 17052592989598036265325329)
          ·
            refine ⟨12789444742198527198993997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17052592989598036265325329 12789444742198527198993997)
            ·
              refine ⟨4796041778324447699622749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12789444742198527198993997 4796041778324447699622749)
              ·
                refine ⟨1798515666871667887358531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4796041778324447699622749 1798515666871667887358531)
                ·
                  refine ⟨2697773500307501831037797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798515666871667887358531 2697773500307501831037797)
                  ·
                    refine ⟨505832531307656593319587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2697773500307501831037797 505832531307656593319587)
                    ·
                      rfl

theorem cell22_1477658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_1477658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477658 prefixEnd_1477658 := by exact prefixLift 1477658
  have htrace : WordTrace (prefixWord ++ tailWord_1477658) baseStart_1477658 baseEnd_1477658 := by
    simpa [prefixWord, tailWord_1477658, baseEnd_1477658] using wordTrace_append hprefix tailTrace_1477658
  have hstable : (prefixWord ++ tailWord_1477658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477658).length < 2 ^ (prefixWord ++ tailWord_1477658).sum := by decide
  have hdescent : baseEnd_1477658 < baseStart_1477658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477688 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1477688 : Nat := 118140960795 + 1477688 * 2 ^ 59
def prefixEnd_1477688 : Nat := 4983230072969 + 3 ^ 40 * 1477688 * 2
def baseEnd_1477688 : Nat := 505842800920746515069495

theorem tailTrace_1477688 : CollatzResearch.WordTrace tailWord_1477688 prefixEnd_1477688 505842800920746515069495 := by
  unfold tailWord_1477688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26947854535298109931692859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35930472713730813242257145 26947854535298109931692859)
  ·
    refine ⟨40421781802947164897539289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26947854535298109931692859 40421781802947164897539289)
    ·
      refine ⟨30316336352210373673154467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40421781802947164897539289 30316336352210373673154467)
      ·
        refine ⟨45474504528315560509731701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30316336352210373673154467 45474504528315560509731701)
        ·
          refine ⟨4263234799529583797787347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45474504528315560509731701 4263234799529583797787347)
          ·
            refine ⟨6394852199294375696681021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263234799529583797787347 6394852199294375696681021)
            ·
              refine ⟨2398069574735390886255383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6394852199294375696681021 2398069574735390886255383)
              ·
                refine ⟨3597104362103086329383075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398069574735390886255383 3597104362103086329383075)
                ·
                  refine ⟨5395656543154629494074613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597104362103086329383075 5395656543154629494074613)
                  ·
                    refine ⟨505842800920746515069495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5395656543154629494074613 505842800920746515069495)
                    ·
                      rfl

theorem cell22_1477688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1477688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477688 prefixEnd_1477688 := by exact prefixLift 1477688
  have htrace : WordTrace (prefixWord ++ tailWord_1477688) baseStart_1477688 baseEnd_1477688 := by
    simpa [prefixWord, tailWord_1477688, baseEnd_1477688] using wordTrace_append hprefix tailTrace_1477688
  have hstable : (prefixWord ++ tailWord_1477688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477688).length < 2 ^ (prefixWord ++ tailWord_1477688).sum := by decide
  have hdescent : baseEnd_1477688 < baseStart_1477688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477731 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_1477731 : Nat := 118140960795 + 1477731 * 2 ^ 59
def prefixEnd_1477731 : Nat := 4983230072969 + 3 ^ 40 * 1477731 * 2
def baseEnd_1477731 : Nat := 505857520699508736244363

theorem tailTrace_1477731 : CollatzResearch.WordTrace tailWord_1477731 prefixEnd_1477731 505857520699508736244363 := by
  unfold tailWord_1477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨53897277409440438207201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35931518272960292138134031 53897277409440438207201047)
  ·
    refine ⟨80845916114160657310801571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53897277409440438207201047 80845916114160657310801571)
    ·
      refine ⟨121268874171240985966202357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80845916114160657310801571 121268874171240985966202357)
      ·
        refine ⟨11368956953553842434331471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121268874171240985966202357 11368956953553842434331471)
        ·
          refine ⟨17053435430330763651497207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368956953553842434331471 17053435430330763651497207)
          ·
            refine ⟨25580153145496145477245811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17053435430330763651497207 25580153145496145477245811)
            ·
              refine ⟨38370229718244218215868717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580153145496145477245811 38370229718244218215868717)
              ·
                refine ⟨14388836144341581830950769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38370229718244218215868717 14388836144341581830950769)
                ·
                  refine ⟨10791627108256186373213077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14388836144341581830950769 10791627108256186373213077)
                  ·
                    refine ⟨505857520699508736244363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10791627108256186373213077 505857520699508736244363)
                    ·
                      rfl

theorem cell22_1477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_1477731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477731 prefixEnd_1477731 := by exact prefixLift 1477731
  have htrace : WordTrace (prefixWord ++ tailWord_1477731) baseStart_1477731 baseEnd_1477731 := by
    simpa [prefixWord, tailWord_1477731, baseEnd_1477731] using wordTrace_append hprefix tailTrace_1477731
  have hstable : (prefixWord ++ tailWord_1477731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477731).length < 2 ^ (prefixWord ++ tailWord_1477731).sum := by decide
  have hdescent : baseEnd_1477731 < baseStart_1477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477750 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1477750 : Nat := 118140960795 + 1477750 * 2 ^ 59
def prefixEnd_1477750 : Nat := 4983230072969 + 3 ^ 40 * 1477750 * 2
def baseEnd_1477750 : Nat := 505864024787799020019305

theorem tailTrace_1477750 : CollatzResearch.WordTrace tailWord_1477750 prefixEnd_1477750 505864024787799020019305 := by
  unfold tailWord_1477750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368623149773225278258919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35931980264247736301428469 3368623149773225278258919)
  ·
    refine ⟨5052934724659837917388379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368623149773225278258919 5052934724659837917388379)
    ·
      refine ⟨7579402086989756876082569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052934724659837917388379 7579402086989756876082569)
      ·
        refine ⟨5684551565242317657061927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579402086989756876082569 5684551565242317657061927)
        ·
          refine ⟨8526827347863476485592891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684551565242317657061927 8526827347863476485592891)
          ·
            refine ⟨12790241021795214728389337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526827347863476485592891 12790241021795214728389337)
            ·
              refine ⟨9592680766346411046292003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12790241021795214728389337 9592680766346411046292003)
              ·
                refine ⟨14389021149519616569438005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9592680766346411046292003 14389021149519616569438005)
                ·
                  refine ⟨1348970732767464053384813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14389021149519616569438005 1348970732767464053384813)
                  ·
                    refine ⟨505864024787799020019305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348970732767464053384813 505864024787799020019305)
                    ·
                      rfl

theorem cell22_1477750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1477750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477750 prefixEnd_1477750 := by exact prefixLift 1477750
  have htrace : WordTrace (prefixWord ++ tailWord_1477750) baseStart_1477750 baseEnd_1477750 := by
    simpa [prefixWord, tailWord_1477750, baseEnd_1477750] using wordTrace_append hprefix tailTrace_1477750
  have hstable : (prefixWord ++ tailWord_1477750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477750).length < 2 ^ (prefixWord ++ tailWord_1477750).sum := by decide
  have hdescent : baseEnd_1477750 < baseStart_1477750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477784 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_1477784 : Nat := 118140960795 + 1477784 * 2 ^ 59
def prefixEnd_1477784 : Nat := 4983230072969 + 3 ^ 40 * 1477784 * 2
def baseEnd_1477784 : Nat := 505875663682634264669201

theorem tailTrace_1477784 : CollatzResearch.WordTrace tailWord_1477784 prefixEnd_1477784 505875663682634264669201 := by
  unfold tailWord_1477784
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949605239124214129440203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35932806985498952172586937 26949605239124214129440203)
  ·
    refine ⟨40424407858686321194160305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26949605239124214129440203 40424407858686321194160305)
    ·
      refine ⟨30318305894014740895620229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40424407858686321194160305 30318305894014740895620229)
      ·
        refine ⟨5684682355127763917928793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30318305894014740895620229 5684682355127763917928793)
        ·
          refine ⟨4263511766345822938446595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5684682355127763917928793 4263511766345822938446595)
          ·
            refine ⟨6395267649518734407669893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263511766345822938446595 6395267649518734407669893)
            ·
              refine ⟨1199112684284762701438105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6395267649518734407669893 1199112684284762701438105)
              ·
                refine ⟨899334513213572026078579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199112684284762701438105 899334513213572026078579)
                ·
                  refine ⟨1349001769820358039117869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899334513213572026078579 1349001769820358039117869)
                  ·
                    refine ⟨505875663682634264669201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349001769820358039117869 505875663682634264669201)
                    ·
                      rfl

theorem cell22_1477784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_1477784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477784 prefixEnd_1477784 := by exact prefixLift 1477784
  have htrace : WordTrace (prefixWord ++ tailWord_1477784) baseStart_1477784 baseEnd_1477784 := by
    simpa [prefixWord, tailWord_1477784, baseEnd_1477784] using wordTrace_append hprefix tailTrace_1477784
  have hstable : (prefixWord ++ tailWord_1477784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477784).length < 2 ^ (prefixWord ++ tailWord_1477784).sum := by decide
  have hdescent : baseEnd_1477784 < baseStart_1477784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477793 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1477793 : Nat := 118140960795 + 1477793 * 2 ^ 59
def prefixEnd_1477793 : Nat := 4983230072969 + 3 ^ 40 * 1477793 * 2
def baseEnd_1477793 : Nat := 505878744566561241194173

theorem tailTrace_1477793 : CollatzResearch.WordTrace tailWord_1477793 prefixEnd_1477793 505878744566561241194173 := by
  unfold tailWord_1477793
  simp only [CollatzResearch.WordTrace]
  refine ⟨53899538735215822795958033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933025823477215197305355 53899538735215822795958033)
  ·
    refine ⟨40424654051411867096968525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53899538735215822795958033 40424654051411867096968525)
    ·
      refine ⟨15159245269279450161363197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40424654051411867096968525 15159245269279450161363197)
      ·
        refine ⟨5684716975979793810511199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15159245269279450161363197 5684716975979793810511199)
        ·
          refine ⟨8527075463969690715766799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684716975979793810511199 8527075463969690715766799)
          ·
            refine ⟨12790613195954536073650199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527075463969690715766799 12790613195954536073650199)
            ·
              refine ⟨19185919793931804110475299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790613195954536073650199 19185919793931804110475299)
              ·
                refine ⟨28778879690897706165712949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19185919793931804110475299 28778879690897706165712949)
                ·
                  refine ⟨2698019971021659953035589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28778879690897706165712949 2698019971021659953035589)
                  ·
                    refine ⟨505878744566561241194173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698019971021659953035589 505878744566561241194173)
                    ·
                      rfl

theorem cell22_1477793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1477793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477793 prefixEnd_1477793 := by exact prefixLift 1477793
  have htrace : WordTrace (prefixWord ++ tailWord_1477793) baseStart_1477793 baseEnd_1477793 := by
    simpa [prefixWord, tailWord_1477793, baseEnd_1477793] using wordTrace_append hprefix tailTrace_1477793
  have hstable : (prefixWord ++ tailWord_1477793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477793).length < 2 ^ (prefixWord ++ tailWord_1477793).sum := by decide
  have hdescent : baseEnd_1477793 < baseStart_1477793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477823 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_1477823 : Nat := 118140960795 + 1477823 * 2 ^ 59
def prefixEnd_1477823 : Nat := 4983230072969 + 3 ^ 40 * 1477823 * 2
def baseEnd_1477823 : Nat := 505889014179651162944081

theorem tailTrace_1477823 : CollatzResearch.WordTrace tailWord_1477823 prefixEnd_1477823 505889014179651162944081 := by
  unfold tailWord_1477823
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900632925107137919550123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933755283404758613033415 53900632925107137919550123)
  ·
    refine ⟨80850949387660706879325185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53900632925107137919550123 80850949387660706879325185)
    ·
      refine ⟨60638212040745530159493889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80850949387660706879325185 60638212040745530159493889)
      ·
        refine ⟨45478659030559147619620417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60638212040745530159493889 45478659030559147619620417)
        ·
          refine ⟨34108994272919360714715313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45478659030559147619620417 34108994272919360714715313)
          ·
            refine ⟨25581745704689520536036485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34108994272919360714715313 25581745704689520536036485)
            ·
              refine ⟨4796577319629285100506841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25581745704689520536036485 4796577319629285100506841)
              ·
                refine ⟨3597432989721963825380131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796577319629285100506841 3597432989721963825380131)
                ·
                  refine ⟨5396149484582945738070197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597432989721963825380131 5396149484582945738070197)
                  ·
                    refine ⟨505889014179651162944081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5396149484582945738070197 505889014179651162944081)
                    ·
                      rfl

theorem cell22_1477823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_1477823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477823 prefixEnd_1477823 := by exact prefixLift 1477823
  have htrace : WordTrace (prefixWord ++ tailWord_1477823) baseStart_1477823 baseEnd_1477823 := by
    simpa [prefixWord, tailWord_1477823, baseEnd_1477823] using wordTrace_append hprefix tailTrace_1477823
  have hstable : (prefixWord ++ tailWord_1477823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477823).length < 2 ^ (prefixWord ++ tailWord_1477823).sum := by decide
  have hdescent : baseEnd_1477823 < baseStart_1477823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477870 : List Nat := [4, 1, 2, 1, 1, 1, 6, 6]
def baseStart_1477870 : Nat := 118140960795 + 1477870 * 2 ^ 59
def prefixEnd_1477870 : Nat := 4983230072969 + 3 ^ 40 * 1477870 * 2
def baseEnd_1477870 : Nat := 56211678137795411890993

theorem tailTrace_1477870 : CollatzResearch.WordTrace tailWord_1477870 prefixEnd_1477870 56211678137795411890993 := by
  unfold tailWord_1477870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737793394492108118313883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35934898103957909964340709 6737793394492108118313883)
  ·
    refine ⟨10106690091738162177470825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6737793394492108118313883 10106690091738162177470825)
    ·
      refine ⟨7580017568803621633103119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10106690091738162177470825 7580017568803621633103119)
      ·
        refine ⟨11370026353205432449654679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580017568803621633103119 11370026353205432449654679)
        ·
          refine ⟨17055039529808148674482019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370026353205432449654679 17055039529808148674482019)
          ·
            refine ⟨25582559294712223011723029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17055039529808148674482019 25582559294712223011723029)
            ·
              refine ⟨1199182466939635453674517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25582559294712223011723029 1199182466939635453674517)
              ·
                refine ⟨56211678137795411890993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1199182466939635453674517 56211678137795411890993)
                ·
                  rfl

theorem cell22_1477870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_1477870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477870 prefixEnd_1477870 := by exact prefixLift 1477870
  have htrace : WordTrace (prefixWord ++ tailWord_1477870) baseStart_1477870 baseEnd_1477870 := by
    simpa [prefixWord, tailWord_1477870, baseEnd_1477870] using wordTrace_append hprefix tailTrace_1477870
  have hstable : (prefixWord ++ tailWord_1477870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477870).length < 2 ^ (prefixWord ++ tailWord_1477870).sum := by decide
  have hdescent : baseEnd_1477870 < baseStart_1477870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477902 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1477902 : Nat := 118140960795 + 1477902 * 2 ^ 59
def prefixEnd_1477902 : Nat := 4983230072969 + 3 ^ 40 * 1477902 * 2
def baseEnd_1477902 : Nat := 505916057494121290218839

theorem tailTrace_1477902 : CollatzResearch.WordTrace tailWord_1477902 prefixEnd_1477902 505916057494121290218839 := by
  unfold tailWord_1477902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737939286477616801459495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35935676194547289607783973 6737939286477616801459495)
  ·
    refine ⟨10106908929716425202189243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6737939286477616801459495 10106908929716425202189243)
    ·
      refine ⟨15160363394574637803283865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106908929716425202189243 15160363394574637803283865)
      ·
        refine ⟨11370272545930978352462899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15160363394574637803283865 11370272545930978352462899)
        ·
          refine ⟨17055408818896467528694349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370272545930978352462899 17055408818896467528694349)
          ·
            refine ⟨6395778307086175323260381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17055408818896467528694349 6395778307086175323260381)
            ·
              refine ⟨2398416865157315746222643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6395778307086175323260381 2398416865157315746222643)
              ·
                refine ⟨3597625297735973619333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398416865157315746222643 3597625297735973619333965)
                ·
                  refine ⟨1349109486650990107250237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3597625297735973619333965 1349109486650990107250237)
                  ·
                    refine ⟨505916057494121290218839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349109486650990107250237 505916057494121290218839)
                    ·
                      rfl

theorem cell22_1477902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1477902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477902 prefixEnd_1477902 := by exact prefixLift 1477902
  have htrace : WordTrace (prefixWord ++ tailWord_1477902) baseStart_1477902 baseEnd_1477902 := by
    simpa [prefixWord, tailWord_1477902, baseEnd_1477902] using wordTrace_append hprefix tailTrace_1477902
  have hstable : (prefixWord ++ tailWord_1477902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477902).length < 2 ^ (prefixWord ++ tailWord_1477902).sum := by decide
  have hdescent : baseEnd_1477902 < baseStart_1477902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477949 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 5]
def baseStart_1477949 : Nat := 118140960795 + 1477949 * 2 ^ 59
def prefixEnd_1477949 : Nat := 4983230072969 + 3 ^ 40 * 1477949 * 2
def baseEnd_1477949 : Nat := 168644048851542944764565

theorem tailTrace_1477949 : CollatzResearch.WordTrace tailWord_1477949 prefixEnd_1477949 168644048851542944764565 := by
  unfold tailWord_1477949
  simp only [CollatzResearch.WordTrace]
  refine ⟨53905228522650661438636901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35936819015100440959091267 53905228522650661438636901)
  ·
    refine ⟨10107230347996999019744419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53905228522650661438636901 10107230347996999019744419)
    ·
      refine ⟨15160845521995498529616629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107230347996999019744419 15160845521995498529616629)
      ·
        refine ⟨1421329267687077987151559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15160845521995498529616629 1421329267687077987151559)
        ·
          refine ⟨2131993901530616980727339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421329267687077987151559 2131993901530616980727339)
          ·
            refine ⟨3197990852295925471091009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131993901530616980727339 3197990852295925471091009)
            ·
              refine ⟨2398493139221944103318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197990852295925471091009 2398493139221944103318257)
              ·
                refine ⟨1798869854416458077488693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398493139221944103318257 1798869854416458077488693)
                ·
                  refine ⟨168644048851542944764565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1798869854416458077488693 168644048851542944764565)
                  ·
                    rfl

theorem cell22_1477949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_1477949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477949 prefixEnd_1477949 := by exact prefixLift 1477949
  have htrace : WordTrace (prefixWord ++ tailWord_1477949) baseStart_1477949 baseEnd_1477949 := by
    simpa [prefixWord, tailWord_1477949, baseEnd_1477949] using wordTrace_append hprefix tailTrace_1477949
  have hstable : (prefixWord ++ tailWord_1477949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477949).length < 2 ^ (prefixWord ++ tailWord_1477949).sum := by decide
  have hdescent : baseEnd_1477949 < baseStart_1477949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477953 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1477953 : Nat := 118140960795 + 1477953 * 2 ^ 59
def prefixEnd_1477953 : Nat := 4983230072969 + 3 ^ 40 * 1477953 * 2
def baseEnd_1477953 : Nat := 505933515836374157193683

theorem tailTrace_1477953 : CollatzResearch.WordTrace tailWord_1477953 prefixEnd_1477953 505933515836374157193683 := by
  unfold tailWord_1477953
  simp only [CollatzResearch.WordTrace]
  refine ⟨53905374414636170121782513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35936916276424113414521675 53905374414636170121782513)
  ·
    refine ⟨40429030810977127591336885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53905374414636170121782513 40429030810977127591336885)
    ·
      refine ⟨3790221638529105711687833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40429030810977127591336885 3790221638529105711687833)
      ·
        refine ⟨2842666228896829283765875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790221638529105711687833 2842666228896829283765875)
        ·
          refine ⟨4263999343345243925648813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842666228896829283765875 4263999343345243925648813)
          ·
            refine ⟨1598999753754466472118305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4263999343345243925648813 1598999753754466472118305)
            ·
              refine ⟨1199249815315849854088729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598999753754466472118305 1199249815315849854088729)
              ·
                refine ⟨899437361486887390566547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199249815315849854088729 899437361486887390566547)
                ·
                  refine ⟨1349156042230331085849821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899437361486887390566547 1349156042230331085849821)
                  ·
                    refine ⟨505933515836374157193683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349156042230331085849821 505933515836374157193683)
                    ·
                      rfl

theorem cell22_1477953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1477953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477953 prefixEnd_1477953 := by exact prefixLift 1477953
  have htrace : WordTrace (prefixWord ++ tailWord_1477953) baseStart_1477953 baseEnd_1477953 := by
    simpa [prefixWord, tailWord_1477953, baseEnd_1477953] using wordTrace_append hprefix tailTrace_1477953
  have hstable : (prefixWord ++ tailWord_1477953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477953).length < 2 ^ (prefixWord ++ tailWord_1477953).sum := by decide
  have hdescent : baseEnd_1477953 < baseStart_1477953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477975 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1477975 : Nat := 118140960795 + 1477975 * 2 ^ 59
def prefixEnd_1477975 : Nat := 4983230072969 + 3 ^ 40 * 1477975 * 2
def baseEnd_1477975 : Nat := 505941046885973433143615

theorem tailTrace_1477975 : CollatzResearch.WordTrace tailWord_1477975 prefixEnd_1477975 505941046885973433143615 := by
  unfold tailWord_1477975
  simp only [CollatzResearch.WordTrace]
  refine ⟨53906176820556467879083379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35937451213704311919388919 53906176820556467879083379)
  ·
    refine ⟨80859265230834701818625069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53906176820556467879083379 80859265230834701818625069)
    ·
      refine ⟨30322224461563013181984401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80859265230834701818625069 30322224461563013181984401)
      ·
        refine ⟨22741668346172259886488301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30322224461563013181984401 22741668346172259886488301)
        ·
          refine ⟨8528125629814597457433113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22741668346172259886488301 8528125629814597457433113)
          ·
            refine ⟨6396094222360948093074835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528125629814597457433113 6396094222360948093074835)
            ·
              refine ⟨9594141333541422139612253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396094222360948093074835 9594141333541422139612253)
              ·
                refine ⟨3597803000078033302354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9594141333541422139612253 3597803000078033302354595)
                ·
                  refine ⟨5396704500117049953531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597803000078033302354595 5396704500117049953531893)
                  ·
                    refine ⟨505941046885973433143615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5396704500117049953531893 505941046885973433143615)
                    ·
                      rfl

theorem cell22_1477975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1477975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1477975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1477975 prefixEnd_1477975 := by exact prefixLift 1477975
  have htrace : WordTrace (prefixWord ++ tailWord_1477975) baseStart_1477975 baseEnd_1477975 := by
    simpa [prefixWord, tailWord_1477975, baseEnd_1477975] using wordTrace_append hprefix tailTrace_1477975
  have hstable : (prefixWord ++ tailWord_1477975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477975).length < 2 ^ (prefixWord ++ tailWord_1477975).sum := by decide
  have hdescent : baseEnd_1477975 < baseStart_1477975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478037 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_1478037 : Nat := 118140960795 + 1478037 * 2 ^ 59
def prefixEnd_1478037 : Nat := 4983230072969 + 3 ^ 40 * 1478037 * 2
def baseEnd_1478037 : Nat := 505962270753025938093425

theorem tailTrace_1478037 : CollatzResearch.WordTrace tailWord_1478037 prefixEnd_1478037 505962270753025938093425 := by
  unfold tailWord_1478037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53908438146331852467840365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35938958764221234978560243 53908438146331852467840365)
  ·
    refine ⟨20215664304874444675440137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53908438146331852467840365 20215664304874444675440137)
    ·
      refine ⟨15161748228655833506580103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215664304874444675440137 15161748228655833506580103)
      ·
        refine ⟨22742622342983750259870155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161748228655833506580103 22742622342983750259870155)
        ·
          refine ⟨34113933514475625389805233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22742622342983750259870155 34113933514475625389805233)
          ·
            refine ⟨25585450135856719042353925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34113933514475625389805233 25585450135856719042353925)
            ·
              refine ⟨4797271900473134820441361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25585450135856719042353925 4797271900473134820441361)
              ·
                refine ⟨3597953925354851115331021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797271900473134820441361 3597953925354851115331021)
                ·
                  refine ⟨1349232722008069168249133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3597953925354851115331021 1349232722008069168249133)
                  ·
                    refine ⟨505962270753025938093425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349232722008069168249133 505962270753025938093425)
                    ·
                      rfl

theorem cell22_1478037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_1478037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478037 prefixEnd_1478037 := by exact prefixLift 1478037
  have htrace : WordTrace (prefixWord ++ tailWord_1478037) baseStart_1478037 baseEnd_1478037 := by
    simpa [prefixWord, tailWord_1478037, baseEnd_1478037] using wordTrace_append hprefix tailTrace_1478037
  have hstable : (prefixWord ++ tailWord_1478037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478037).length < 2 ^ (prefixWord ++ tailWord_1478037).sum := by decide
  have hdescent : baseEnd_1478037 < baseStart_1478037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478071 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 1, 3]
def baseStart_1478071 : Nat := 118140960795 + 1478071 * 2 ^ 59
def prefixEnd_1478071 : Nat := 4983230072969 + 3 ^ 40 * 1478071 * 2
def baseEnd_1478071 : Nat := 505973909647861182743321

theorem tailTrace_1478071 : CollatzResearch.WordTrace tailWord_1478071 prefixEnd_1478071 505973909647861182743321 := by
  unfold tailWord_1478071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53909678228208676274578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35939785485472450849718711 53909678228208676274578067)
  ·
    refine ⟨80864517342313014411867101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53909678228208676274578067 80864517342313014411867101)
    ·
      refine ⟨30324194003367380404450163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80864517342313014411867101 30324194003367380404450163)
      ·
        refine ⟨45486291005051070606675245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30324194003367380404450163 45486291005051070606675245)
        ·
          refine ⟨17057359126894151477503217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45486291005051070606675245 17057359126894151477503217)
          ·
            refine ⟨12793019345170613608127413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17057359126894151477503217 12793019345170613608127413)
            ·
              refine ⟨1199345563609745025761945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12793019345170613608127413 1199345563609745025761945)
              ·
                refine ⟨899509172707308769321459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199345563609745025761945 899509172707308769321459)
                ·
                  refine ⟨1349263759060963153982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899509172707308769321459 1349263759060963153982189)
                  ·
                    refine ⟨505973909647861182743321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349263759060963153982189 505973909647861182743321)
                    ·
                      rfl

theorem cell22_1478071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_1478071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478071 prefixEnd_1478071 := by exact prefixLift 1478071
  have htrace : WordTrace (prefixWord ++ tailWord_1478071) baseStart_1478071 baseEnd_1478071 := by
    simpa [prefixWord, tailWord_1478071, baseEnd_1478071] using wordTrace_append hprefix tailTrace_1478071
  have hstable : (prefixWord ++ tailWord_1478071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478071).length < 2 ^ (prefixWord ++ tailWord_1478071).sum := by decide
  have hdescent : baseEnd_1478071 < baseStart_1478071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478084 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1478084 : Nat := 118140960795 + 1478084 * 2 ^ 59
def prefixEnd_1478084 : Nat := 4983230072969 + 3 ^ 40 * 1478084 * 2
def baseEnd_1478084 : Nat := 168659453271177827389427

theorem tailTrace_1478084 : CollatzResearch.WordTrace tailWord_1478084 prefixEnd_1478084 168659453271177827389427 := by
  unfold tailWord_1478084
  simp only [CollatzResearch.WordTrace]
  refine ⟨26955076188580789747400653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35940101584774386329867537 26955076188580789747400653)
  ·
    refine ⟨10108153570717796155275245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26955076188580789747400653 10108153570717796155275245)
    ·
      refine ⟨3790557589019173558228217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10108153570717796155275245 3790557589019173558228217)
      ·
        refine ⟨2842918191764380168671163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790557589019173558228217 2842918191764380168671163)
        ·
          refine ⟨4264377287646570253006745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842918191764380168671163 4264377287646570253006745)
          ·
            refine ⟨3198282965734927689755059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4264377287646570253006745 3198282965734927689755059)
            ·
              refine ⟨4797424448602391534632589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198282965734927689755059 4797424448602391534632589)
              ·
                refine ⟨1799034168225896825487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4797424448602391534632589 1799034168225896825487221)
                ·
                  refine ⟨168659453271177827389427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799034168225896825487221 168659453271177827389427)
                  ·
                    rfl

theorem cell22_1478084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1478084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478084 prefixEnd_1478084 := by exact prefixLift 1478084
  have htrace : WordTrace (prefixWord ++ tailWord_1478084) baseStart_1478084 baseEnd_1478084 := by
    simpa [prefixWord, tailWord_1478084, baseEnd_1478084] using wordTrace_append hprefix tailTrace_1478084
  have hstable : (prefixWord ++ tailWord_1478084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478084).length < 2 ^ (prefixWord ++ tailWord_1478084).sum := by decide
  have hdescent : baseEnd_1478084 < baseStart_1478084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478095 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 6]
def baseStart_1478095 : Nat := 118140960795 + 1478095 * 2 ^ 59
def prefixEnd_1478095 : Nat := 4983230072969 + 3 ^ 40 * 1478095 * 2
def baseEnd_1478095 : Nat := 168660708446111040047749

theorem tailTrace_1478095 : CollatzResearch.WordTrace tailWord_1478095 prefixEnd_1478095 168660708446111040047749 := by
  unfold tailWord_1478095
  simp only [CollatzResearch.WordTrace]
  refine ⟨53910553580121728373451739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35940369053414485582301159 53910553580121728373451739)
  ·
    refine ⟨80865830370182592560177609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53910553580121728373451739 80865830370182592560177609)
    ·
      refine ⟨60649372777636944420133207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80865830370182592560177609 60649372777636944420133207)
      ·
        refine ⟨90974059166455416630199811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60649372777636944420133207 90974059166455416630199811)
        ·
          refine ⟨136461088749683124945299717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90974059166455416630199811 136461088749683124945299717)
          ·
            refine ⟨25586454140565585927243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136461088749683124945299717 25586454140565585927243697)
            ·
              refine ⟨19189840605424189445432773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25586454140565585927243697 19189840605424189445432773)
              ·
                refine ⟨3598095113517035521018645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19189840605424189445432773 3598095113517035521018645)
                ·
                  refine ⟨168660708446111040047749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3598095113517035521018645 168660708446111040047749)
                  ·
                    rfl

theorem cell22_1478095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_1478095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478095 prefixEnd_1478095 := by exact prefixLift 1478095
  have htrace : WordTrace (prefixWord ++ tailWord_1478095) baseStart_1478095 baseEnd_1478095 := by
    simpa [prefixWord, tailWord_1478095, baseEnd_1478095] using wordTrace_append hprefix tailTrace_1478095
  have hstable : (prefixWord ++ tailWord_1478095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478095).length < 2 ^ (prefixWord ++ tailWord_1478095).sum := by decide
  have hdescent : baseEnd_1478095 < baseStart_1478095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478127 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 4, 3]
def baseStart_1478127 : Nat := 118140960795 + 1478127 * 2 ^ 59
def prefixEnd_1478127 : Nat := 4983230072969 + 3 ^ 40 * 1478127 * 2
def baseEnd_1478127 : Nat := 505993079592295703343149

theorem tailTrace_1478127 : CollatzResearch.WordTrace tailWord_1478127 prefixEnd_1478127 505993079592295703343149 := by
  unfold tailWord_1478127
  simp only [CollatzResearch.WordTrace]
  refine ⟨53911720716005797838616635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35941147144003865225744423 53911720716005797838616635)
  ·
    refine ⟨80867581074008696757924953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53911720716005797838616635 80867581074008696757924953)
    ·
      refine ⟨60650685805506522568443715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80867581074008696757924953 60650685805506522568443715)
      ·
        refine ⟨90976028708259783852665573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60650685805506522568443715 90976028708259783852665573)
        ·
          refine ⟨17058005382798709472374795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90976028708259783852665573 17058005382798709472374795)
          ·
            refine ⟨25587008074198064208562193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17058005382798709472374795 25587008074198064208562193)
            ·
              refine ⟨19190256055648548156421645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25587008074198064208562193 19190256055648548156421645)
              ·
                refine ⟨7196346020868205558658117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19190256055648548156421645 7196346020868205558658117)
                ·
                  refine ⟨1349314878912788542248397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7196346020868205558658117 1349314878912788542248397)
                  ·
                    refine ⟨505993079592295703343149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349314878912788542248397 505993079592295703343149)
                    ·
                      rfl

theorem cell22_1478127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_1478127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478127 prefixEnd_1478127 := by exact prefixLift 1478127
  have htrace : WordTrace (prefixWord ++ tailWord_1478127) baseStart_1478127 baseEnd_1478127 := by
    simpa [prefixWord, tailWord_1478127, baseEnd_1478127] using wordTrace_append hprefix tailTrace_1478127
  have hstable : (prefixWord ++ tailWord_1478127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478127).length < 2 ^ (prefixWord ++ tailWord_1478127).sum := by decide
  have hdescent : baseEnd_1478127 < baseStart_1478127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478129 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 4]
def baseStart_1478129 : Nat := 118140960795 + 1478129 * 2 ^ 59
def prefixEnd_1478129 : Nat := 4983230072969 + 3 ^ 40 * 1478129 * 2
def baseEnd_1478129 : Nat := 168664588077722788264381

theorem tailTrace_1478129 : CollatzResearch.WordTrace tailWord_1478129 prefixEnd_1478129 168664588077722788264381 := by
  unfold tailWord_1478129
  simp only [CollatzResearch.WordTrace]
  refine ⟨53911793661998552180189441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35941195774665701453459627 53911793661998552180189441)
  ·
    refine ⟨40433845246498914135142081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53911793661998552180189441 40433845246498914135142081)
    ·
      refine ⟨30325383934874185601356561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40433845246498914135142081 30325383934874185601356561)
      ·
        refine ⟨22744037951155639201017421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30325383934874185601356561 22744037951155639201017421)
        ·
          refine ⟨8529014231683364700381533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22744037951155639201017421 8529014231683364700381533)
          ·
            refine ⟨3198380336881261762643075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8529014231683364700381533 3198380336881261762643075)
            ·
              refine ⟨4797570505321892643964613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198380336881261762643075 4797570505321892643964613)
              ·
                refine ⟨899544469747854870743365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4797570505321892643964613 899544469747854870743365)
                ·
                  refine ⟨168664588077722788264381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899544469747854870743365 168664588077722788264381)
                  ·
                    rfl

theorem cell22_1478129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_1478129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478129 prefixEnd_1478129 := by exact prefixLift 1478129
  have htrace : WordTrace (prefixWord ++ tailWord_1478129) baseStart_1478129 baseEnd_1478129 := by
    simpa [prefixWord, tailWord_1478129, baseEnd_1478129] using wordTrace_append hprefix tailTrace_1478129
  have hstable : (prefixWord ++ tailWord_1478129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478129).length < 2 ^ (prefixWord ++ tailWord_1478129).sum := by decide
  have hdescent : baseEnd_1478129 < baseStart_1478129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1478232 : Nat := 118140960795 + 1478232 * 2 ^ 59
def prefixEnd_1478232 : Nat := 4983230072969 + 3 ^ 40 * 1478232 * 2
def baseEnd_1478232 : Nat := 506029023238110429467827

theorem tailTrace_1478232 : CollatzResearch.WordTrace tailWord_1478232 prefixEnd_1478232 506029023238110429467827 := by
  unfold tailWord_1478232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957775190312700385594475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35943700253750267180792633 26957775190312700385594475)
  ·
    refine ⟨40436662785469050578391713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26957775190312700385594475 40436662785469050578391713)
    ·
      refine ⟨30327497089101787933793785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40436662785469050578391713 30327497089101787933793785)
      ·
        refine ⟨22745622816826340950345339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30327497089101787933793785 22745622816826340950345339)
        ·
          refine ⟨34118434225239511425518009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22745622816826340950345339 34118434225239511425518009)
          ·
            refine ⟨25588825668929633569138507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34118434225239511425518009 25588825668929633569138507)
            ·
              refine ⟨38383238503394450353707761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25588825668929633569138507 38383238503394450353707761)
              ·
                refine ⟨28787428877545837765280821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38383238503394450353707761 28787428877545837765280821)
                ·
                  refine ⟨2698821457269922290495077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28787428877545837765280821 2698821457269922290495077)
                  ·
                    refine ⟨506029023238110429467827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2698821457269922290495077 506029023238110429467827)
                    ·
                      rfl

theorem cell22_1478232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1478232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478232 prefixEnd_1478232 := by exact prefixLift 1478232
  have htrace : WordTrace (prefixWord ++ tailWord_1478232) baseStart_1478232 baseEnd_1478232 := by
    simpa [prefixWord, tailWord_1478232, baseEnd_1478232] using wordTrace_append hprefix tailTrace_1478232
  have hstable : (prefixWord ++ tailWord_1478232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478232).length < 2 ^ (prefixWord ++ tailWord_1478232).sum := by decide
  have hdescent : baseEnd_1478232 < baseStart_1478232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478253 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1478253 : Nat := 118140960795 + 1478253 * 2 ^ 59
def prefixEnd_1478253 : Nat := 4983230072969 + 3 ^ 40 * 1478253 * 2
def baseEnd_1478253 : Nat := 168678737322424458230921

theorem tailTrace_1478253 : CollatzResearch.WordTrace tailWord_1478253 prefixEnd_1478253 168678737322424458230921 := by
  unfold tailWord_1478253
  simp only [CollatzResearch.WordTrace]
  refine ⟨53916316313549321357703413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35944210875699547571802275 53916316313549321357703413)
  ·
    refine ⟨5054654654395248877284695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53916316313549321357703413 5054654654395248877284695)
    ·
      refine ⟨7581981981592873315927043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054654654395248877284695 7581981981592873315927043)
      ·
        refine ⟨11372972972389309973890565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581981981592873315927043 11372972972389309973890565)
        ·
          refine ⟨2132432432322995620104481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11372972972389309973890565 2132432432322995620104481)
          ·
            refine ⟨1599324324242246715078361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2132432432322995620104481 1599324324242246715078361)
            ·
              refine ⟨1199493243181685036308771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599324324242246715078361 1199493243181685036308771)
              ·
                refine ⟨1799239864772527554463157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199493243181685036308771 1799239864772527554463157)
                ·
                  refine ⟨168678737322424458230921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799239864772527554463157 168678737322424458230921)
                  ·
                    rfl

theorem cell22_1478253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1478253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478253 prefixEnd_1478253 := by exact prefixLift 1478253
  have htrace : WordTrace (prefixWord ++ tailWord_1478253) baseStart_1478253 baseEnd_1478253 := by
    simpa [prefixWord, tailWord_1478253, baseEnd_1478253] using wordTrace_append hprefix tailTrace_1478253
  have hstable : (prefixWord ++ tailWord_1478253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478253).length < 2 ^ (prefixWord ++ tailWord_1478253).sum := by decide
  have hdescent : baseEnd_1478253 < baseStart_1478253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478279 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1478279 : Nat := 118140960795 + 1478279 * 2 ^ 59
def prefixEnd_1478279 : Nat := 4983230072969 + 3 ^ 40 * 1478279 * 2
def baseEnd_1478279 : Nat := 506045112298617973542683

theorem tailTrace_1478279 : CollatzResearch.WordTrace tailWord_1478279 prefixEnd_1478279 506045112298617973542683 := by
  unfold tailWord_1478279
  simp only [CollatzResearch.WordTrace]
  refine ⟨53917264611455127798149891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35944843074303418532099927 53917264611455127798149891)
  ·
    refine ⟨80875896917182691697224837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53917264611455127798149891 80875896917182691697224837)
    ·
      refine ⟨15164230671971754693229657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80875896917182691697224837 15164230671971754693229657)
      ·
        refine ⟨11373173003978816019922243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15164230671971754693229657 11373173003978816019922243)
        ·
          refine ⟨17059759505968224029883365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11373173003978816019922243 17059759505968224029883365)
          ·
            refine ⟨3198704907369042005603131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17059759505968224029883365 3198704907369042005603131)
            ·
              refine ⟨4798057361053563008404697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198704907369042005603131 4798057361053563008404697)
              ·
                refine ⟨3598543020790172256303523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4798057361053563008404697 3598543020790172256303523)
                ·
                  refine ⟨5397814531185258384455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598543020790172256303523 5397814531185258384455285)
                  ·
                    refine ⟨506045112298617973542683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5397814531185258384455285 506045112298617973542683)
                    ·
                      rfl

theorem cell22_1478279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1478279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478279 prefixEnd_1478279 := by exact prefixLift 1478279
  have htrace : WordTrace (prefixWord ++ tailWord_1478279) baseStart_1478279 baseEnd_1478279 := by
    simpa [prefixWord, tailWord_1478279, baseEnd_1478279] using wordTrace_append hprefix tailTrace_1478279
  have hstable : (prefixWord ++ tailWord_1478279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478279).length < 2 ^ (prefixWord ++ tailWord_1478279).sum := by decide
  have hdescent : baseEnd_1478279 < baseStart_1478279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478296 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_1478296 : Nat := 118140960795 + 1478296 * 2 ^ 59
def prefixEnd_1478296 : Nat := 4983230072969 + 3 ^ 40 * 1478296 * 2
def baseEnd_1478296 : Nat := 506050931746035595867631

theorem tailTrace_1478296 : CollatzResearch.WordTrace tailWord_1478296 prefixEnd_1478296 506050931746035595867631 := by
  unfold tailWord_1478296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26958942326196769850759371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35945256434929026467679161 26958942326196769850759371)
  ·
    refine ⟨40438413489295154776139057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26958942326196769850759371 40438413489295154776139057)
    ·
      refine ⟨30328810116971366082104293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40438413489295154776139057 30328810116971366082104293)
      ·
        refine ⟨5686651896932131140394555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30328810116971366082104293 5686651896932131140394555)
        ·
          refine ⟨8529977845398196710591833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686651896932131140394555 8529977845398196710591833)
          ·
            refine ⟨6397483384048647532943875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8529977845398196710591833 6397483384048647532943875)
            ·
              refine ⟨9596225076072971299415813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397483384048647532943875 9596225076072971299415813)
              ·
                refine ⟨1799292201763682118640465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9596225076072971299415813 1799292201763682118640465)
                ·
                  refine ⟨1349469151322761588980349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799292201763682118640465 1349469151322761588980349)
                  ·
                    refine ⟨506050931746035595867631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349469151322761588980349 506050931746035595867631)
                    ·
                      rfl

theorem cell22_1478296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_1478296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478296 prefixEnd_1478296 := by exact prefixLift 1478296
  have htrace : WordTrace (prefixWord ++ tailWord_1478296) baseStart_1478296 baseEnd_1478296 := by
    simpa [prefixWord, tailWord_1478296, baseEnd_1478296] using wordTrace_append hprefix tailTrace_1478296
  have hstable : (prefixWord ++ tailWord_1478296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478296).length < 2 ^ (prefixWord ++ tailWord_1478296).sum := by decide
  have hdescent : baseEnd_1478296 < baseStart_1478296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478388 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1478388 : Nat := 118140960795 + 1478388 * 2 ^ 59
def prefixEnd_1478388 : Nat := 4983230072969 + 3 ^ 40 * 1478388 * 2
def baseEnd_1478388 : Nat := 168694141742059340855783

theorem tailTrace_1478388 : CollatzResearch.WordTrace tailWord_1478388 prefixEnd_1478388 168694141742059340855783 := by
  unfold tailWord_1478388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960620084030119706933909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35947493445373492942578545 26960620084030119706933909)
  ·
    refine ⟨1263779066438911861262527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26960620084030119706933909 1263779066438911861262527)
    ·
      refine ⟨1895668599658367791893791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263779066438911861262527 1895668599658367791893791)
      ·
        refine ⟨2843502899487551687840687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895668599658367791893791 2843502899487551687840687)
        ·
          refine ⟨4265254349231327531761031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843502899487551687840687 4265254349231327531761031)
          ·
            refine ⟨6397881523846991297641547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265254349231327531761031 6397881523846991297641547)
            ·
              refine ⟨9596822285770486946462321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397881523846991297641547 9596822285770486946462321)
              ·
                refine ⟨7197616714327865209846741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9596822285770486946462321 7197616714327865209846741)
                ·
                  refine ⟨168694141742059340855783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7197616714327865209846741 168694141742059340855783)
                  ·
                    rfl

theorem cell22_1478388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1478388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478388 prefixEnd_1478388 := by exact prefixLift 1478388
  have htrace : WordTrace (prefixWord ++ tailWord_1478388) baseStart_1478388 baseEnd_1478388 := by
    simpa [prefixWord, tailWord_1478388, baseEnd_1478388] using wordTrace_append hprefix tailTrace_1478388
  have hstable : (prefixWord ++ tailWord_1478388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478388).length < 2 ^ (prefixWord ++ tailWord_1478388).sum := by decide
  have hdescent : baseEnd_1478388 < baseStart_1478388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478401 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1478401 : Nat := 118140960795 + 1478401 * 2 ^ 59
def prefixEnd_1478401 : Nat := 4983230072969 + 3 ^ 40 * 1478401 * 2
def baseEnd_1478401 : Nat := 506086875391850321992309

theorem tailTrace_1478401 : CollatzResearch.WordTrace tailWord_1478401 prefixEnd_1478401 506086875391850321992309 := by
  unfold tailWord_1478401
  simp only [CollatzResearch.WordTrace]
  refine ⟨53921714317013142634091057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35947809544675428422727371 53921714317013142634091057)
  ·
    refine ⟨40441285737759856975568293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53921714317013142634091057 40441285737759856975568293)
    ·
      refine ⟨7582741075829973182919055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40441285737759856975568293 7582741075829973182919055)
      ·
        refine ⟨11374111613744959774378583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582741075829973182919055 11374111613744959774378583)
        ·
          refine ⟨17061167420617439661567875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11374111613744959774378583 17061167420617439661567875)
          ·
            refine ⟨25591751130926159492351813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17061167420617439661567875 25591751130926159492351813)
            ·
              refine ⟨4798453337048654904815965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25591751130926159492351813 4798453337048654904815965)
              ·
                refine ⟨1799420001393245589305987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798453337048654904815965 1799420001393245589305987)
                ·
                  refine ⟨2699130002089868383958981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799420001393245589305987 2699130002089868383958981)
                  ·
                    refine ⟨506086875391850321992309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2699130002089868383958981 506086875391850321992309)
                    ·
                      rfl

theorem cell22_1478401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1478401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478401 prefixEnd_1478401 := by exact prefixLift 1478401
  have htrace : WordTrace (prefixWord ++ tailWord_1478401) baseStart_1478401 baseEnd_1478401 := by
    simpa [prefixWord, tailWord_1478401, baseEnd_1478401] using wordTrace_append hprefix tailTrace_1478401
  have hstable : (prefixWord ++ tailWord_1478401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478401).length < 2 ^ (prefixWord ++ tailWord_1478401).sum := by decide
  have hdescent : baseEnd_1478401 < baseStart_1478401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478444 : List Nat := [2, 2, 1, 1, 1, 5, 2, 8]
def baseStart_1478444 : Nat := 118140960795 + 1478444 * 2 ^ 59
def prefixEnd_1478444 : Nat := 4983230072969 + 3 ^ 40 * 1478444 * 2
def baseEnd_1478444 : Nat := 56233510574512504796353

theorem tailTrace_1478444 : CollatzResearch.WordTrace tailWord_1478444 prefixEnd_1478444 56233510574512504796353 := by
  unfold tailWord_1478444
  simp only [CollatzResearch.WordTrace]
  refine ⟨26961641327928680488953193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35948855103904907318604257 26961641327928680488953193)
  ·
    refine ⟨20221230995946510366714895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26961641327928680488953193 20221230995946510366714895)
    ·
      refine ⟨30331846493919765550072343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20221230995946510366714895 30331846493919765550072343)
      ·
        refine ⟨45497769740879648325108515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30331846493919765550072343 45497769740879648325108515)
        ·
          refine ⟨68246654611319472487662773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45497769740879648325108515 68246654611319472487662773)
          ·
            refine ⟨6398123869811200545718385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68246654611319472487662773 6398123869811200545718385)
            ·
              refine ⟨4798592902358400409288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398123869811200545718385 4798592902358400409288789)
              ·
                refine ⟨56233510574512504796353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4798592902358400409288789 56233510574512504796353)
                ·
                  rfl

theorem cell22_1478444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_1478444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478444 prefixEnd_1478444 := by exact prefixLift 1478444
  have htrace : WordTrace (prefixWord ++ tailWord_1478444) baseStart_1478444 baseEnd_1478444 := by
    simpa [prefixWord, tailWord_1478444, baseEnd_1478444] using wordTrace_append hprefix tailTrace_1478444
  have hstable : (prefixWord ++ tailWord_1478444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478444).length < 2 ^ (prefixWord ++ tailWord_1478444).sum := by decide
  have hdescent : baseEnd_1478444 < baseStart_1478444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478474 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1478474 : Nat := 118140960795 + 1478474 * 2 ^ 59
def prefixEnd_1478474 : Nat := 4983230072969 + 3 ^ 40 * 1478474 * 2
def baseEnd_1478474 : Nat := 506111864783702464917085

theorem tailTrace_1478474 : CollatzResearch.WordTrace tailWord_1478474 prefixEnd_1478474 506111864783702464917085 := by
  unfold tailWord_1478474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481094211437169025374619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35949584563832450734332317 13481094211437169025374619)
  ·
    refine ⟨20221641317155753538061929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13481094211437169025374619 20221641317155753538061929)
    ·
      refine ⟨15166230987866815153546447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20221641317155753538061929 15166230987866815153546447)
      ·
        refine ⟨22749346481800222730319671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15166230987866815153546447 22749346481800222730319671)
        ·
          refine ⟨34124019722700334095479507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22749346481800222730319671 34124019722700334095479507)
          ·
            refine ⟨51186029584050501143219261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34124019722700334095479507 51186029584050501143219261)
            ·
              refine ⟨19194761094018937928707223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51186029584050501143219261 19194761094018937928707223)
              ·
                refine ⟨28792141641028406893060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19194761094018937928707223 28792141641028406893060835)
                ·
                  refine ⟨43188212461542610339591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28792141641028406893060835 43188212461542610339591253)
                  ·
                    refine ⟨506111864783702464917085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43188212461542610339591253 506111864783702464917085)
                    ·
                      rfl

theorem cell22_1478474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1478474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478474 prefixEnd_1478474 := by exact prefixLift 1478474
  have htrace : WordTrace (prefixWord ++ tailWord_1478474) baseStart_1478474 baseEnd_1478474 := by
    simpa [prefixWord, tailWord_1478474, baseEnd_1478474] using wordTrace_append hprefix tailTrace_1478474
  have hstable : (prefixWord ++ tailWord_1478474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478474).length < 2 ^ (prefixWord ++ tailWord_1478474).sum := by decide
  have hdescent : baseEnd_1478474 < baseStart_1478474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478551 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 6]
def baseStart_1478551 : Nat := 118140960795 + 1478551 * 2 ^ 59
def prefixEnd_1478551 : Nat := 4983230072969 + 3 ^ 40 * 1478551 * 2
def baseEnd_1478551 : Nat := 168712741152433310247283

theorem tailTrace_1478551 : CollatzResearch.WordTrace tailWord_1478551 prefixEnd_1478551 168712741152433310247283 := by
  unfold tailWord_1478551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53927185266469718252051507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35951456844313145501367671 53927185266469718252051507)
  ·
    refine ⟨80890777899704577378077261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53927185266469718252051507 80890777899704577378077261)
    ·
      refine ⟨30334041712389216516778973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80890777899704577378077261 30334041712389216516778973)
      ·
        refine ⟨11375265642145956193792115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30334041712389216516778973 11375265642145956193792115)
        ·
          refine ⟨17062898463218934290688173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375265642145956193792115 17062898463218934290688173)
          ·
            refine ⟨6398586923707100359008065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17062898463218934290688173 6398586923707100359008065)
            ·
              refine ⟨4798940192780325269256049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398586923707100359008065 4798940192780325269256049)
              ·
                refine ⟨3599205144585243951942037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4798940192780325269256049 3599205144585243951942037)
                ·
                  refine ⟨168712741152433310247283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3599205144585243951942037 168712741152433310247283)
                  ·
                    rfl

theorem cell22_1478551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_1478551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478551 prefixEnd_1478551 := by exact prefixLift 1478551
  have htrace : WordTrace (prefixWord ++ tailWord_1478551) baseStart_1478551 baseEnd_1478551 := by
    simpa [prefixWord, tailWord_1478551, baseEnd_1478551] using wordTrace_append hprefix tailTrace_1478551
  have hstable : (prefixWord ++ tailWord_1478551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478551).length < 2 ^ (prefixWord ++ tailWord_1478551).sum := by decide
  have hdescent : baseEnd_1478551 < baseStart_1478551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478583 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 2, 3]
def baseStart_1478583 : Nat := 118140960795 + 1478583 * 2 ^ 59
def prefixEnd_1478583 : Nat := 4983230072969 + 3 ^ 40 * 1478583 * 2
def baseEnd_1478583 : Nat := 506149177711262513941751

theorem tailTrace_1478583 : CollatzResearch.WordTrace tailWord_1478583 prefixEnd_1478583 506149177711262513941751 := by
  unfold tailWord_1478583
  simp only [CollatzResearch.WordTrace]
  refine ⟨53928352402353787717216403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35952234934902525144810935 53928352402353787717216403)
  ·
    refine ⟨80892528603530681575824605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53928352402353787717216403 80892528603530681575824605)
    ·
      refine ⟨30334698226324005590934227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80892528603530681575824605 30334698226324005590934227)
      ·
        refine ⟨45502047339486008386401341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30334698226324005590934227 45502047339486008386401341)
        ·
          refine ⟨17063267752307253144900503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45502047339486008386401341 17063267752307253144900503)
          ·
            refine ⟨25594901628460879717350755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17063267752307253144900503 25594901628460879717350755)
            ·
              refine ⟨38392352442691319576026133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25594901628460879717350755 38392352442691319576026133)
              ·
                refine ⟨1799641520751155605126225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38392352442691319576026133 1799641520751155605126225)
                ·
                  refine ⟨1349731140563366703844669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799641520751155605126225 1349731140563366703844669)
                  ·
                    refine ⟨506149177711262513941751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349731140563366703844669 506149177711262513941751)
                    ·
                      rfl

theorem cell22_1478583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_1478583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478583 prefixEnd_1478583 := by exact prefixLift 1478583
  have htrace : WordTrace (prefixWord ++ tailWord_1478583) baseStart_1478583 baseEnd_1478583 := by
    simpa [prefixWord, tailWord_1478583, baseEnd_1478583] using wordTrace_append hprefix tailTrace_1478583
  have hstable : (prefixWord ++ tailWord_1478583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478583).length < 2 ^ (prefixWord ++ tailWord_1478583).sum := by decide
  have hdescent : baseEnd_1478583 < baseStart_1478583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478585 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 4]
def baseStart_1478585 : Nat := 118140960795 + 1478585 * 2 ^ 59
def prefixEnd_1478585 : Nat := 4983230072969 + 3 ^ 40 * 1478585 * 2
def baseEnd_1478585 : Nat := 168716620784045058463915

theorem tailTrace_1478585 : CollatzResearch.WordTrace tailWord_1478585 prefixEnd_1478585 168716620784045058463915 := by
  unfold tailWord_1478585
  simp only [CollatzResearch.WordTrace]
  refine ⟨53928425348346542058789209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35952283565564361372526139 53928425348346542058789209)
  ·
    refine ⟨40446319011259906544091907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53928425348346542058789209 40446319011259906544091907)
    ·
      refine ⟨60669478516889859816137861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40446319011259906544091907 60669478516889859816137861)
      ·
        refine ⟨11375527221916848715525849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60669478516889859816137861 11375527221916848715525849)
        ·
          refine ⟨8531645416437636536644387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375527221916848715525849 8531645416437636536644387)
          ·
            refine ⟨12797468124656454804966581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8531645416437636536644387 12797468124656454804966581)
            ·
              refine ⟨1199762636686542637965617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12797468124656454804966581 1199762636686542637965617)
              ·
                refine ⟨899821977514906978474213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199762636686542637965617 899821977514906978474213)
                ·
                  refine ⟨168716620784045058463915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899821977514906978474213 168716620784045058463915)
                  ·
                    rfl

theorem cell22_1478585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_1478585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478585 prefixEnd_1478585 := by exact prefixLift 1478585
  have htrace : WordTrace (prefixWord ++ tailWord_1478585) baseStart_1478585 baseEnd_1478585 := by
    simpa [prefixWord, tailWord_1478585, baseEnd_1478585] using wordTrace_append hprefix tailTrace_1478585
  have hstable : (prefixWord ++ tailWord_1478585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478585).length < 2 ^ (prefixWord ++ tailWord_1478585).sum := by decide
  have hdescent : baseEnd_1478585 < baseStart_1478585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478600 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1478600 : Nat := 118140960795 + 1478600 * 2 ^ 59
def prefixEnd_1478600 : Nat := 4983230072969 + 3 ^ 40 * 1478600 * 2
def baseEnd_1478600 : Nat := 506154997158680136266699

theorem tailTrace_1478600 : CollatzResearch.WordTrace tailWord_1478600 prefixEnd_1478600 506154997158680136266699 := by
  unfold tailWord_1478600
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964486221646099810292627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35952648295528133080390169 26964486221646099810292627)
  ·
    refine ⟨40446729332469149715438941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26964486221646099810292627 40446729332469149715438941)
    ·
      refine ⟨15167523499675931143289603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40446729332469149715438941 15167523499675931143289603)
      ·
        refine ⟨22751285249513896714934405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15167523499675931143289603 22751285249513896714934405)
        ·
          refine ⟨4265865984283855634050201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22751285249513896714934405 4265865984283855634050201)
          ·
            refine ⟨3199399488212891725537651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4265865984283855634050201 3199399488212891725537651)
            ·
              refine ⟨4799099232319337588306477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199399488212891725537651 4799099232319337588306477)
              ·
                refine ⟨1799662212119751595614929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799099232319337588306477 1799662212119751595614929)
                ·
                  refine ⟨1349746659089813696711197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799662212119751595614929 1349746659089813696711197)
                  ·
                    refine ⟨506154997158680136266699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349746659089813696711197 506154997158680136266699)
                    ·
                      rfl

theorem cell22_1478600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1478600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478600 prefixEnd_1478600 := by exact prefixLift 1478600
  have htrace : WordTrace (prefixWord ++ tailWord_1478600) baseStart_1478600 baseEnd_1478600 := by
    simpa [prefixWord, tailWord_1478600, baseEnd_1478600] using wordTrace_append hprefix tailTrace_1478600
  have hstable : (prefixWord ++ tailWord_1478600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478600).length < 2 ^ (prefixWord ++ tailWord_1478600).sum := by decide
  have hdescent : baseEnd_1478600 < baseStart_1478600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478679 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 1, 3]
def baseStart_1478679 : Nat := 118140960795 + 1478679 * 2 ^ 59
def prefixEnd_1478679 : Nat := 4983230072969 + 3 ^ 40 * 1478679 * 2
def baseEnd_1478679 : Nat := 506182040473150263541457

theorem tailTrace_1478679 : CollatzResearch.WordTrace tailWord_1478679 prefixEnd_1478679 506182040473150263541457 := by
  unfold tailWord_1478679
  simp only [CollatzResearch.WordTrace]
  refine ⟨53931853810005996112711091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35954569206670664075140727 53931853810005996112711091)
  ·
    refine ⟨80897780715008994169066637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53931853810005996112711091 80897780715008994169066637)
    ·
      refine ⟨30336667768128372813399989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80897780715008994169066637 30336667768128372813399989)
      ·
        refine ⟨2844062603262034951256249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30336667768128372813399989 2844062603262034951256249)
        ·
          refine ⟨2133046952446526213442187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844062603262034951256249 2133046952446526213442187)
          ·
            refine ⟨3199570428669789320163281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133046952446526213442187 3199570428669789320163281)
            ·
              refine ⟨2399677821502341990122461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199570428669789320163281 2399677821502341990122461)
              ·
                refine ⟨899879183063378246295923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2399677821502341990122461 899879183063378246295923)
                ·
                  refine ⟨1349818774595067369443885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899879183063378246295923 1349818774595067369443885)
                  ·
                    refine ⟨506182040473150263541457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1349818774595067369443885 506182040473150263541457)
                    ·
                      rfl

theorem cell22_1478679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_1478679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478679 prefixEnd_1478679 := by exact prefixLift 1478679
  have htrace : WordTrace (prefixWord ++ tailWord_1478679) baseStart_1478679 baseEnd_1478679 := by
    simpa [prefixWord, tailWord_1478679, baseEnd_1478679] using wordTrace_append hprefix tailTrace_1478679
  have hstable : (prefixWord ++ tailWord_1478679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478679).length < 2 ^ (prefixWord ++ tailWord_1478679).sum := by decide
  have hdescent : baseEnd_1478679 < baseStart_1478679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478692 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1478692 : Nat := 118140960795 + 1478692 * 2 ^ 59
def prefixEnd_1478692 : Nat := 4983230072969 + 3 ^ 40 * 1478692 * 2
def baseEnd_1478692 : Nat := 168728830212940854322139

theorem tailTrace_1478692 : CollatzResearch.WordTrace tailWord_1478692 prefixEnd_1478692 168728830212940854322139 := by
  unfold tailWord_1478692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966163979479449666467165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35954885305972599555289553 26966163979479449666467165)
  ·
    refine ⟨10112311492304793624925187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26966163979479449666467165 10112311492304793624925187)
    ·
      refine ⟨15168467238457190437387781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112311492304793624925187 15168467238457190437387781)
      ·
        refine ⟨2844087607210723207010209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15168467238457190437387781 2844087607210723207010209)
        ·
          refine ⟨2133065705408042405257657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844087607210723207010209 2133065705408042405257657)
          ·
            refine ⟨1599799279056031803943243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133065705408042405257657 1599799279056031803943243)
            ·
              refine ⟨2399698918584047705914865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599799279056031803943243 2399698918584047705914865)
              ·
                refine ⟨1799774188938035779436149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399698918584047705914865 1799774188938035779436149)
                ·
                  refine ⟨168728830212940854322139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1799774188938035779436149 168728830212940854322139)
                  ·
                    rfl

theorem cell22_1478692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1478692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478692 prefixEnd_1478692 := by exact prefixLift 1478692
  have htrace : WordTrace (prefixWord ++ tailWord_1478692) baseStart_1478692 baseEnd_1478692 := by
    simpa [prefixWord, tailWord_1478692, baseEnd_1478692] using wordTrace_append hprefix tailTrace_1478692
  have hstable : (prefixWord ++ tailWord_1478692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478692).length < 2 ^ (prefixWord ++ tailWord_1478692).sum := by decide
  have hdescent : baseEnd_1478692 < baseStart_1478692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478731 : List Nat := [1, 1, 1, 1, 3, 1, 2, 12]
def baseStart_1478731 : Nat := 118140960795 + 1478731 * 2 ^ 59
def prefixEnd_1478731 : Nat := 4983230072969 + 3 ^ 40 * 1478731 * 2
def baseEnd_1478731 : Nat := 56244426792871051249033

theorem tailTrace_1478731 : CollatzResearch.WordTrace tailWord_1478731 prefixEnd_1478731 56244426792871051249033 := by
  unfold tailWord_1478731
  simp only [CollatzResearch.WordTrace]
  refine ⟨53933750405817608993604047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35955833603878405995736031 53933750405817608993604047)
  ·
    refine ⟨80900625608726413490406071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53933750405817608993604047 80900625608726413490406071)
    ·
      refine ⟨121350938413089620235609107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80900625608726413490406071 121350938413089620235609107)
      ·
        refine ⟨182026407619634430353413661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121350938413089620235609107 182026407619634430353413661)
        ·
          refine ⟨68259902857362911382530123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182026407619634430353413661 68259902857362911382530123)
          ·
            refine ⟨102389854286044367073795185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68259902857362911382530123 102389854286044367073795185)
            ·
              refine ⟨76792390714533275305346389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102389854286044367073795185 76792390714533275305346389)
              ·
                refine ⟨56244426792871051249033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 76792390714533275305346389 56244426792871051249033)
                ·
                  rfl

theorem cell22_1478731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_1478731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478731 prefixEnd_1478731 := by exact prefixLift 1478731
  have htrace : WordTrace (prefixWord ++ tailWord_1478731) baseStart_1478731 baseEnd_1478731 := by
    simpa [prefixWord, tailWord_1478731, baseEnd_1478731] using wordTrace_append hprefix tailTrace_1478731
  have hstable : (prefixWord ++ tailWord_1478731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478731).length < 2 ^ (prefixWord ++ tailWord_1478731).sum := by decide
  have hdescent : baseEnd_1478731 < baseStart_1478731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478748 : List Nat := [2, 2, 4, 1, 1, 2, 10]
def baseStart_1478748 : Nat := 118140960795 + 1478748 * 2 ^ 59
def prefixEnd_1478748 : Nat := 4983230072969 + 3 ^ 40 * 1478748 * 2
def baseEnd_1478748 : Nat := 18748357799379891983935

theorem tailTrace_1478748 : CollatzResearch.WordTrace tailWord_1478748 prefixEnd_1478748 18748357799379891983935 := by
  unfold tailWord_1478748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967185223378010448486449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35956246964504013931315265 26967185223378010448486449)
  ·
    refine ⟨20225388917533507836364837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26967185223378010448486449 20225388917533507836364837)
    ·
      refine ⟨3792260422037532719318407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20225388917533507836364837 3792260422037532719318407)
      ·
        refine ⟨5688390633056299078977611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792260422037532719318407 5688390633056299078977611)
        ·
          refine ⟨8532585949584448618466417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688390633056299078977611 8532585949584448618466417)
          ·
            refine ⟨6399439462188336463849813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8532585949584448618466417 6399439462188336463849813)
            ·
              refine ⟨18748357799379891983935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6399439462188336463849813 18748357799379891983935)
              ·
                rfl

theorem cell22_1478748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 10].length) (baseStart_1478748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478748 prefixEnd_1478748 := by exact prefixLift 1478748
  have htrace : WordTrace (prefixWord ++ tailWord_1478748) baseStart_1478748 baseEnd_1478748 := by
    simpa [prefixWord, tailWord_1478748, baseEnd_1478748] using wordTrace_append hprefix tailTrace_1478748
  have hstable : (prefixWord ++ tailWord_1478748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478748).length < 2 ^ (prefixWord ++ tailWord_1478748).sum := by decide
  have hdescent : baseEnd_1478748 < baseStart_1478748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478754 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1478754 : Nat := 118140960795 + 1478754 * 2 ^ 59
def prefixEnd_1478754 : Nat := 4983230072969 + 3 ^ 40 * 1478754 * 2
def baseEnd_1478754 : Nat := 168735904835291689305409

theorem tailTrace_1478754 : CollatzResearch.WordTrace tailWord_1478754 prefixEnd_1478754 168735904835291689305409 := by
  unfold tailWord_1478754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13483647321183570980422829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35956392856489522614460877 13483647321183570980422829)
  ·
    refine ⟨5056367745443839117658561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13483647321183570980422829 5056367745443839117658561)
    ·
      refine ⟨3792275809082879338243921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5056367745443839117658561 3792275809082879338243921)
      ·
        refine ⟨2844206856812159503682941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792275809082879338243921 2844206856812159503682941)
        ·
          refine ⟨1066577571304559813881103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2844206856812159503682941 1066577571304559813881103)
          ·
            refine ⟨1599866356956839720821655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066577571304559813881103 1599866356956839720821655)
            ·
              refine ⟨2399799535435259581232483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599866356956839720821655 2399799535435259581232483)
              ·
                refine ⟨3599699303152889371848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399799535435259581232483 3599699303152889371848725)
                ·
                  refine ⟨168735904835291689305409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3599699303152889371848725 168735904835291689305409)
                  ·
                    rfl

theorem cell22_1478754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1478754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478754 prefixEnd_1478754 := by exact prefixLift 1478754
  have htrace : WordTrace (prefixWord ++ tailWord_1478754) baseStart_1478754 baseEnd_1478754 := by
    simpa [prefixWord, tailWord_1478754, baseEnd_1478754] using wordTrace_append hprefix tailTrace_1478754
  have hstable : (prefixWord ++ tailWord_1478754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478754).length < 2 ^ (prefixWord ++ tailWord_1478754).sum := by decide
  have hdescent : baseEnd_1478754 < baseStart_1478754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478840 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1478840 : Nat := 118140960795 + 1478840 * 2 ^ 59
def prefixEnd_1478840 : Nat := 4983230072969 + 3 ^ 40 * 1478840 * 2
def baseEnd_1478840 : Nat := 506237154063399510265963

theorem tailTrace_1478840 : CollatzResearch.WordTrace tailWord_1478840 prefixEnd_1478840 506237154063399510265963 := by
  unfold tailWord_1478840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26968862981211360304660987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35958483974948480406214649 26968862981211360304660987)
  ·
    refine ⟨40453294471817040456991481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26968862981211360304660987 40453294471817040456991481)
    ·
      refine ⟨30339970853862780342743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40453294471817040456991481 30339970853862780342743611)
      ·
        refine ⟨45509956280794170514115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30339970853862780342743611 45509956280794170514115417)
        ·
          refine ⟨34132467210595627885586563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45509956280794170514115417 34132467210595627885586563)
          ·
            refine ⟨51198700815893441828379845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34132467210595627885586563 51198700815893441828379845)
            ·
              refine ⟨9599756402980020342821221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51198700815893441828379845 9599756402980020342821221)
              ·
                refine ⟨1799954325558753814278979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9599756402980020342821221 1799954325558753814278979)
                ·
                  refine ⟨2699931488338130721418469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799954325558753814278979 2699931488338130721418469)
                  ·
                    refine ⟨506237154063399510265963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2699931488338130721418469 506237154063399510265963)
                    ·
                      rfl

theorem cell22_1478840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1478840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478840 prefixEnd_1478840 := by exact prefixLift 1478840
  have htrace : WordTrace (prefixWord ++ tailWord_1478840) baseStart_1478840 baseEnd_1478840 := by
    simpa [prefixWord, tailWord_1478840, baseEnd_1478840] using wordTrace_append hprefix tailTrace_1478840
  have hstable : (prefixWord ++ tailWord_1478840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478840).length < 2 ^ (prefixWord ++ tailWord_1478840).sum := by decide
  have hdescent : baseEnd_1478840 < baseStart_1478840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478872 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_1478872 : Nat := 118140960795 + 1478872 * 2 ^ 59
def prefixEnd_1478872 : Nat := 4983230072969 + 3 ^ 40 * 1478872 * 2
def baseEnd_1478872 : Nat := 168749369439120697821955

theorem tailTrace_1478872 : CollatzResearch.WordTrace tailWord_1478872 prefixEnd_1478872 168749369439120697821955 := by
  unfold tailWord_1478872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26969446549153395037243435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35959262065537860049657913 26969446549153395037243435)
  ·
    refine ⟨40454169823730092555865153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26969446549153395037243435 40454169823730092555865153)
    ·
      refine ⟨30340627367797569416898865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40454169823730092555865153 30340627367797569416898865)
      ·
        refine ⟨22755470525848177062674149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30340627367797569416898865 22755470525848177062674149)
        ·
          refine ⟨4266650723596533199251403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22755470525848177062674149 4266650723596533199251403)
          ·
            refine ⟨6399976085394799798877105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266650723596533199251403 6399976085394799798877105)
            ·
              refine ⟨4799982064046099849157829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399976085394799798877105 4799982064046099849157829)
              ·
                refine ⟨899996637008643721717093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4799982064046099849157829 899996637008643721717093)
                ·
                  refine ⟨168749369439120697821955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899996637008643721717093 168749369439120697821955)
                  ·
                    rfl

theorem cell22_1478872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_1478872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478872 prefixEnd_1478872 := by exact prefixLift 1478872
  have htrace : WordTrace (prefixWord ++ tailWord_1478872) baseStart_1478872 baseEnd_1478872 := by
    simpa [prefixWord, tailWord_1478872, baseEnd_1478872] using wordTrace_append hprefix tailTrace_1478872
  have hstable : (prefixWord ++ tailWord_1478872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478872).length < 2 ^ (prefixWord ++ tailWord_1478872).sum := by decide
  have hdescent : baseEnd_1478872 < baseStart_1478872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478885 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1478885 : Nat := 118140960795 + 1478885 * 2 ^ 59
def prefixEnd_1478885 : Nat := 4983230072969 + 3 ^ 40 * 1478885 * 2
def baseEnd_1478885 : Nat := 506252558483034392890825

theorem tailTrace_1478885 : CollatzResearch.WordTrace tailWord_1478885 prefixEnd_1478885 506252558483034392890825 := by
  unfold tailWord_1478885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53939367247259693294710109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35959578164839795529806739 53939367247259693294710109)
  ·
    refine ⟨20227262717722384985516291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53939367247259693294710109 20227262717722384985516291)
    ·
      refine ⟨30340894076583577478274437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20227262717722384985516291 30340894076583577478274437)
      ·
        refine ⟨5688917639359420777176457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30340894076583577478274437 5688917639359420777176457)
        ·
          refine ⟨4266688229519565582882343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5688917639359420777176457 4266688229519565582882343)
          ·
            refine ⟨6400032344279348374323515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266688229519565582882343 6400032344279348374323515)
            ·
              refine ⟨9600048516419022561485273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400032344279348374323515 9600048516419022561485273)
              ·
                refine ⟨7200036387314266921113955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600048516419022561485273 7200036387314266921113955)
                ·
                  refine ⟨10800054580971400381670933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200036387314266921113955 10800054580971400381670933)
                  ·
                    refine ⟨506252558483034392890825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10800054580971400381670933 506252558483034392890825)
                    ·
                      rfl

theorem cell22_1478885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1478885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478885 prefixEnd_1478885 := by exact prefixLift 1478885
  have htrace : WordTrace (prefixWord ++ tailWord_1478885) baseStart_1478885 baseEnd_1478885 := by
    simpa [prefixWord, tailWord_1478885, baseEnd_1478885] using wordTrace_append hprefix tailTrace_1478885
  have hstable : (prefixWord ++ tailWord_1478885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478885).length < 2 ^ (prefixWord ++ tailWord_1478885).sum := by decide
  have hdescent : baseEnd_1478885 < baseStart_1478885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478887 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1478887 : Nat := 118140960795 + 1478887 * 2 ^ 59
def prefixEnd_1478887 : Nat := 4983230072969 + 3 ^ 40 * 1478887 * 2
def baseEnd_1478887 : Nat := 506253243123907054340819

theorem tailTrace_1478887 : CollatzResearch.WordTrace tailWord_1478887 prefixEnd_1478887 506253243123907054340819 := by
  unfold tailWord_1478887
  simp only [CollatzResearch.WordTrace]
  refine ⟨53939440193252447636282915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35959626795501631757521943 53939440193252447636282915)
  ·
    refine ⟨80909160289878671454424373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53939440193252447636282915 80909160289878671454424373)
    ·
      refine ⟨7585233777176125448852285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80909160289878671454424373 7585233777176125448852285)
      ·
        refine ⟨2844462666441047043319607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7585233777176125448852285 2844462666441047043319607)
        ·
          refine ⟨4266693999661570564979411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844462666441047043319607 4266693999661570564979411)
          ·
            refine ⟨6400040999492355847469117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266693999661570564979411 6400040999492355847469117)
            ·
              refine ⟨2400015374809633442800919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6400040999492355847469117 2400015374809633442800919)
              ·
                refine ⟨3600023062214450164201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400015374809633442800919 3600023062214450164201379)
                ·
                  refine ⟨5400034593321675246302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600023062214450164201379 5400034593321675246302069)
                  ·
                    refine ⟨506253243123907054340819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5400034593321675246302069 506253243123907054340819)
                    ·
                      rfl

theorem cell22_1478887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1478887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478887 prefixEnd_1478887 := by exact prefixLift 1478887
  have htrace : WordTrace (prefixWord ++ tailWord_1478887) baseStart_1478887 baseEnd_1478887 := by
    simpa [prefixWord, tailWord_1478887, baseEnd_1478887] using wordTrace_append hprefix tailTrace_1478887
  have hstable : (prefixWord ++ tailWord_1478887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478887).length < 2 ^ (prefixWord ++ tailWord_1478887).sum := by decide
  have hdescent : baseEnd_1478887 < baseStart_1478887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478919 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1478919 : Nat := 118140960795 + 1478919 * 2 ^ 59
def prefixEnd_1478919 : Nat := 4983230072969 + 3 ^ 40 * 1478919 * 2
def baseEnd_1478919 : Nat := 506264197377869637540721

theorem tailTrace_1478919 : CollatzResearch.WordTrace tailWord_1478919 prefixEnd_1478919 506264197377869637540721 := by
  unfold tailWord_1478919
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940607329136517101447811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35960404886091011400965207 53940607329136517101447811)
  ·
    refine ⟨80910910993704775652171717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53940607329136517101447811 80910910993704775652171717)
    ·
      refine ⟨15170795811319645434782197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80910910993704775652171717 15170795811319645434782197)
      ·
        refine ⟨1422262107311216759510831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15170795811319645434782197 1422262107311216759510831)
        ·
          refine ⟨2133393160966825139266247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422262107311216759510831 2133393160966825139266247)
          ·
            refine ⟨3200089741450237708899371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133393160966825139266247 3200089741450237708899371)
            ·
              refine ⟨4800134612175356563349057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200089741450237708899371 4800134612175356563349057)
              ·
                refine ⟨3600100959131517422511793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800134612175356563349057 3600100959131517422511793)
                ·
                  refine ⟨2700075719348638066883845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600100959131517422511793 2700075719348638066883845)
                  ·
                    refine ⟨506264197377869637540721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700075719348638066883845 506264197377869637540721)
                    ·
                      rfl

theorem cell22_1478919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1478919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478919 prefixEnd_1478919 := by exact prefixLift 1478919
  have htrace : WordTrace (prefixWord ++ tailWord_1478919) baseStart_1478919 baseEnd_1478919 := by
    simpa [prefixWord, tailWord_1478919, baseEnd_1478919] using wordTrace_append hprefix tailTrace_1478919
  have hstable : (prefixWord ++ tailWord_1478919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478919).length < 2 ^ (prefixWord ++ tailWord_1478919).sum := by decide
  have hdescent : baseEnd_1478919 < baseStart_1478919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478938 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_1478938 : Nat := 118140960795 + 1478938 * 2 ^ 59
def prefixEnd_1478938 : Nat := 4983230072969 + 3 ^ 40 * 1478938 * 2
def baseEnd_1478938 : Nat := 506270701466159921315663

theorem tailTrace_1478938 : CollatzResearch.WordTrace tailWord_1478938 prefixEnd_1478938 506270701466159921315663 := by
  unfold tailWord_1478938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485325079016920836597367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35960866877378455564259645 13485325079016920836597367)
  ·
    refine ⟨20227987618525381254896051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485325079016920836597367 20227987618525381254896051)
    ·
      refine ⟨30341981427788071882344077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20227987618525381254896051 30341981427788071882344077)
      ·
        refine ⟨11378243035420526955879029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30341981427788071882344077 11378243035420526955879029)
        ·
          refine ⟨1066710284570674402113659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11378243035420526955879029 1066710284570674402113659)
          ·
            refine ⟨1600065426856011603170489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066710284570674402113659 1600065426856011603170489)
            ·
              refine ⟨1200049070142008702377867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600065426856011603170489 1200049070142008702377867)
              ·
                refine ⟨1800073605213013053566801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200049070142008702377867 1800073605213013053566801)
                ·
                  refine ⟨1350055203909759790175101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800073605213013053566801 1350055203909759790175101)
                  ·
                    refine ⟨506270701466159921315663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350055203909759790175101 506270701466159921315663)
                    ·
                      rfl

theorem cell22_1478938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_1478938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1478938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1478938 prefixEnd_1478938 := by exact prefixLift 1478938
  have htrace : WordTrace (prefixWord ++ tailWord_1478938) baseStart_1478938 baseEnd_1478938 := by
    simpa [prefixWord, tailWord_1478938, baseEnd_1478938] using wordTrace_append hprefix tailTrace_1478938
  have hstable : (prefixWord ++ tailWord_1478938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478938).length < 2 ^ (prefixWord ++ tailWord_1478938).sum := by decide
  have hdescent : baseEnd_1478938 < baseStart_1478938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479024 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_1479024 : Nat := 118140960795 + 1479024 * 2 ^ 59
def prefixEnd_1479024 : Nat := 4983230072969 + 3 ^ 40 * 1479024 * 2
def baseEnd_1479024 : Nat := 168766713674561454555133

theorem tailTrace_1479024 : CollatzResearch.WordTrace tailWord_1479024 prefixEnd_1479024 168766713674561454555133 := by
  unfold tailWord_1479024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972218496878060017010063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35962957995837413356013417 26972218496878060017010063)
  ·
    refine ⟨40458327745317090025515095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26972218496878060017010063 40458327745317090025515095)
    ·
      refine ⟨60687491617975635038272643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40458327745317090025515095 60687491617975635038272643)
      ·
        refine ⟨91031237426963452557408965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60687491617975635038272643 91031237426963452557408965)
        ·
          refine ⟨17068357017555647354514181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91031237426963452557408965 17068357017555647354514181)
          ·
            refine ⟨3200316940791683878971409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17068357017555647354514181 3200316940791683878971409)
            ·
              refine ⟨2400237705593762909228557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200316940791683878971409 2400237705593762909228557)
              ·
                refine ⟨900089139597661090960709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400237705593762909228557 900089139597661090960709)
                ·
                  refine ⟨168766713674561454555133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900089139597661090960709 168766713674561454555133)
                  ·
                    rfl

theorem cell22_1479024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_1479024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479024 prefixEnd_1479024 := by exact prefixLift 1479024
  have htrace : WordTrace (prefixWord ++ tailWord_1479024) baseStart_1479024 baseEnd_1479024 := by
    simpa [prefixWord, tailWord_1479024, baseEnd_1479024] using wordTrace_append hprefix tailTrace_1479024
  have hstable : (prefixWord ++ tailWord_1479024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479024).length < 2 ^ (prefixWord ++ tailWord_1479024).sum := by decide
  have hdescent : baseEnd_1479024 < baseStart_1479024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479026 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1479026 : Nat := 118140960795 + 1479026 * 2 ^ 59
def prefixEnd_1479026 : Nat := 4983230072969 + 3 ^ 40 * 1479026 * 2
def baseEnd_1479026 : Nat := 506300825664557025115393

theorem tailTrace_1479026 : CollatzResearch.WordTrace tailWord_1479026 prefixEnd_1479026 506300825664557025115393 := by
  unfold tailWord_1479026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486127484937218593898233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35963006626499249583728621 13486127484937218593898233)
  ·
    refine ⟨10114595613702913945423675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13486127484937218593898233 10114595613702913945423675)
    ·
      refine ⟨15171893420554370918135513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114595613702913945423675 15171893420554370918135513)
      ·
        refine ⟨11378920065415778188601635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15171893420554370918135513 11378920065415778188601635)
        ·
          refine ⟨17068380098123667282902453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378920065415778188601635 17068380098123667282902453)
          ·
            refine ⟨1600160634199093807772105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17068380098123667282902453 1600160634199093807772105)
            ·
              refine ⟨1200120475649320355829079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600160634199093807772105 1200120475649320355829079)
              ·
                refine ⟨1800180713473980533743619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200120475649320355829079 1800180713473980533743619)
                ·
                  refine ⟨2700271070210970800615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800180713473980533743619 2700271070210970800615429)
                  ·
                    refine ⟨506300825664557025115393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700271070210970800615429 506300825664557025115393)
                    ·
                      rfl

theorem cell22_1479026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1479026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479026 prefixEnd_1479026 := by exact prefixLift 1479026
  have htrace : WordTrace (prefixWord ++ tailWord_1479026) baseStart_1479026 baseEnd_1479026 := by
    simpa [prefixWord, tailWord_1479026, baseEnd_1479026] using wordTrace_append hprefix tailTrace_1479026
  have hstable : (prefixWord ++ tailWord_1479026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479026).length < 2 ^ (prefixWord ++ tailWord_1479026).sum := by decide
  have hdescent : baseEnd_1479026 < baseStart_1479026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479035 : List Nat := [1, 1, 1, 1, 1, 8, 9]
def baseStart_1479035 : Nat := 118140960795 + 1479035 * 2 ^ 59
def prefixEnd_1479035 : Nat := 4983230072969 + 3 ^ 40 * 1479035 * 2
def baseEnd_1479035 : Nat := 18751996538832740801495

theorem tailTrace_1479035 : CollatzResearch.WordTrace tailWord_1479035 prefixEnd_1479035 18751996538832740801495 := by
  unfold tailWord_1479035
  simp only [CollatzResearch.WordTrace]
  refine ⟨53944838196716268912670559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35963225464477512608447039 53944838196716268912670559)
  ·
    refine ⟨80917257295074403369005839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53944838196716268912670559 80917257295074403369005839)
    ·
      refine ⟨121375885942611605053508759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80917257295074403369005839 121375885942611605053508759)
      ·
        refine ⟨182063828913917407580263139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121375885942611605053508759 182063828913917407580263139)
        ·
          refine ⟨273095743370876111370394709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182063828913917407580263139 273095743370876111370394709)
          ·
            refine ⟨3200340742627454430121813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 273095743370876111370394709 3200340742627454430121813)
            ·
              refine ⟨18751996538832740801495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3200340742627454430121813 18751996538832740801495)
              ·
                rfl

theorem cell22_1479035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 9].length) (baseStart_1479035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479035 prefixEnd_1479035 := by exact prefixLift 1479035
  have htrace : WordTrace (prefixWord ++ tailWord_1479035) baseStart_1479035 baseEnd_1479035 := by
    simpa [prefixWord, tailWord_1479035, baseEnd_1479035] using wordTrace_append hprefix tailTrace_1479035
  have hstable : (prefixWord ++ tailWord_1479035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479035).length < 2 ^ (prefixWord ++ tailWord_1479035).sum := by decide
  have hdescent : baseEnd_1479035 < baseStart_1479035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479097 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 7]
def baseStart_1479097 : Nat := 118140960795 + 1479097 * 2 ^ 59
def prefixEnd_1479097 : Nat := 4983230072969 + 3 ^ 40 * 1479097 * 2
def baseEnd_1479097 : Nat := 168775043471845502196725

theorem tailTrace_1479097 : CollatzResearch.WordTrace tailWord_1479097 prefixEnd_1479097 168775043471845502196725 := by
  unfold tailWord_1479097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53947099522491653501427545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35964733014994435667618363 53947099522491653501427545)
  ·
    refine ⟨40460324641868740126070659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53947099522491653501427545 40460324641868740126070659)
    ·
      refine ⟨60690486962803110189105989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40460324641868740126070659 60690486962803110189105989)
      ·
        refine ⟨11379466305525583160457373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60690486962803110189105989 11379466305525583160457373)
        ·
          refine ⟨4267299864572093685171515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11379466305525583160457373 4267299864572093685171515)
          ·
            refine ⟨6400949796858140527757273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267299864572093685171515 6400949796858140527757273)
            ·
              refine ⟨4800712347643605395817955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6400949796858140527757273 4800712347643605395817955)
              ·
                refine ⟨7201068521465408093726933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800712347643605395817955 7201068521465408093726933)
                ·
                  refine ⟨168775043471845502196725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7201068521465408093726933 168775043471845502196725)
                  ·
                    rfl

theorem cell22_1479097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_1479097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479097 prefixEnd_1479097 := by exact prefixLift 1479097
  have htrace : WordTrace (prefixWord ++ tailWord_1479097) baseStart_1479097 baseEnd_1479097 := by
    simpa [prefixWord, tailWord_1479097, baseEnd_1479097] using wordTrace_append hprefix tailTrace_1479097
  have hstable : (prefixWord ++ tailWord_1479097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479097).length < 2 ^ (prefixWord ++ tailWord_1479097).sum := by decide
  have hdescent : baseEnd_1479097 < baseStart_1479097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479101 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_1479101 : Nat := 118140960795 + 1479101 * 2 ^ 59
def prefixEnd_1479101 : Nat := 4983230072969 + 3 ^ 40 * 1479101 * 2
def baseEnd_1479101 : Nat := 506326499697281829490163

theorem tailTrace_1479101 : CollatzResearch.WordTrace tailWord_1479101 prefixEnd_1479101 506326499697281829490163 := by
  unfold tailWord_1479101
  simp only [CollatzResearch.WordTrace]
  refine ⟨53947245414477162184573157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35964830276318108123048771 53947245414477162184573157)
  ·
    refine ⟨10115108515214467909607467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53947245414477162184573157 10115108515214467909607467)
    ·
      refine ⟨15172662772821701864411201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10115108515214467909607467 15172662772821701864411201)
      ·
        refine ⟨11379497079616276398308401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15172662772821701864411201 11379497079616276398308401)
        ·
          refine ⟨8534622809712207298731301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11379497079616276398308401 8534622809712207298731301)
          ·
            refine ⟨1600241776821038868512119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8534622809712207298731301 1600241776821038868512119)
            ·
              refine ⟨2400362665231558302768179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600241776821038868512119 2400362665231558302768179)
              ·
                refine ⟨3600543997847337454152269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400362665231558302768179 3600543997847337454152269)
                ·
                  refine ⟨1350203999192751545307101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3600543997847337454152269 1350203999192751545307101)
                  ·
                    refine ⟨506326499697281829490163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350203999192751545307101 506326499697281829490163)
                    ·
                      rfl

theorem cell22_1479101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_1479101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479101 prefixEnd_1479101 := by exact prefixLift 1479101
  have htrace : WordTrace (prefixWord ++ tailWord_1479101) baseStart_1479101 baseEnd_1479101 := by
    simpa [prefixWord, tailWord_1479101, baseEnd_1479101] using wordTrace_append hprefix tailTrace_1479101
  have hstable : (prefixWord ++ tailWord_1479101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479101).length < 2 ^ (prefixWord ++ tailWord_1479101).sum := by decide
  have hdescent : baseEnd_1479101 < baseStart_1479101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479208 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1479208 : Nat := 118140960795 + 1479208 * 2 ^ 59
def prefixEnd_1479208 : Nat := 4983230072969 + 3 ^ 40 * 1479208 * 2
def baseEnd_1479208 : Nat := 506363127983969217064835

theorem tailTrace_1479208 : CollatzResearch.WordTrace tailWord_1479208 prefixEnd_1479208 506363127983969217064835 := by
  unfold tailWord_1479208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26975574012544759729359139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35967432016726346305812185 26975574012544759729359139)
  ·
    refine ⟨40463361018817139594038709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26975574012544759729359139 40463361018817139594038709)
    ·
      refine ⟨3793440095514106836941129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40463361018817139594038709 3793440095514106836941129)
      ·
        refine ⟨2845080071635580127705847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3793440095514106836941129 2845080071635580127705847)
        ·
          refine ⟨4267620107453370191558771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845080071635580127705847 4267620107453370191558771)
          ·
            refine ⟨6401430161180055287338157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267620107453370191558771 6401430161180055287338157)
            ·
              refine ⟨2400536310442520732751809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6401430161180055287338157 2400536310442520732751809)
              ·
                refine ⟨1800402232831890549563857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400536310442520732751809 1800402232831890549563857)
                ·
                  refine ⟨1350301674623917912172893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800402232831890549563857 1350301674623917912172893)
                  ·
                    refine ⟨506363127983969217064835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350301674623917912172893 506363127983969217064835)
                    ·
                      rfl

theorem cell22_1479208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1479208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479208 prefixEnd_1479208 := by exact prefixLift 1479208
  have htrace : WordTrace (prefixWord ++ tailWord_1479208) baseStart_1479208 baseEnd_1479208 := by
    simpa [prefixWord, tailWord_1479208, baseEnd_1479208] using wordTrace_append hprefix tailTrace_1479208
  have hstable : (prefixWord ++ tailWord_1479208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479208).length < 2 ^ (prefixWord ++ tailWord_1479208).sum := by decide
  have hdescent : baseEnd_1479208 < baseStart_1479208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479217 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1479217 : Nat := 118140960795 + 1479217 * 2 ^ 59
def prefixEnd_1479217 : Nat := 4983230072969 + 3 ^ 40 * 1479217 * 2
def baseEnd_1479217 : Nat := 506366208867896193589807

theorem tailTrace_1479217 : CollatzResearch.WordTrace tailWord_1479217 prefixEnd_1479217 506366208867896193589807 := by
  unfold tailWord_1479217
  simp only [CollatzResearch.WordTrace]
  refine ⟨53951476282056913995795905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35967650854704609330530603 53951476282056913995795905)
  ·
    refine ⟨40463607211542685496846929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53951476282056913995795905 40463607211542685496846929)
    ·
      refine ⟨30347705408657014122635197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40463607211542685496846929 30347705408657014122635197)
      ·
        refine ⟨11380389528246380295988199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30347705408657014122635197 11380389528246380295988199)
        ·
          refine ⟨17070584292369570443982299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11380389528246380295988199 17070584292369570443982299)
          ·
            refine ⟨25605876438554355665973449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17070584292369570443982299 25605876438554355665973449)
            ·
              refine ⟨19204407328915766749480087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25605876438554355665973449 19204407328915766749480087)
              ·
                refine ⟨28806610993373650124220131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19204407328915766749480087 28806610993373650124220131)
                ·
                  refine ⟨43209916490060475186330197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28806610993373650124220131 43209916490060475186330197)
                  ·
                    refine ⟨506366208867896193589807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43209916490060475186330197 506366208867896193589807)
                    ·
                      rfl

theorem cell22_1479217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1479217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479217 prefixEnd_1479217 := by exact prefixLift 1479217
  have htrace : WordTrace (prefixWord ++ tailWord_1479217) baseStart_1479217 baseEnd_1479217 := by
    simpa [prefixWord, tailWord_1479217, baseEnd_1479217] using wordTrace_append hprefix tailTrace_1479217
  have hstable : (prefixWord ++ tailWord_1479217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479217).length < 2 ^ (prefixWord ++ tailWord_1479217).sum := by decide
  have hdescent : baseEnd_1479217 < baseStart_1479217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479238 : List Nat := [6, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1479238 : Nat := 118140960795 + 1479238 * 2 ^ 59
def prefixEnd_1479238 : Nat := 4983230072969 + 3 ^ 40 * 1479238 * 2
def baseEnd_1479238 : Nat := 56263710844117682090527

theorem tailTrace_1479238 : CollatzResearch.WordTrace tailWord_1479238 prefixEnd_1479238 56263710844117682090527 := by
  unfold tailWord_1479238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686007569218151080697199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35968161476653889721540245 1686007569218151080697199)
  ·
    refine ⟨2529011353827226621045799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686007569218151080697199 2529011353827226621045799)
    ·
      refine ⟨3793517030740839931568699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529011353827226621045799 3793517030740839931568699)
      ·
        refine ⟨5690275546111259897353049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793517030740839931568699 5690275546111259897353049)
        ·
          refine ⟨4267706659583444923014787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690275546111259897353049 4267706659583444923014787)
          ·
            refine ⟨6401559989375167384522181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267706659583444923014787 6401559989375167384522181)
            ·
              refine ⟨1200292498007843884597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6401559989375167384522181 1200292498007843884597909)
              ·
                refine ⟨56263710844117682090527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1200292498007843884597909 56263710844117682090527)
                ·
                  rfl

theorem cell22_1479238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1479238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479238 prefixEnd_1479238 := by exact prefixLift 1479238
  have htrace : WordTrace (prefixWord ++ tailWord_1479238) baseStart_1479238 baseEnd_1479238 := by
    simpa [prefixWord, tailWord_1479238, baseEnd_1479238] using wordTrace_append hprefix tailTrace_1479238
  have hstable : (prefixWord ++ tailWord_1479238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479238).length < 2 ^ (prefixWord ++ tailWord_1479238).sum := by decide
  have hdescent : baseEnd_1479238 < baseStart_1479238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479247 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1479247 : Nat := 118140960795 + 1479247 * 2 ^ 59
def prefixEnd_1479247 : Nat := 4983230072969 + 3 ^ 40 * 1479247 * 2
def baseEnd_1479247 : Nat := 506376478480986115339715

theorem tailTrace_1479247 : CollatzResearch.WordTrace tailWord_1479247 prefixEnd_1479247 506376478480986115339715 := by
  unfold tailWord_1479247
  simp only [CollatzResearch.WordTrace]
  refine ⟨53952570471948229119387995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35968380314632152746258663 53952570471948229119387995)
  ·
    refine ⟨80928855707922343679081993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53952570471948229119387995 80928855707922343679081993)
    ·
      refine ⟨60696641780941757759311495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80928855707922343679081993 60696641780941757759311495)
      ·
        refine ⟨91044962671412636638967243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60696641780941757759311495 91044962671412636638967243)
        ·
          refine ⟨136567444007118954958450865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91044962671412636638967243 136567444007118954958450865)
          ·
            refine ⟨102425583005339216218838149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136567444007118954958450865 102425583005339216218838149)
            ·
              refine ⟨19204796813501103041032153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102425583005339216218838149 19204796813501103041032153)
              ·
                refine ⟨14403597610125827280774115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19204796813501103041032153 14403597610125827280774115)
                ·
                  refine ⟨21605396415188740921161173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14403597610125827280774115 21605396415188740921161173)
                  ·
                    refine ⟨506376478480986115339715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21605396415188740921161173 506376478480986115339715)
                    ·
                      rfl

theorem cell22_1479247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1479247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479247 prefixEnd_1479247 := by exact prefixLift 1479247
  have htrace : WordTrace (prefixWord ++ tailWord_1479247) baseStart_1479247 baseEnd_1479247 := by
    simpa [prefixWord, tailWord_1479247, baseEnd_1479247] using wordTrace_append hprefix tailTrace_1479247
  have hstable : (prefixWord ++ tailWord_1479247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479247).length < 2 ^ (prefixWord ++ tailWord_1479247).sum := by decide
  have hdescent : baseEnd_1479247 < baseStart_1479247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479253 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1479253 : Nat := 118140960795 + 1479253 * 2 ^ 59
def prefixEnd_1479253 : Nat := 4983230072969 + 3 ^ 40 * 1479253 * 2
def baseEnd_1479253 : Nat := 506378532403604099689697

theorem tailTrace_1479253 : CollatzResearch.WordTrace tailWord_1479253 prefixEnd_1479253 506378532403604099689697 := by
  unfold tailWord_1479253
  simp only [CollatzResearch.WordTrace]
  refine ⟨53952789309926492144106413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35968526206617661429404275 53952789309926492144106413)
  ·
    refine ⟨20232295991222434554039905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53952789309926492144106413 20232295991222434554039905)
    ·
      refine ⟨15174221993416825915529929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20232295991222434554039905 15174221993416825915529929)
      ·
        refine ⟨11380666495062619436647447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15174221993416825915529929 11380666495062619436647447)
        ·
          refine ⟨17070999742593929154971171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11380666495062619436647447 17070999742593929154971171)
          ·
            refine ⟨25606499613890893732456757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17070999742593929154971171 25606499613890893732456757)
            ·
              refine ⟨2400609338802271287417821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25606499613890893732456757 2400609338802271287417821)
              ·
                refine ⟨900228502050851732781683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400609338802271287417821 900228502050851732781683)
                ·
                  refine ⟨1350342753076277599172525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900228502050851732781683 1350342753076277599172525)
                  ·
                    refine ⟨506378532403604099689697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350342753076277599172525 506378532403604099689697)
                    ·
                      rfl

theorem cell22_1479253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1479253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479253 prefixEnd_1479253 := by exact prefixLift 1479253
  have htrace : WordTrace (prefixWord ++ tailWord_1479253) baseStart_1479253 baseEnd_1479253 := by
    simpa [prefixWord, tailWord_1479253, baseEnd_1479253] using wordTrace_append hprefix tailTrace_1479253
  have hstable : (prefixWord ++ tailWord_1479253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479253).length < 2 ^ (prefixWord ++ tailWord_1479253).sum := by decide
  have hdescent : baseEnd_1479253 < baseStart_1479253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479296 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_1479296 : Nat := 118140960795 + 1479296 * 2 ^ 59
def prefixEnd_1479296 : Nat := 4983230072969 + 3 ^ 40 * 1479296 * 2
def baseEnd_1479296 : Nat := 506393252182366320864565

theorem tailTrace_1479296 : CollatzResearch.WordTrace tailWord_1479296 prefixEnd_1479296 506393252182366320864565 := by
  unfold tailWord_1479296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977178824385355243960871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35969571765847140325281161 26977178824385355243960871)
  ·
    refine ⟨40465768236578032865941307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977178824385355243960871 40465768236578032865941307)
    ·
      refine ⟨60698652354867049298911961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40465768236578032865941307 60698652354867049298911961)
      ·
        refine ⟨45523989266150286974183971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60698652354867049298911961 45523989266150286974183971)
        ·
          refine ⟨68285983899225430461275957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45523989266150286974183971 68285983899225430461275957)
          ·
            refine ⟨6401810990552384105744621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68285983899225430461275957 6401810990552384105744621)
            ·
              refine ⟨2400679121457144039654233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6401810990552384105744621 2400679121457144039654233)
              ·
                refine ⟨1800509341092858029740675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400679121457144039654233 1800509341092858029740675)
                ·
                  refine ⟨2700764011639287044611013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800509341092858029740675 2700764011639287044611013)
                  ·
                    refine ⟨506393252182366320864565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700764011639287044611013 506393252182366320864565)
                    ·
                      rfl

theorem cell22_1479296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_1479296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479296 prefixEnd_1479296 := by exact prefixLift 1479296
  have htrace : WordTrace (prefixWord ++ tailWord_1479296) baseStart_1479296 baseEnd_1479296 := by
    simpa [prefixWord, tailWord_1479296, baseEnd_1479296] using wordTrace_append hprefix tailTrace_1479296
  have hstable : (prefixWord ++ tailWord_1479296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479296).length < 2 ^ (prefixWord ++ tailWord_1479296).sum := by decide
  have hdescent : baseEnd_1479296 < baseStart_1479296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479326 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1479326 : Nat := 118140960795 + 1479326 * 2 ^ 59
def prefixEnd_1479326 : Nat := 4983230072969 + 3 ^ 40 * 1479326 * 2
def baseEnd_1479326 : Nat := 506403521795456242614473

theorem tailTrace_1479326 : CollatzResearch.WordTrace tailWord_1479326 prefixEnd_1479326 506403521795456242614473 := by
  unfold tailWord_1479326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744431479832753201439229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35970301225774683741009221 6744431479832753201439229)
  ·
    refine ⟨2529161804937282450539711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6744431479832753201439229 2529161804937282450539711)
    ·
      refine ⟨3793742707405923675809567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529161804937282450539711 3793742707405923675809567)
      ·
        refine ⟨5690614061108885513714351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793742707405923675809567 5690614061108885513714351)
        ·
          refine ⟨8535921091663328270571527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690614061108885513714351 8535921091663328270571527)
          ·
            refine ⟨12803881637494992405857291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535921091663328270571527 12803881637494992405857291)
            ·
              refine ⟨19205822456242488608785937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803881637494992405857291 19205822456242488608785937)
              ·
                refine ⟨14404366842181866456589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19205822456242488608785937 14404366842181866456589453)
                ·
                  refine ⟨5401637565818199921221045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14404366842181866456589453 5401637565818199921221045)
                  ·
                    refine ⟨506403521795456242614473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5401637565818199921221045 506403521795456242614473)
                    ·
                      rfl

theorem cell22_1479326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1479326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479326 prefixEnd_1479326 := by exact prefixLift 1479326
  have htrace : WordTrace (prefixWord ++ tailWord_1479326) baseStart_1479326 baseEnd_1479326 := by
    simpa [prefixWord, tailWord_1479326, baseEnd_1479326] using wordTrace_append hprefix tailTrace_1479326
  have hstable : (prefixWord ++ tailWord_1479326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479326).length < 2 ^ (prefixWord ++ tailWord_1479326).sum := by decide
  have hdescent : baseEnd_1479326 < baseStart_1479326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479328 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_1479328 : Nat := 118140960795 + 1479328 * 2 ^ 59
def prefixEnd_1479328 : Nat := 4983230072969 + 3 ^ 40 * 1479328 * 2
def baseEnd_1479328 : Nat := 168801402145442968021489

theorem tailTrace_1479328 : CollatzResearch.WordTrace tailWord_1479328 prefixEnd_1479328 168801402145442968021489 := by
  unfold tailWord_1479328
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977762392327389976543319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35970349856436519968724425 26977762392327389976543319)
  ·
    refine ⟨40466643588491084964814979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977762392327389976543319 40466643588491084964814979)
    ·
      refine ⟨60699965382736627447222469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40466643588491084964814979 60699965382736627447222469)
      ·
        refine ⟨11381243509263117646354213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60699965382736627447222469 11381243509263117646354213)
        ·
          refine ⟨2133983157986834558691415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11381243509263117646354213 2133983157986834558691415)
          ·
            refine ⟨3200974736980251838037123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133983157986834558691415 3200974736980251838037123)
            ·
              refine ⟨4801462105470377757055685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200974736980251838037123 4801462105470377757055685)
              ·
                refine ⟨900274144775695829447941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4801462105470377757055685 900274144775695829447941)
                ·
                  refine ⟨168801402145442968021489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900274144775695829447941 168801402145442968021489)
                  ·
                    rfl

theorem cell22_1479328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_1479328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479328 prefixEnd_1479328 := by exact prefixLift 1479328
  have htrace : WordTrace (prefixWord ++ tailWord_1479328) baseStart_1479328 baseEnd_1479328 := by
    simpa [prefixWord, tailWord_1479328, baseEnd_1479328] using wordTrace_append hprefix tailTrace_1479328
  have hstable : (prefixWord ++ tailWord_1479328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479328).length < 2 ^ (prefixWord ++ tailWord_1479328).sum := by decide
  have hdescent : baseEnd_1479328 < baseStart_1479328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479356 : List Nat := [2, 2, 2, 3, 1, 1, 5, 6]
def baseStart_1479356 : Nat := 118140960795 + 1479356 * 2 ^ 59
def prefixEnd_1479356 : Nat := 4983230072969 + 3 ^ 40 * 1479356 * 2
def baseEnd_1479356 : Nat := 56268199045394018262709

theorem tailTrace_1479356 : CollatzResearch.WordTrace tailWord_1479356 prefixEnd_1479356 56268199045394018262709 := by
  unfold tailWord_1479356
  simp only [CollatzResearch.WordTrace]
  refine ⟨26978273014276670367552961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35971030685702227156737281 26978273014276670367552961)
  ·
    refine ⟨20233704760707502775664721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26978273014276670367552961 20233704760707502775664721)
    ·
      refine ⟨15175278570530627081748541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20233704760707502775664721 15175278570530627081748541)
      ·
        refine ⟨5690729463948985155655703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15175278570530627081748541 5690729463948985155655703)
        ·
          refine ⟨8536094195923477733483555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690729463948985155655703 8536094195923477733483555)
          ·
            refine ⟨12804141293885216600225333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536094195923477733483555 12804141293885216600225333)
            ·
              refine ⟨1200388246301739056271125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12804141293885216600225333 1200388246301739056271125)
              ·
                refine ⟨56268199045394018262709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1200388246301739056271125 56268199045394018262709)
                ·
                  rfl

theorem cell22_1479356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_1479356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479356 prefixEnd_1479356 := by exact prefixLift 1479356
  have htrace : WordTrace (prefixWord ++ tailWord_1479356) baseStart_1479356 baseEnd_1479356 := by
    simpa [prefixWord, tailWord_1479356, baseEnd_1479356] using wordTrace_append hprefix tailTrace_1479356
  have hstable : (prefixWord ++ tailWord_1479356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479356).length < 2 ^ (prefixWord ++ tailWord_1479356).sum := by decide
  have hdescent : baseEnd_1479356 < baseStart_1479356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479373 : List Nat := [1, 6, 2, 1, 2, 1, 9]
def baseStart_1479373 : Nat := 118140960795 + 1479373 * 2 ^ 59
def prefixEnd_1479373 : Nat := 4983230072969 + 3 ^ 40 * 1479373 * 2
def baseEnd_1479373 : Nat := 18756281883554214321827

theorem tailTrace_1479373 : CollatzResearch.WordTrace tailWord_1479373 prefixEnd_1479373 18756281883554214321827 := by
  unfold tailWord_1479373
  simp only [CollatzResearch.WordTrace]
  refine ⟨53957166069491752638474773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35971444046327835092316515 53957166069491752638474773)
  ·
    refine ⟨2529242159507425904928505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53957166069491752638474773 2529242159507425904928505)
    ·
      refine ⟨1896931619630569428696379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529242159507425904928505 1896931619630569428696379)
      ·
        refine ⟨2845397429445854143044569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896931619630569428696379 2845397429445854143044569)
        ·
          refine ⟨2134048072084390607283427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845397429445854143044569 2134048072084390607283427)
          ·
            refine ⟨3201072108126585910925141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134048072084390607283427 3201072108126585910925141)
            ·
              refine ⟨18756281883554214321827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3201072108126585910925141 18756281883554214321827)
              ·
                rfl

theorem cell22_1479373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 9].length) (baseStart_1479373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479373 prefixEnd_1479373 := by exact prefixLift 1479373
  have htrace : WordTrace (prefixWord ++ tailWord_1479373) baseStart_1479373 baseEnd_1479373 := by
    simpa [prefixWord, tailWord_1479373, baseEnd_1479373] using wordTrace_append hprefix tailTrace_1479373
  have hstable : (prefixWord ++ tailWord_1479373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479373).length < 2 ^ (prefixWord ++ tailWord_1479373).sum := by decide
  have hdescent : baseEnd_1479373 < baseStart_1479373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479422 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1479422 : Nat := 118140960795 + 1479422 * 2 ^ 59
def prefixEnd_1479422 : Nat := 4983230072969 + 3 ^ 40 * 1479422 * 2
def baseEnd_1479422 : Nat := 506436384557343992214179

theorem tailTrace_1479422 : CollatzResearch.WordTrace tailWord_1479422 prefixEnd_1479422 506436384557343992214179 := by
  unfold tailWord_1479422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744869155789279250876065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35972635497542822671339013 6744869155789279250876065)
  ·
    refine ⟨5058651866841959438157049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6744869155789279250876065 5058651866841959438157049)
    ·
      refine ⟨3793988900131469578617787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5058651866841959438157049 3793988900131469578617787)
      ·
        refine ⟨5690983350197204367926681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793988900131469578617787 5690983350197204367926681)
        ·
          refine ⟨4268237512647903275945011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690983350197204367926681 4268237512647903275945011)
          ·
            refine ⟨6402356268971854913917517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268237512647903275945011 6402356268971854913917517)
            ·
              refine ⟨2400883600864445592719069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6402356268971854913917517 2400883600864445592719069)
              ·
                refine ⟨900331350324167097269651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400883600864445592719069 900331350324167097269651)
                ·
                  refine ⟨1350497025486250645904477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900331350324167097269651 1350497025486250645904477)
                  ·
                    refine ⟨506436384557343992214179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350497025486250645904477 506436384557343992214179)
                    ·
                      rfl

theorem cell22_1479422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1479422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479422 prefixEnd_1479422 := by exact prefixLift 1479422
  have htrace : WordTrace (prefixWord ++ tailWord_1479422) baseStart_1479422 baseEnd_1479422 := by
    simpa [prefixWord, tailWord_1479422, baseEnd_1479422] using wordTrace_append hprefix tailTrace_1479422
  have hstable : (prefixWord ++ tailWord_1479422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479422).length < 2 ^ (prefixWord ++ tailWord_1479422).sum := by decide
  have hdescent : baseEnd_1479422 < baseStart_1479422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479429 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 8]
def baseStart_1479429 : Nat := 118140960795 + 1479429 * 2 ^ 59
def prefixEnd_1479429 : Nat := 4983230072969 + 3 ^ 40 * 1479429 * 2
def baseEnd_1479429 : Nat := 168812926933466102429719

theorem tailTrace_1479429 : CollatzResearch.WordTrace tailWord_1479429 prefixEnd_1479429 168812926933466102429719 := by
  unfold tailWord_1479429
  simp only [CollatzResearch.WordTrace]
  refine ⟨53959208557288874202513341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35972805704859249468342227 53959208557288874202513341)
  ·
    refine ⟨20234703208983327825942503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53959208557288874202513341 20234703208983327825942503)
    ·
      refine ⟨30352054813474991738913755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20234703208983327825942503 30352054813474991738913755)
      ·
        refine ⟨45528082220212487608370633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30352054813474991738913755 45528082220212487608370633)
        ·
          refine ⟨34146061665159365706277975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45528082220212487608370633 34146061665159365706277975)
          ·
            refine ⟨51219092497739048559416963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34146061665159365706277975 51219092497739048559416963)
            ·
              refine ⟨76828638746608572839125445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51219092497739048559416963 76828638746608572839125445)
              ·
                refine ⟨14405369764989107407336021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76828638746608572839125445 14405369764989107407336021)
                ·
                  refine ⟨168812926933466102429719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14405369764989107407336021 168812926933466102429719)
                  ·
                    rfl

theorem cell22_1479429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_1479429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479429 prefixEnd_1479429 := by exact prefixLift 1479429
  have htrace : WordTrace (prefixWord ++ tailWord_1479429) baseStart_1479429 baseEnd_1479429 := by
    simpa [prefixWord, tailWord_1479429, baseEnd_1479429] using wordTrace_append hprefix tailTrace_1479429
  have hstable : (prefixWord ++ tailWord_1479429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479429).length < 2 ^ (prefixWord ++ tailWord_1479429).sum := by decide
  have hdescent : baseEnd_1479429 < baseStart_1479429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479461 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1479461 : Nat := 118140960795 + 1479461 * 2 ^ 59
def prefixEnd_1479461 : Nat := 4983230072969 + 3 ^ 40 * 1479461 * 2
def baseEnd_1479461 : Nat := 506449735054360890489059

theorem tailTrace_1479461 : CollatzResearch.WordTrace tailWord_1479461 prefixEnd_1479461 506449735054360890489059 := by
  unfold tailWord_1479461
  simp only [CollatzResearch.WordTrace]
  refine ⟨53960375693172943667678237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35973583795448629111785491 53960375693172943667678237)
  ·
    refine ⟨20235140884939853875379339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53960375693172943667678237 20235140884939853875379339)
    ·
      refine ⟨30352711327409780813069009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20235140884939853875379339 30352711327409780813069009)
      ·
        refine ⟨22764533495557335609801757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30352711327409780813069009 22764533495557335609801757)
        ·
          refine ⟨8536700060834000853675659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22764533495557335609801757 8536700060834000853675659)
          ·
            refine ⟨12805050091251001280513489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536700060834000853675659 12805050091251001280513489)
            ·
              refine ⟨9603787568438250960385117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12805050091251001280513489 9603787568438250960385117)
              ·
                refine ⟨3601420338164344110144419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9603787568438250960385117 3601420338164344110144419)
                ·
                  refine ⟨5402130507246516165216629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601420338164344110144419 5402130507246516165216629)
                  ·
                    refine ⟨506449735054360890489059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5402130507246516165216629 506449735054360890489059)
                    ·
                      rfl

theorem cell22_1479461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1479461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479461 prefixEnd_1479461 := by exact prefixLift 1479461
  have htrace : WordTrace (prefixWord ++ tailWord_1479461) baseStart_1479461 baseEnd_1479461 := by
    simpa [prefixWord, tailWord_1479461, baseEnd_1479461] using wordTrace_append hprefix tailTrace_1479461
  have hstable : (prefixWord ++ tailWord_1479461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479461).length < 2 ^ (prefixWord ++ tailWord_1479461).sum := by decide
  have hdescent : baseEnd_1479461 < baseStart_1479461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479523 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 5, 3]
def baseStart_1479523 : Nat := 118140960795 + 1479523 * 2 ^ 59
def prefixEnd_1479523 : Nat := 4983230072969 + 3 ^ 40 * 1479523 * 2
def baseEnd_1479523 : Nat := 506470958921413395438869

theorem tailTrace_1479523 : CollatzResearch.WordTrace tailWord_1479523 prefixEnd_1479523 506470958921413395438869 := by
  unfold tailWord_1479523
  simp only [CollatzResearch.WordTrace]
  refine ⟨53962637018948328256435223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35975091345965552170956815 53962637018948328256435223)
  ·
    refine ⟨80943955528422492384652835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53962637018948328256435223 80943955528422492384652835)
    ·
      refine ⟨121415933292633738576979253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80943955528422492384652835 121415933292633738576979253)
      ·
        refine ⟨11382743746184412991591805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121415933292633738576979253 11382743746184412991591805)
        ·
          refine ⟨4268528904819154871846927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11382743746184412991591805 4268528904819154871846927)
          ·
            refine ⟨6402793357228732307770391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268528904819154871846927 6402793357228732307770391)
            ·
              refine ⟨9604190035843098461655587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402793357228732307770391 9604190035843098461655587)
              ·
                refine ⟨14406285053764647692483381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9604190035843098461655587 14406285053764647692483381)
                ·
                  refine ⟨1350589223790435721170317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14406285053764647692483381 1350589223790435721170317)
                  ·
                    refine ⟨506470958921413395438869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350589223790435721170317 506470958921413395438869)
                    ·
                      rfl

theorem cell22_1479523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].length) (baseStart_1479523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479523 prefixEnd_1479523 := by exact prefixLift 1479523
  have htrace : WordTrace (prefixWord ++ tailWord_1479523) baseStart_1479523 baseEnd_1479523 := by
    simpa [prefixWord, tailWord_1479523, baseEnd_1479523] using wordTrace_append hprefix tailTrace_1479523
  have hstable : (prefixWord ++ tailWord_1479523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479523).length < 2 ^ (prefixWord ++ tailWord_1479523).sum := by decide
  have hdescent : baseEnd_1479523 < baseStart_1479523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479551 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1479551 : Nat := 118140960795 + 1479551 * 2 ^ 59
def prefixEnd_1479551 : Nat := 4983230072969 + 3 ^ 40 * 1479551 * 2
def baseEnd_1479551 : Nat := 506480543893630655738783

theorem tailTrace_1479551 : CollatzResearch.WordTrace tailWord_1479551 prefixEnd_1479551 506480543893630655738783 := by
  unfold tailWord_1479551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963658262846889038454507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35975772175231259358969671 53963658262846889038454507)
  ·
    refine ⟨80945487394270333557681761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53963658262846889038454507 80945487394270333557681761)
    ·
      refine ⟨60709115545702750168261321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80945487394270333557681761 60709115545702750168261321)
      ·
        refine ⟨45531836659277062626195991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60709115545702750168261321 45531836659277062626195991)
        ·
          refine ⟨68297754988915593939293987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45531836659277062626195991 68297754988915593939293987)
          ·
            refine ⟨102446632483373390908940981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68297754988915593939293987 102446632483373390908940981)
            ·
              refine ⟨9604371795316255397713217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102446632483373390908940981 9604371795316255397713217)
              ·
                refine ⟨7203278846487191548284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9604371795316255397713217 7203278846487191548284913)
                ·
                  refine ⟨5402459134865393661213685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7203278846487191548284913 5402459134865393661213685)
                  ·
                    refine ⟨506480543893630655738783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5402459134865393661213685 506480543893630655738783)
                    ·
                      rfl

theorem cell22_1479551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1479551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479551 prefixEnd_1479551 := by exact prefixLift 1479551
  have htrace : WordTrace (prefixWord ++ tailWord_1479551) baseStart_1479551 baseEnd_1479551 := by
    simpa [prefixWord, tailWord_1479551, baseEnd_1479551] using wordTrace_append hprefix tailTrace_1479551
  have hstable : (prefixWord ++ tailWord_1479551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479551).length < 2 ^ (prefixWord ++ tailWord_1479551).sum := by decide
  have hdescent : baseEnd_1479551 < baseStart_1479551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479574 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1479574 : Nat := 118140960795 + 1479574 * 2 ^ 59
def prefixEnd_1479574 : Nat := 4983230072969 + 3 ^ 40 * 1479574 * 2
def baseEnd_1479574 : Nat := 506488417263666262413713

theorem tailTrace_1479574 : CollatzResearch.WordTrace tailWord_1479574 prefixEnd_1479574 506488417263666262413713 := by
  unfold tailWord_1479574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372781071360222747908861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35976331427842375977694517 3372781071360222747908861)
  ·
    refine ⟨1264792901760083530465823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3372781071360222747908861 1264792901760083530465823)
    ·
      refine ⟨1897189352640125295698735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264792901760083530465823 1897189352640125295698735)
      ·
        refine ⟨2845784028960187943548103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897189352640125295698735 2845784028960187943548103)
        ·
          refine ⟨4268676043440281915322155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845784028960187943548103 4268676043440281915322155)
          ·
            refine ⟨6403014065160422872983233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268676043440281915322155 6403014065160422872983233)
            ·
              refine ⟨4802260548870317154737425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6403014065160422872983233 4802260548870317154737425)
              ·
                refine ⟨3601695411652737866053069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802260548870317154737425 3601695411652737866053069)
                ·
                  refine ⟨1350635779369776699769901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3601695411652737866053069 1350635779369776699769901)
                  ·
                    refine ⟨506488417263666262413713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350635779369776699769901 506488417263666262413713)
                    ·
                      rfl

theorem cell22_1479574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1479574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479574 prefixEnd_1479574 := by exact prefixLift 1479574
  have htrace : WordTrace (prefixWord ++ tailWord_1479574) baseStart_1479574 baseEnd_1479574 := by
    simpa [prefixWord, tailWord_1479574, baseEnd_1479574] using wordTrace_append hprefix tailTrace_1479574
  have hstable : (prefixWord ++ tailWord_1479574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479574).length < 2 ^ (prefixWord ++ tailWord_1479574).sum := by decide
  have hdescent : baseEnd_1479574 < baseStart_1479574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479591 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1479591 : Nat := 118140960795 + 1479591 * 2 ^ 59
def prefixEnd_1479591 : Nat := 4983230072969 + 3 ^ 40 * 1479591 * 2
def baseEnd_1479591 : Nat := 506494236711083884738661

theorem tailTrace_1479591 : CollatzResearch.WordTrace tailWord_1479591 prefixEnd_1479591 506494236711083884738661 := by
  unfold tailWord_1479591
  simp only [CollatzResearch.WordTrace]
  refine ⟨53965117182701975869910627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35976744788467983913273751 53965117182701975869910627)
  ·
    refine ⟨80947675774052963804865941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53965117182701975869910627 80947675774052963804865941)
    ·
      refine ⟨3794422301908732678353091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80947675774052963804865941 3794422301908732678353091)
      ·
        refine ⟨5691633452863099017529637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794422301908732678353091 5691633452863099017529637)
        ·
          refine ⟨1067181272411831065786807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5691633452863099017529637 1067181272411831065786807)
          ·
            refine ⟨1600771908617746598680211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067181272411831065786807 1600771908617746598680211)
            ·
              refine ⟨2401157862926619898020317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600771908617746598680211 2401157862926619898020317)
              ·
                refine ⟨900434198597482461757619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401157862926619898020317 900434198597482461757619)
                ·
                  refine ⟨1350651297896223692636429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900434198597482461757619 1350651297896223692636429)
                  ·
                    refine ⟨506494236711083884738661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350651297896223692636429 506494236711083884738661)
                    ·
                      rfl

theorem cell22_1479591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1479591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479591 prefixEnd_1479591 := by exact prefixLift 1479591
  have htrace : WordTrace (prefixWord ++ tailWord_1479591) baseStart_1479591 baseEnd_1479591 := by
    simpa [prefixWord, tailWord_1479591, baseEnd_1479591] using wordTrace_append hprefix tailTrace_1479591
  have hstable : (prefixWord ++ tailWord_1479591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479591).length < 2 ^ (prefixWord ++ tailWord_1479591).sum := by decide
  have hdescent : baseEnd_1479591 < baseStart_1479591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479628 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1479628 : Nat := 118140960795 + 1479628 * 2 ^ 59
def prefixEnd_1479628 : Nat := 4983230072969 + 3 ^ 40 * 1479628 * 2
def baseEnd_1479628 : Nat := 506506902567228121563547

theorem tailTrace_1479628 : CollatzResearch.WordTrace tailWord_1479628 prefixEnd_1479628 506506902567228121563547 := by
  unfold tailWord_1479628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26983233341783965594503769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35977644455711954126005025 26983233341783965594503769)
  ·
    refine ⟨20237425006337974195877827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26983233341783965594503769 20237425006337974195877827)
    ·
      refine ⟨30356137509506961293816741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20237425006337974195877827 30356137509506961293816741)
      ·
        refine ⟨5691775783032555242590639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30356137509506961293816741 5691775783032555242590639)
        ·
          refine ⟨8537663674548832863885959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691775783032555242590639 8537663674548832863885959)
          ·
            refine ⟨12806495511823249295828939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537663674548832863885959 12806495511823249295828939)
            ·
              refine ⟨19209743267734873943743409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12806495511823249295828939 19209743267734873943743409)
              ·
                refine ⟨14407307450801155457807557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19209743267734873943743409 14407307450801155457807557)
                ·
                  refine ⟨2701370147025216648338917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14407307450801155457807557 2701370147025216648338917)
                  ·
                    refine ⟨506506902567228121563547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701370147025216648338917 506506902567228121563547)
                    ·
                      rfl

theorem cell22_1479628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1479628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479628 prefixEnd_1479628 := by exact prefixLift 1479628
  have htrace : WordTrace (prefixWord ++ tailWord_1479628) baseStart_1479628 baseEnd_1479628 := by
    simpa [prefixWord, tailWord_1479628, baseEnd_1479628] using wordTrace_append hprefix tailTrace_1479628
  have hstable : (prefixWord ++ tailWord_1479628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479628).length < 2 ^ (prefixWord ++ tailWord_1479628).sum := by decide
  have hdescent : baseEnd_1479628 < baseStart_1479628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479645 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1479645 : Nat := 118140960795 + 1479645 * 2 ^ 59
def prefixEnd_1479645 : Nat := 4983230072969 + 3 ^ 40 * 1479645 * 2
def baseEnd_1479645 : Nat := 506512722014645743888495

theorem tailTrace_1479645 : CollatzResearch.WordTrace tailWord_1479645 prefixEnd_1479645 506512722014645743888495 := by
  unfold tailWord_1479645
  simp only [CollatzResearch.WordTrace]
  refine ⟨53967086724506343092376389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35978057816337562061584259 53967086724506343092376389)
  ·
    refine ⟨10118828760844939329820573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53967086724506343092376389 10118828760844939329820573)
    ·
      refine ⟨3794560785316852248682715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10118828760844939329820573 3794560785316852248682715)
      ·
        refine ⟨5691841177975278373024073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794560785316852248682715 5691841177975278373024073)
        ·
          refine ⟨4268880883481458779768055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691841177975278373024073 4268880883481458779768055)
          ·
            refine ⟨6403321325222188169652083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268880883481458779768055 6403321325222188169652083)
            ·
              refine ⟨9604981987833282254478125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403321325222188169652083 9604981987833282254478125)
              ·
                refine ⟨3601868245437480845429297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604981987833282254478125 3601868245437480845429297)
                ·
                  refine ⟨2701401184078110634071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601868245437480845429297 2701401184078110634071973)
                  ·
                    refine ⟨506512722014645743888495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701401184078110634071973 506512722014645743888495)
                    ·
                      rfl

theorem cell22_1479645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1479645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479645 prefixEnd_1479645 := by exact prefixLift 1479645
  have htrace : WordTrace (prefixWord ++ tailWord_1479645) baseStart_1479645 baseEnd_1479645 := by
    simpa [prefixWord, tailWord_1479645, baseEnd_1479645] using wordTrace_append hprefix tailTrace_1479645
  have hstable : (prefixWord ++ tailWord_1479645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479645).length < 2 ^ (prefixWord ++ tailWord_1479645).sum := by decide
  have hdescent : baseEnd_1479645 < baseStart_1479645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479666 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1479666 : Nat := 118140960795 + 1479666 * 2 ^ 59
def prefixEnd_1479666 : Nat := 4983230072969 + 3 ^ 40 * 1479666 * 2
def baseEnd_1479666 : Nat := 168839970247936229704477

theorem tailTrace_1479666 : CollatzResearch.WordTrace tailWord_1479666 prefixEnd_1479666 168839970247936229704477 := by
  unfold tailWord_1479666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491963164357565919722713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35978568438286842452593901 13491963164357565919722713)
  ·
    refine ⟨10118972373268174439792035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13491963164357565919722713 10118972373268174439792035)
    ·
      refine ⟨15178458559902261659688053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118972373268174439792035 15178458559902261659688053)
      ·
        refine ⟨1422980489990837030595755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15178458559902261659688053 1422980489990837030595755)
        ·
          refine ⟨2134470734986255545893633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422980489990837030595755 2134470734986255545893633)
          ·
            refine ⟨1600853051239691659420225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134470734986255545893633 1600853051239691659420225)
            ·
              refine ⟨1200639788429768744565169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600853051239691659420225 1200639788429768744565169)
              ·
                refine ⟨900479841322326558423877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200639788429768744565169 900479841322326558423877)
                ·
                  refine ⟨168839970247936229704477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900479841322326558423877 168839970247936229704477)
                  ·
                    rfl

theorem cell22_1479666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1479666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479666 prefixEnd_1479666 := by exact prefixLift 1479666
  have htrace : WordTrace (prefixWord ++ tailWord_1479666) baseStart_1479666 baseEnd_1479666 := by
    simpa [prefixWord, tailWord_1479666, baseEnd_1479666] using wordTrace_append hprefix tailTrace_1479666
  have hstable : (prefixWord ++ tailWord_1479666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479666).length < 2 ^ (prefixWord ++ tailWord_1479666).sum := by decide
  have hdescent : baseEnd_1479666 < baseStart_1479666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479765 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_1479765 : Nat := 118140960795 + 1479765 * 2 ^ 59
def prefixEnd_1479765 : Nat := 4983230072969 + 3 ^ 40 * 1479765 * 2
def baseEnd_1479765 : Nat := 506553800467005430888127

theorem tailTrace_1479765 : CollatzResearch.WordTrace tailWord_1479765 prefixEnd_1479765 506553800467005430888127 := by
  unfold tailWord_1479765
  simp only [CollatzResearch.WordTrace]
  refine ⟨53971463484071603586744749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35980975656047735724496499 53971463484071603586744749)
  ·
    refine ⟨20239298806526851345029281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53971463484071603586744749 20239298806526851345029281)
    ·
      refine ⟨15179474104895138508771961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20239298806526851345029281 15179474104895138508771961)
      ·
        refine ⟨11384605578671353881578971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15179474104895138508771961 11384605578671353881578971)
        ·
          refine ⟨17076908368007030822368457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384605578671353881578971 17076908368007030822368457)
          ·
            refine ⟨12807681276005273116776343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17076908368007030822368457 12807681276005273116776343)
            ·
              refine ⟨19211521914007909675164515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12807681276005273116776343 19211521914007909675164515)
              ·
                refine ⟨28817282871011864512746773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19211521914007909675164515 28817282871011864512746773)
                ·
                  refine ⟨1350810134578681149035005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28817282871011864512746773 1350810134578681149035005)
                  ·
                    refine ⟨506553800467005430888127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350810134578681149035005 506553800467005430888127)
                    ·
                      rfl

theorem cell22_1479765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_1479765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479765 prefixEnd_1479765 := by exact prefixLift 1479765
  have htrace : WordTrace (prefixWord ++ tailWord_1479765) baseStart_1479765 baseEnd_1479765 := by
    simpa [prefixWord, tailWord_1479765, baseEnd_1479765] using wordTrace_append hprefix tailTrace_1479765
  have hstable : (prefixWord ++ tailWord_1479765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479765).length < 2 ^ (prefixWord ++ tailWord_1479765).sum := by decide
  have hdescent : baseEnd_1479765 < baseStart_1479765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479784 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_1479784 : Nat := 118140960795 + 1479784 * 2 ^ 59
def prefixEnd_1479784 : Nat := 4983230072969 + 3 ^ 40 * 1479784 * 2
def baseEnd_1479784 : Nat := 168853434851765238221023

theorem tailTrace_1479784 : CollatzResearch.WordTrace tailWord_1479784 prefixEnd_1479784 168853434851765238221023 := by
  unfold tailWord_1479784
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986078235501384915843203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35981437647335179887790937 26986078235501384915843203)
  ·
    refine ⟨40479117353252077373764805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986078235501384915843203 40479117353252077373764805)
    ·
      refine ⟨7589834503734764507580901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40479117353252077373764805 7589834503734764507580901)
      ·
        refine ⟨1423093969450268345171419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7589834503734764507580901 1423093969450268345171419)
        ·
          refine ⟨2134640954175402517757129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423093969450268345171419 2134640954175402517757129)
          ·
            refine ⟨1600980715631551888317847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134640954175402517757129 1600980715631551888317847)
            ·
              refine ⟨2401471073447327832476771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600980715631551888317847 2401471073447327832476771)
              ·
                refine ⟨3602206610170991748715157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401471073447327832476771 3602206610170991748715157)
                ·
                  refine ⟨168853434851765238221023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3602206610170991748715157 168853434851765238221023)
                  ·
                    rfl

theorem cell22_1479784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_1479784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479784 prefixEnd_1479784 := by exact prefixLift 1479784
  have htrace : WordTrace (prefixWord ++ tailWord_1479784) baseStart_1479784 baseEnd_1479784 := by
    simpa [prefixWord, tailWord_1479784, baseEnd_1479784] using wordTrace_append hprefix tailTrace_1479784
  have hstable : (prefixWord ++ tailWord_1479784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479784).length < 2 ^ (prefixWord ++ tailWord_1479784).sum := by decide
  have hdescent : baseEnd_1479784 < baseStart_1479784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1479793 : Nat := 118140960795 + 1479793 * 2 ^ 59
def prefixEnd_1479793 : Nat := 4983230072969 + 3 ^ 40 * 1479793 * 2
def baseEnd_1479793 : Nat := 506563385439222691188041

theorem tailTrace_1479793 : CollatzResearch.WordTrace tailWord_1479793 prefixEnd_1479793 506563385439222691188041 := by
  unfold tailWord_1479793
  simp only [CollatzResearch.WordTrace]
  refine ⟨53972484727970164368764033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35981656485313442912509355 53972484727970164368764033)
  ·
    refine ⟨40479363545977623276573025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53972484727970164368764033 40479363545977623276573025)
    ·
      refine ⟨30359522659483217457429769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40479363545977623276573025 30359522659483217457429769)
      ·
        refine ⟨22769641994612413093072327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30359522659483217457429769 22769641994612413093072327)
        ·
          refine ⟨34154462991918619639608491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22769641994612413093072327 34154462991918619639608491)
          ·
            refine ⟨51231694487877929459412737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34154462991918619639608491 51231694487877929459412737)
            ·
              refine ⟨38423770865908447094559553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51231694487877929459412737 38423770865908447094559553)
              ·
                refine ⟨28817828149431335320919665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38423770865908447094559553 28817828149431335320919665)
                ·
                  refine ⟨21613371112073501490689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28817828149431335320919665 21613371112073501490689749)
                  ·
                    refine ⟨506563385439222691188041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21613371112073501490689749 506563385439222691188041)
                    ·
                      rfl

theorem cell22_1479793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1479793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479793 prefixEnd_1479793 := by exact prefixLift 1479793
  have htrace : WordTrace (prefixWord ++ tailWord_1479793) baseStart_1479793 baseEnd_1479793 := by
    simpa [prefixWord, tailWord_1479793, baseEnd_1479793] using wordTrace_append hprefix tailTrace_1479793
  have hstable : (prefixWord ++ tailWord_1479793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479793).length < 2 ^ (prefixWord ++ tailWord_1479793).sum := by decide
  have hdescent : baseEnd_1479793 < baseStart_1479793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479857 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 5]
def baseStart_1479857 : Nat := 118140960795 + 1479857 * 2 ^ 59
def prefixEnd_1479857 : Nat := 4983230072969 + 3 ^ 40 * 1479857 * 2
def baseEnd_1479857 : Nat := 168861764649049285862615

theorem tailTrace_1479857 : CollatzResearch.WordTrace tailWord_1479857 prefixEnd_1479857 168861764649049285862615 := by
  unfold tailWord_1479857
  simp only [CollatzResearch.WordTrace]
  refine ⟨53974818999738303299093825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35983212666492202199395883 53974818999738303299093825)
  ·
    refine ⟨40481114249803727474320369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53974818999738303299093825 40481114249803727474320369)
    ·
      refine ⟨30360835687352795605740277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40481114249803727474320369 30360835687352795605740277)
      ·
        refine ⟨2846328345689324588038151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30360835687352795605740277 2846328345689324588038151)
        ·
          refine ⟨4269492518533986882057227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846328345689324588038151 4269492518533986882057227)
          ·
            refine ⟨6404238777800980323085841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269492518533986882057227 6404238777800980323085841)
            ·
              refine ⟨4803179083350735242314381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404238777800980323085841 4803179083350735242314381)
              ·
                refine ⟨1801192156256525715867893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803179083350735242314381 1801192156256525715867893)
                ·
                  refine ⟨168861764649049285862615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1801192156256525715867893 168861764649049285862615)
                  ·
                    rfl

theorem cell22_1479857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_1479857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479857 prefixEnd_1479857 := by exact prefixLift 1479857
  have htrace : WordTrace (prefixWord ++ tailWord_1479857) baseStart_1479857 baseEnd_1479857 := by
    simpa [prefixWord, tailWord_1479857, baseEnd_1479857] using wordTrace_append hprefix tailTrace_1479857
  have hstable : (prefixWord ++ tailWord_1479857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479857).length < 2 ^ (prefixWord ++ tailWord_1479857).sum := by decide
  have hdescent : baseEnd_1479857 < baseStart_1479857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479915 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_1479915 : Nat := 118140960795 + 1479915 * 2 ^ 59
def prefixEnd_1479915 : Nat := 4983230072969 + 3 ^ 40 * 1479915 * 2
def baseEnd_1479915 : Nat := 506605148532455039637667

theorem tailTrace_1479915 : CollatzResearch.WordTrace tailWord_1479915 prefixEnd_1479915 506605148532455039637667 := by
  unfold tailWord_1479915
  simp only [CollatzResearch.WordTrace]
  refine ⟨53976934433528179204705199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35984622955685452803136799 53976934433528179204705199)
  ·
    refine ⟨80965401650292268807057799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53976934433528179204705199 80965401650292268807057799)
    ·
      refine ⟨121448102475438403210586699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80965401650292268807057799 121448102475438403210586699)
      ·
        refine ⟨182172153713157604815880049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121448102475438403210586699 182172153713157604815880049)
        ·
          refine ⟨136629115284868203611910037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182172153713157604815880049 136629115284868203611910037)
          ·
            refine ⟨6404489778978197044308283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136629115284868203611910037 6404489778978197044308283)
            ·
              refine ⟨9606734668467295566462425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404489778978197044308283 9606734668467295566462425)
              ·
                refine ⟨7205051001350471674846819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606734668467295566462425 7205051001350471674846819)
                ·
                  refine ⟨10807576502025707512270229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205051001350471674846819 10807576502025707512270229)
                  ·
                    refine ⟨506605148532455039637667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10807576502025707512270229 506605148532455039637667)
                    ·
                      rfl

theorem cell22_1479915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_1479915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479915 prefixEnd_1479915 := by exact prefixLift 1479915
  have htrace : WordTrace (prefixWord ++ tailWord_1479915) baseStart_1479915 baseEnd_1479915 := by
    simpa [prefixWord, tailWord_1479915, baseEnd_1479915] using wordTrace_append hprefix tailTrace_1479915
  have hstable : (prefixWord ++ tailWord_1479915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479915).length < 2 ^ (prefixWord ++ tailWord_1479915).sum := by decide
  have hdescent : baseEnd_1479915 < baseStart_1479915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479930 : List Nat := [3, 1, 1, 1, 1, 4, 3, 8]
def baseStart_1479930 : Nat := 118140960795 + 1479930 * 2 ^ 59
def prefixEnd_1479930 : Nat := 4983230072969 + 3 ^ 40 * 1479930 * 2
def baseEnd_1479930 : Nat := 56290031482111111168069

theorem tailTrace_1479930 : CollatzResearch.WordTrace tailWord_1479930 prefixEnd_1479930 56290031482111111168069 := by
  unfold tailWord_1479930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494370382118459191625311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35984987685649224511000829 13494370382118459191625311)
  ·
    refine ⟨20241555573177688787437967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13494370382118459191625311 20241555573177688787437967)
    ·
      refine ⟨30362333359766533181156951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20241555573177688787437967 30362333359766533181156951)
      ·
        refine ⟨45543500039649799771735427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30362333359766533181156951 45543500039649799771735427)
        ·
          refine ⟨68315250059474699657603141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45543500039649799771735427 68315250059474699657603141)
          ·
            refine ⟨12809109386151506185800589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68315250059474699657603141 12809109386151506185800589)
            ·
              refine ⟨4803416019806814819675221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12809109386151506185800589 4803416019806814819675221)
              ·
                refine ⟨56290031482111111168069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4803416019806814819675221 56290031482111111168069)
                ·
                  rfl

theorem cell22_1479930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_1479930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479930 prefixEnd_1479930 := by exact prefixLift 1479930
  have htrace : WordTrace (prefixWord ++ tailWord_1479930) baseStart_1479930 baseEnd_1479930 := by
    simpa [prefixWord, tailWord_1479930, baseEnd_1479930] using wordTrace_append hprefix tailTrace_1479930
  have hstable : (prefixWord ++ tailWord_1479930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479930).length < 2 ^ (prefixWord ++ tailWord_1479930).sum := by decide
  have hdescent : baseEnd_1479930 < baseStart_1479930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479934 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1479934 : Nat := 118140960795 + 1479934 * 2 ^ 59
def prefixEnd_1479934 : Nat := 4983230072969 + 3 ^ 40 * 1479934 * 2
def baseEnd_1479934 : Nat := 506611652620745323412609

theorem tailTrace_1479934 : CollatzResearch.WordTrace tailWord_1479934 prefixEnd_1479934 506611652620745323412609 := by
  unfold tailWord_1479934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747203427557418181205857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35985084946972896966431237 6747203427557418181205857)
  ·
    refine ⟨5060402570668063635904393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6747203427557418181205857 5060402570668063635904393)
    ·
      refine ⟨3795301928001047726928295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5060402570668063635904393 3795301928001047726928295)
      ·
        refine ⟨5692952892001571590392443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795301928001047726928295 5692952892001571590392443)
        ·
          refine ⟨8539429338002357385588665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692952892001571590392443 8539429338002357385588665)
          ·
            refine ⟨6404572003501768039191499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8539429338002357385588665 6404572003501768039191499)
            ·
              refine ⟨9606858005252652058787249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404572003501768039191499 9606858005252652058787249)
              ·
                refine ⟨7205143503939489044090437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606858005252652058787249 7205143503939489044090437)
                ·
                  refine ⟨1350964406988654195766957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7205143503939489044090437 1350964406988654195766957)
                  ·
                    refine ⟨506611652620745323412609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350964406988654195766957 506611652620745323412609)
                    ·
                      rfl

theorem cell22_1479934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1479934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479934 prefixEnd_1479934 := by exact prefixLift 1479934
  have htrace : WordTrace (prefixWord ++ tailWord_1479934) baseStart_1479934 baseEnd_1479934 := by
    simpa [prefixWord, tailWord_1479934, baseEnd_1479934] using wordTrace_append hprefix tailTrace_1479934
  have hstable : (prefixWord ++ tailWord_1479934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479934).length < 2 ^ (prefixWord ++ tailWord_1479934).sum := by decide
  have hdescent : baseEnd_1479934 < baseStart_1479934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479968 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_1479968 : Nat := 118140960795 + 1479968 * 2 ^ 59
def prefixEnd_1479968 : Nat := 4983230072969 + 3 ^ 40 * 1479968 * 2
def baseEnd_1479968 : Nat := 506623291515580568062505

theorem tailTrace_1479968 : CollatzResearch.WordTrace tailWord_1479968 prefixEnd_1479968 506623291515580568062505 := by
  unfold tailWord_1479968
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989433751168084628192279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35985911668224112837589705 26989433751168084628192279)
  ·
    refine ⟨40484150626752126942288419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26989433751168084628192279 40484150626752126942288419)
    ·
      refine ⟨60726225940128190413432629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40484150626752126942288419 60726225940128190413432629)
      ·
        refine ⟨5693083681887017851259309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60726225940128190413432629 5693083681887017851259309)
        ·
          refine ⟨2134906380707631694222241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5693083681887017851259309 2134906380707631694222241)
          ·
            refine ⟨1601179785530723770666681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134906380707631694222241 1601179785530723770666681)
            ·
              refine ⟨1200884839148042828000011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601179785530723770666681 1200884839148042828000011)
              ·
                refine ⟨1801327258722064242000017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200884839148042828000011 1801327258722064242000017)
                ·
                  refine ⟨1350995444041548181500013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801327258722064242000017 1350995444041548181500013)
                  ·
                    refine ⟨506623291515580568062505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1350995444041548181500013 506623291515580568062505)
                    ·
                      rfl

theorem cell22_1479968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_1479968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1479968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1479968 prefixEnd_1479968 := by exact prefixLift 1479968
  have htrace : WordTrace (prefixWord ++ tailWord_1479968) baseStart_1479968 baseEnd_1479968 := by
    simpa [prefixWord, tailWord_1479968, baseEnd_1479968] using wordTrace_append hprefix tailTrace_1479968
  have hstable : (prefixWord ++ tailWord_1479968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479968).length < 2 ^ (prefixWord ++ tailWord_1479968).sum := by decide
  have hdescent : baseEnd_1479968 < baseStart_1479968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480037 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 6]
def baseStart_1480037 : Nat := 118140960795 + 1480037 * 2 ^ 59
def prefixEnd_1480037 : Nat := 4983230072969 + 3 ^ 40 * 1480037 * 2
def baseEnd_1480037 : Nat := 168882303875229129362431

theorem tailTrace_1480037 : CollatzResearch.WordTrace tailWord_1480037 prefixEnd_1480037 168882303875229129362431 := by
  unfold tailWord_1480037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53981384139086194040646365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35987589426057462693764243 53981384139086194040646365)
  ·
    refine ⟨20243019052157322765242387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53981384139086194040646365 20243019052157322765242387)
    ·
      refine ⟨30364528578235984147863581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20243019052157322765242387 30364528578235984147863581)
      ·
        refine ⟨11386698216838494055448843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30364528578235984147863581 11386698216838494055448843)
        ·
          refine ⟨17080047325257741083173265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386698216838494055448843 17080047325257741083173265)
          ·
            refine ⟨12810035493943305812379949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17080047325257741083173265 12810035493943305812379949)
            ·
              refine ⟨4803763310228739679642481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12810035493943305812379949 4803763310228739679642481)
              ·
                refine ⟨3602822482671554759731861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803763310228739679642481 3602822482671554759731861)
                ·
                  refine ⟨168882303875229129362431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3602822482671554759731861 168882303875229129362431)
                  ·
                    rfl

theorem cell22_1480037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_1480037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480037 prefixEnd_1480037 := by exact prefixLift 1480037
  have htrace : WordTrace (prefixWord ++ tailWord_1480037) baseStart_1480037 baseEnd_1480037 := by
    simpa [prefixWord, tailWord_1480037, baseEnd_1480037] using wordTrace_append hprefix tailTrace_1480037
  have hstable : (prefixWord ++ tailWord_1480037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480037).length < 2 ^ (prefixWord ++ tailWord_1480037).sum := by decide
  have hdescent : baseEnd_1480037 < baseStart_1480037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480084 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1480084 : Nat := 118140960795 + 1480084 * 2 ^ 59
def prefixEnd_1480084 : Nat := 4983230072969 + 3 ^ 40 * 1480084 * 2
def baseEnd_1480084 : Nat := 506663000686194932162149

theorem tailTrace_1480084 : CollatzResearch.WordTrace tailWord_1480084 prefixEnd_1480084 506663000686194932162149 := by
  unfold tailWord_1480084
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991549184957960533803653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35988732246610614045071537 26991549184957960533803653)
  ·
    refine ⟨5060915472179617600088185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26991549184957960533803653 5060915472179617600088185)
    ·
      refine ⟨3795686604134713200066139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5060915472179617600088185 3795686604134713200066139)
      ·
        refine ⟨5693529906202069800099209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795686604134713200066139 5693529906202069800099209)
        ·
          refine ⟨4270147429651552350074407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693529906202069800099209 4270147429651552350074407)
          ·
            refine ⟨6405221144477328525111611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270147429651552350074407 6405221144477328525111611)
            ·
              refine ⟨9607831716715992787667417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405221144477328525111611 9607831716715992787667417)
              ·
                refine ⟨7205873787536994590750563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9607831716715992787667417 7205873787536994590750563)
                ·
                  refine ⟨10808810681305491886125845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205873787536994590750563 10808810681305491886125845)
                  ·
                    refine ⟨506663000686194932162149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10808810681305491886125845 506663000686194932162149)
                    ·
                      rfl

theorem cell22_1480084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1480084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480084 prefixEnd_1480084 := by exact prefixLift 1480084
  have htrace : WordTrace (prefixWord ++ tailWord_1480084) baseStart_1480084 baseEnd_1480084 := by
    simpa [prefixWord, tailWord_1480084, baseEnd_1480084] using wordTrace_append hprefix tailTrace_1480084
  have hstable : (prefixWord ++ tailWord_1480084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480084).length < 2 ^ (prefixWord ++ tailWord_1480084).sum := by decide
  have hdescent : baseEnd_1480084 < baseStart_1480084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480131 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 1, 3]
def baseStart_1480131 : Nat := 118140960795 + 1480131 * 2 ^ 59
def prefixEnd_1480131 : Nat := 4983230072969 + 3 ^ 40 * 1480131 * 2
def baseEnd_1480131 : Nat := 506679089746702476237005

theorem tailTrace_1480131 : CollatzResearch.WordTrace tailWord_1480131 prefixEnd_1480131 506679089746702476237005 := by
  unfold tailWord_1480131
  simp only [CollatzResearch.WordTrace]
  refine ⟨53984812600745648094568247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35989875067163765396378831 53984812600745648094568247)
  ·
    refine ⟨80977218901118472141852371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53984812600745648094568247 80977218901118472141852371)
    ·
      refine ⟨121465828351677708212778557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80977218901118472141852371 121465828351677708212778557)
      ·
        refine ⟨45549685631879140579791959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121465828351677708212778557 45549685631879140579791959)
        ·
          refine ⟨68324528447818710869687939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45549685631879140579791959 68324528447818710869687939)
          ·
            refine ⟨102486792671728066304531909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68324528447818710869687939 102486792671728066304531909)
            ·
              refine ⟨19216273625949012432099733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102486792671728066304531909 19216273625949012432099733)
              ·
                refine ⟨900762826216359957754675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19216273625949012432099733 900762826216359957754675)
                ·
                  refine ⟨1351144239324539936632013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900762826216359957754675 1351144239324539936632013)
                  ·
                    refine ⟨506679089746702476237005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351144239324539936632013 506679089746702476237005)
                    ·
                      rfl

theorem cell22_1480131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 3].length) (baseStart_1480131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480131 prefixEnd_1480131 := by exact prefixLift 1480131
  have htrace : WordTrace (prefixWord ++ tailWord_1480131) baseStart_1480131 baseEnd_1480131 := by
    simpa [prefixWord, tailWord_1480131, baseEnd_1480131] using wordTrace_append hprefix tailTrace_1480131
  have hstable : (prefixWord ++ tailWord_1480131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480131).length < 2 ^ (prefixWord ++ tailWord_1480131).sum := by decide
  have hdescent : baseEnd_1480131 < baseStart_1480131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480172 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1480172 : Nat := 118140960795 + 1480172 * 2 ^ 59
def prefixEnd_1480172 : Nat := 4983230072969 + 3 ^ 40 * 1480172 * 2
def baseEnd_1480172 : Nat := 168897708294864011987293

theorem tailTrace_1480172 : CollatzResearch.WordTrace tailWord_1480172 prefixEnd_1480172 168897708294864011987293 := by
  unfold tailWord_1480172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993153996798556048405385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35990871995731408064540513 26993153996798556048405385)
  ·
    refine ⟨20244865497598917036304039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26993153996798556048405385 20244865497598917036304039)
    ·
      refine ⟨30367298246398375554456059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244865497598917036304039 30367298246398375554456059)
      ·
        refine ⟨45550947369597563331684089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30367298246398375554456059 45550947369597563331684089)
        ·
          refine ⟨34163210527198172498763067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45550947369597563331684089 34163210527198172498763067)
          ·
            refine ⟨51244815790797258748144601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34163210527198172498763067 51244815790797258748144601)
            ·
              refine ⟨38433611843097944061108451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51244815790797258748144601 38433611843097944061108451)
              ·
                refine ⟨57650417764646916091662677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38433611843097944061108451 57650417764646916091662677)
                ·
                  refine ⟨168897708294864011987293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57650417764646916091662677 168897708294864011987293)
                  ·
                    rfl

theorem cell22_1480172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1480172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480172 prefixEnd_1480172 := by exact prefixLift 1480172
  have htrace : WordTrace (prefixWord ++ tailWord_1480172) baseStart_1480172 baseEnd_1480172 := by
    simpa [prefixWord, tailWord_1480172, baseEnd_1480172] using wordTrace_append hprefix tailTrace_1480172
  have hstable : (prefixWord ++ tailWord_1480172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480172).length < 2 ^ (prefixWord ++ tailWord_1480172).sum := by decide
  have hdescent : baseEnd_1480172 < baseStart_1480172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480182 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_1480182 : Nat := 118140960795 + 1480182 * 2 ^ 59
def prefixEnd_1480182 : Nat := 4983230072969 + 3 ^ 40 * 1480182 * 2
def baseEnd_1480182 : Nat := 506696548088955343211849

theorem tailTrace_1480182 : CollatzResearch.WordTrace tailWord_1480182 prefixEnd_1480182 506696548088955343211849 := by
  unfold tailWord_1480182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374167045222555237792175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35991115149040589203116533 3374167045222555237792175)
  ·
    refine ⟨5061250567833832856688263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374167045222555237792175 5061250567833832856688263)
    ·
      refine ⟨7591875851750749285032395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061250567833832856688263 7591875851750749285032395)
      ·
        refine ⟨11387813777626123927548593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591875851750749285032395 11387813777626123927548593)
        ·
          refine ⟨8540860333219592945661445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11387813777626123927548593 8540860333219592945661445)
          ·
            refine ⟨1601411312478673677311521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8540860333219592945661445 1601411312478673677311521)
            ·
              refine ⟨1201058484359005257983641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601411312478673677311521 1201058484359005257983641)
              ·
                refine ⟨900793863269253943487731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201058484359005257983641 900793863269253943487731)
                ·
                  refine ⟨1351190794903880915231597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900793863269253943487731 1351190794903880915231597)
                  ·
                    refine ⟨506696548088955343211849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351190794903880915231597 506696548088955343211849)
                    ·
                      rfl

theorem cell22_1480182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_1480182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480182 prefixEnd_1480182 := by exact prefixLift 1480182
  have htrace : WordTrace (prefixWord ++ tailWord_1480182) baseStart_1480182 baseEnd_1480182 := by
    simpa [prefixWord, tailWord_1480182, baseEnd_1480182] using wordTrace_append hprefix tailTrace_1480182
  have hstable : (prefixWord ++ tailWord_1480182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480182).length < 2 ^ (prefixWord ++ tailWord_1480182).sum := by decide
  have hdescent : baseEnd_1480182 < baseStart_1480182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480206 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_1480206 : Nat := 118140960795 + 1480206 * 2 ^ 59
def prefixEnd_1480206 : Nat := 4983230072969 + 3 ^ 40 * 1480206 * 2
def baseEnd_1480206 : Nat := 168901587926475760203925

theorem tailTrace_1480206 : CollatzResearch.WordTrace tailWord_1480206 prefixEnd_1480206 168901587926475760203925 := by
  unfold tailWord_1480206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748443509434241987943559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35991698716982623935698981 6748443509434241987943559)
  ·
    refine ⟨10122665264151362981915339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748443509434241987943559 10122665264151362981915339)
    ·
      refine ⟨15183997896227044472873009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10122665264151362981915339 15183997896227044472873009)
      ·
        refine ⟨11387998422170283354654757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183997896227044472873009 11387998422170283354654757)
        ·
          refine ⟨2135249704156928128997767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11387998422170283354654757 2135249704156928128997767)
          ·
            refine ⟨3202874556235392193496651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135249704156928128997767 3202874556235392193496651)
            ·
              refine ⟨4804311834353088290244977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202874556235392193496651 4804311834353088290244977)
              ·
                refine ⟨3603233875764816217683733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804311834353088290244977 3603233875764816217683733)
                ·
                  refine ⟨168901587926475760203925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3603233875764816217683733 168901587926475760203925)
                  ·
                    rfl

theorem cell22_1480206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_1480206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480206 prefixEnd_1480206 := by exact prefixLift 1480206
  have htrace : WordTrace (prefixWord ++ tailWord_1480206) baseStart_1480206 baseEnd_1480206 := by
    simpa [prefixWord, tailWord_1480206, baseEnd_1480206] using wordTrace_append hprefix tailTrace_1480206
  have hstable : (prefixWord ++ tailWord_1480206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480206).length < 2 ^ (prefixWord ++ tailWord_1480206).sum := by decide
  have hdescent : baseEnd_1480206 < baseStart_1480206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480221 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1480221 : Nat := 118140960795 + 1480221 * 2 ^ 59
def prefixEnd_1480221 : Nat := 4983230072969 + 3 ^ 40 * 1480221 * 2
def baseEnd_1480221 : Nat := 506709898585972241486729

theorem tailTrace_1480221 : CollatzResearch.WordTrace tailWord_1480221 prefixEnd_1480221 506709898585972241486729 := by
  unfold tailWord_1480221
  simp only [CollatzResearch.WordTrace]
  refine ⟨53988095170419593465344517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35992063446946395643563011 53988095170419593465344517)
  ·
    refine ⟨10122767844453673774752097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53988095170419593465344517 10122767844453673774752097)
    ·
      refine ⟨7592075883340255331064073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10122767844453673774752097 7592075883340255331064073)
      ·
        refine ⟨5694056912505191498298055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7592075883340255331064073 5694056912505191498298055)
        ·
          refine ⟨8541085368757787247447083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694056912505191498298055 8541085368757787247447083)
          ·
            refine ⟨12811628053136680871170625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541085368757787247447083 12811628053136680871170625)
            ·
              refine ⟨9608721039852510653377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811628053136680871170625 9608721039852510653377969)
              ·
                refine ⟨7206540779889382990033477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9608721039852510653377969 7206540779889382990033477)
                ·
                  refine ⟨1351226396229259310631277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7206540779889382990033477 1351226396229259310631277)
                  ·
                    refine ⟨506709898585972241486729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351226396229259310631277 506709898585972241486729)
                    ·
                      rfl

theorem cell22_1480221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1480221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480221 prefixEnd_1480221 := by exact prefixLift 1480221
  have htrace : WordTrace (prefixWord ++ tailWord_1480221) baseStart_1480221 baseEnd_1480221 := by
    simpa [prefixWord, tailWord_1480221, baseEnd_1480221] using wordTrace_append hprefix tailTrace_1480221
  have hstable : (prefixWord ++ tailWord_1480221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480221).length < 2 ^ (prefixWord ++ tailWord_1480221).sum := by decide
  have hdescent : baseEnd_1480221 < baseStart_1480221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480234 : List Nat := [3, 1, 4, 1, 1, 1, 11]
def baseStart_1480234 : Nat := 118140960795 + 1480234 * 2 ^ 59
def prefixEnd_1480234 : Nat := 4983230072969 + 3 ^ 40 * 1480234 * 2
def baseEnd_1480234 : Nat := 18767198101912760774507

theorem tailTrace_1480234 : CollatzResearch.WordTrace tailWord_1480234 prefixEnd_1480234 18767198101912760774507 := by
  unfold tailWord_1480234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497142329843124171391939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35992379546248331123711837 13497142329843124171391939)
  ·
    refine ⟨20245713494764686257087909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13497142329843124171391939 20245713494764686257087909)
    ·
      refine ⟨3796071280268378673203983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20245713494764686257087909 3796071280268378673203983)
      ·
        refine ⟨5694106920402568009805975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796071280268378673203983 5694106920402568009805975)
        ·
          refine ⟨8541160380603852014708963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694106920402568009805975 8541160380603852014708963)
          ·
            refine ⟨12811740570905778022063445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541160380603852014708963 12811740570905778022063445)
            ·
              refine ⟨18767198101912760774507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12811740570905778022063445 18767198101912760774507)
              ·
                rfl

theorem cell22_1480234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 11].length) (baseStart_1480234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480234 prefixEnd_1480234 := by exact prefixLift 1480234
  have htrace : WordTrace (prefixWord ++ tailWord_1480234) baseStart_1480234 baseEnd_1480234 := by
    simpa [prefixWord, tailWord_1480234, baseEnd_1480234] using wordTrace_append hprefix tailTrace_1480234
  have hstable : (prefixWord ++ tailWord_1480234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480234).length < 2 ^ (prefixWord ++ tailWord_1480234).sum := by decide
  have hdescent : baseEnd_1480234 < baseStart_1480234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480238 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1480238 : Nat := 118140960795 + 1480238 * 2 ^ 59
def prefixEnd_1480238 : Nat := 4983230072969 + 3 ^ 40 * 1480238 * 2
def baseEnd_1480238 : Nat := 506715718033389863811677

theorem tailTrace_1480238 : CollatzResearch.WordTrace tailWord_1480238 prefixEnd_1480238 506715718033389863811677 := by
  unfold tailWord_1480238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748589401419750671089171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35992476807572003579142245 6748589401419750671089171)
  ·
    refine ⟨10122884102129626006633757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748589401419750671089171 10122884102129626006633757)
    ·
      refine ⟨3796081538298609752487659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10122884102129626006633757 3796081538298609752487659)
      ·
        refine ⟨5694122307447914628731489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796081538298609752487659 5694122307447914628731489)
        ·
          refine ⟨4270591730585935971548617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5694122307447914628731489 4270591730585935971548617)
          ·
            refine ⟨3202943797939451978661463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4270591730585935971548617 3202943797939451978661463)
            ·
              refine ⟨4804415696909177967992195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202943797939451978661463 4804415696909177967992195)
              ·
                refine ⟨7206623545363766951988293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804415696909177967992195 7206623545363766951988293)
                ·
                  refine ⟨1351241914755706303497805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7206623545363766951988293 1351241914755706303497805)
                  ·
                    refine ⟨506715718033389863811677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351241914755706303497805 506715718033389863811677)
                    ·
                      rfl

theorem cell22_1480238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1480238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480238 prefixEnd_1480238 := by exact prefixLift 1480238
  have htrace : WordTrace (prefixWord ++ tailWord_1480238) baseStart_1480238 baseEnd_1480238 := by
    simpa [prefixWord, tailWord_1480238, baseEnd_1480238] using wordTrace_append hprefix tailTrace_1480238
  have hstable : (prefixWord ++ tailWord_1480238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480238).length < 2 ^ (prefixWord ++ tailWord_1480238).sum := by decide
  have hdescent : baseEnd_1480238 < baseStart_1480238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480266 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1480266 : Nat := 118140960795 + 1480266 * 2 ^ 59
def prefixEnd_1480266 : Nat := 4983230072969 + 3 ^ 40 * 1480266 * 2
def baseEnd_1480266 : Nat := 506725303005607124111591

theorem tailTrace_1480266 : CollatzResearch.WordTrace tailWord_1480266 prefixEnd_1480266 506725303005607124111591 := by
  unfold tailWord_1480266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497434113814141537683163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35993157636837710767155101 13497434113814141537683163)
  ·
    refine ⟨20246151170721212306524745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13497434113814141537683163 20246151170721212306524745)
    ·
      refine ⟨15184613378040909229893559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20246151170721212306524745 15184613378040909229893559)
      ·
        refine ⟨22776920067061363844840339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15184613378040909229893559 22776920067061363844840339)
        ·
          refine ⟨34165380100592045767260509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22776920067061363844840339 34165380100592045767260509)
          ·
            refine ⟨12812017537722017162722691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34165380100592045767260509 12812017537722017162722691)
            ·
              refine ⟨19218026306583025744084037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812017537722017162722691 19218026306583025744084037)
              ·
                refine ⟨3603379932484317327015757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19218026306583025744084037 3603379932484317327015757)
                ·
                  refine ⟨1351267474681618997630909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3603379932484317327015757 1351267474681618997630909)
                  ·
                    refine ⟨506725303005607124111591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351267474681618997630909 506725303005607124111591)
                    ·
                      rfl

theorem cell22_1480266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1480266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480266 prefixEnd_1480266 := by exact prefixLift 1480266
  have htrace : WordTrace (prefixWord ++ tailWord_1480266) baseStart_1480266 baseEnd_1480266 := by
    simpa [prefixWord, tailWord_1480266, baseEnd_1480266] using wordTrace_append hprefix tailTrace_1480266
  have hstable : (prefixWord ++ tailWord_1480266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480266).length < 2 ^ (prefixWord ++ tailWord_1480266).sum := by decide
  have hdescent : baseEnd_1480266 < baseStart_1480266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480279 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 7]
def baseStart_1480279 : Nat := 118140960795 + 1480279 * 2 ^ 59
def prefixEnd_1480279 : Nat := 4983230072969 + 3 ^ 40 * 1480279 * 2
def baseEnd_1480279 : Nat := 168909917723759807845517

theorem tailTrace_1480279 : CollatzResearch.WordTrace tailWord_1480279 prefixEnd_1480279 168909917723759807845517 := by
  unfold tailWord_1480279
  simp only [CollatzResearch.WordTrace]
  refine ⟨53990210604209469370955891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35993473736139646247303927 53990210604209469370955891)
  ·
    refine ⟨80985315906314204056433837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53990210604209469370955891 80985315906314204056433837)
    ·
      refine ⟨30369493464867826521162689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80985315906314204056433837 30369493464867826521162689)
      ·
        refine ⟨22777120098650869890872017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30369493464867826521162689 22777120098650869890872017)
        ·
          refine ⟨17082840073988152418154013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22777120098650869890872017 17082840073988152418154013)
          ·
            refine ⟨6406065027745557156807755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17082840073988152418154013 6406065027745557156807755)
            ·
              refine ⟨9609097541618335735211633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6406065027745557156807755 9609097541618335735211633)
              ·
                refine ⟨7206823156213751801408725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9609097541618335735211633 7206823156213751801408725)
                ·
                  refine ⟨168909917723759807845517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7206823156213751801408725 168909917723759807845517)
                  ·
                    rfl

theorem cell22_1480279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_1480279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480279 prefixEnd_1480279 := by exact prefixLift 1480279
  have htrace : WordTrace (prefixWord ++ tailWord_1480279) baseStart_1480279 baseEnd_1480279 := by
    simpa [prefixWord, tailWord_1480279, baseEnd_1480279] using wordTrace_append hprefix tailTrace_1480279
  have hstable : (prefixWord ++ tailWord_1480279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480279).length < 2 ^ (prefixWord ++ tailWord_1480279).sum := by decide
  have hdescent : baseEnd_1480279 < baseStart_1480279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480285 : List Nat := [1, 4, 4, 2, 2, 1, 8]
def baseStart_1480285 : Nat := 118140960795 + 1480285 * 2 ^ 59
def prefixEnd_1480285 : Nat := 4983230072969 + 3 ^ 40 * 1480285 * 2
def baseEnd_1480285 : Nat := 18767844707181385477279

theorem tailTrace_1480285 : CollatzResearch.WordTrace tailWord_1480285 prefixEnd_1480285 18767844707181385477279 := by
  unfold tailWord_1480285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53990429442187732395674309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35993619628125154930449539 53990429442187732395674309)
  ·
    refine ⟨10123205520410199824188933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53990429442187732395674309 10123205520410199824188933)
    ·
      refine ⟨1898101035076912467035425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10123205520410199824188933 1898101035076912467035425)
      ·
        refine ⟨1423575776307684350276569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898101035076912467035425 1423575776307684350276569)
        ·
          refine ⟨1067681832230763262707427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423575776307684350276569 1067681832230763262707427)
          ·
            refine ⟨1601522748346144894061141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067681832230763262707427 1601522748346144894061141)
            ·
              refine ⟨18767844707181385477279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1601522748346144894061141 18767844707181385477279)
              ·
                rfl

theorem cell22_1480285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 8].length) (baseStart_1480285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480285 prefixEnd_1480285 := by exact prefixLift 1480285
  have htrace : WordTrace (prefixWord ++ tailWord_1480285) baseStart_1480285 baseEnd_1480285 := by
    simpa [prefixWord, tailWord_1480285, baseEnd_1480285] using wordTrace_append hprefix tailTrace_1480285
  have hstable : (prefixWord ++ tailWord_1480285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480285).length < 2 ^ (prefixWord ++ tailWord_1480285).sum := by decide
  have hdescent : baseEnd_1480285 < baseStart_1480285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480296 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_1480296 : Nat := 118140960795 + 1480296 * 2 ^ 59
def prefixEnd_1480296 : Nat := 4983230072969 + 3 ^ 40 * 1480296 * 2
def baseEnd_1480296 : Nat := 168911857539565681953833

theorem tailTrace_1480296 : CollatzResearch.WordTrace tailWord_1480296 prefixEnd_1480296 168911857539565681953833 := by
  unfold tailWord_1480296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26995415322573940637162371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35993887096765254182883161 26995415322573940637162371)
  ·
    refine ⟨40493122983860910955743557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26995415322573940637162371 40493122983860910955743557)
    ·
      refine ⟨7592460559473920804201917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40493122983860910955743557 7592460559473920804201917)
      ·
        refine ⟨2847172709802720301575719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7592460559473920804201917 2847172709802720301575719)
        ·
          refine ⟨4270759064704080452363579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847172709802720301575719 4270759064704080452363579)
          ·
            refine ⟨6406138597056120678545369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270759064704080452363579 6406138597056120678545369)
            ·
              refine ⟨4804603947792090508909027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406138597056120678545369 4804603947792090508909027)
              ·
                refine ⟨7206905921688135763363541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804603947792090508909027 7206905921688135763363541)
                ·
                  refine ⟨168911857539565681953833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7206905921688135763363541 168911857539565681953833)
                  ·
                    rfl

theorem cell22_1480296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_1480296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480296 prefixEnd_1480296 := by exact prefixLift 1480296
  have htrace : WordTrace (prefixWord ++ tailWord_1480296) baseStart_1480296 baseEnd_1480296 := by
    simpa [prefixWord, tailWord_1480296, baseEnd_1480296] using wordTrace_append hprefix tailTrace_1480296
  have hstable : (prefixWord ++ tailWord_1480296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480296).length < 2 ^ (prefixWord ++ tailWord_1480296).sum := by decide
  have hdescent : baseEnd_1480296 < baseStart_1480296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480351 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 1, 3]
def baseStart_1480351 : Nat := 118140960795 + 1480351 * 2 ^ 59
def prefixEnd_1480351 : Nat := 4983230072969 + 3 ^ 40 * 1480351 * 2
def baseEnd_1480351 : Nat := 506754400242695235736331

theorem tailTrace_1480351 : CollatzResearch.WordTrace tailWord_1480351 prefixEnd_1480351 506754400242695235736331 := by
  unfold tailWord_1480351
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992836659948625667576907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35995224439965750445051271 53992836659948625667576907)
  ·
    refine ⟨80989254989922938501365361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53992836659948625667576907 80989254989922938501365361)
    ·
      refine ⟨60741941242442203876024021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80989254989922938501365361 60741941242442203876024021)
      ·
        refine ⟨1423639247869739153344313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 60741941242442203876024021 1423639247869739153344313)
        ·
          refine ⟨1067729435902304365008235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423639247869739153344313 1067729435902304365008235)
          ·
            refine ⟨1601594153853456547512353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067729435902304365008235 1601594153853456547512353)
            ·
              refine ⟨1201195615390092410634265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601594153853456547512353 1201195615390092410634265)
              ·
                refine ⟨900896711542569307975699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201195615390092410634265 900896711542569307975699)
                ·
                  refine ⟨1351345067313853961963549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900896711542569307975699 1351345067313853961963549)
                  ·
                    refine ⟨506754400242695235736331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351345067313853961963549 506754400242695235736331)
                    ·
                      rfl

theorem cell22_1480351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_1480351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480351 prefixEnd_1480351 := by exact prefixLift 1480351
  have htrace : WordTrace (prefixWord ++ tailWord_1480351) baseStart_1480351 baseEnd_1480351 := by
    simpa [prefixWord, tailWord_1480351, baseEnd_1480351] using wordTrace_append hprefix tailTrace_1480351
  have hstable : (prefixWord ++ tailWord_1480351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480351).length < 2 ^ (prefixWord ++ tailWord_1480351).sum := by decide
  have hdescent : baseEnd_1480351 < baseStart_1480351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480452 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1480452 : Nat := 118140960795 + 1480452 * 2 ^ 59
def prefixEnd_1480452 : Nat := 4983230072969 + 3 ^ 40 * 1480452 * 2
def baseEnd_1480452 : Nat := 506788974606764638961021

theorem tailTrace_1480452 : CollatzResearch.WordTrace tailWord_1480452 prefixEnd_1480452 506788974606764638961021 := by
  unfold tailWord_1480452
  simp only [CollatzResearch.WordTrace]
  refine ⟨26998260216291359958501805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35997680288388479944669073 26998260216291359958501805)
  ·
    refine ⟨10124347581109259984438177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26998260216291359958501805 10124347581109259984438177)
    ·
      refine ⟨7593260685831944988328633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10124347581109259984438177 7593260685831944988328633)
      ·
        refine ⟨5694945514373958741246475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7593260685831944988328633 5694945514373958741246475)
        ·
          refine ⟨8542418271560938111869713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694945514373958741246475 8542418271560938111869713)
          ·
            refine ⟨6406813703670703583902285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8542418271560938111869713 6406813703670703583902285)
            ·
              refine ⟨2402555138876513843963357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6406813703670703583902285 2402555138876513843963357)
              ·
                refine ⟨900958177078692691486259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2402555138876513843963357 900958177078692691486259)
                ·
                  refine ⟨1351437265618039037229389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900958177078692691486259 1351437265618039037229389)
                  ·
                    refine ⟨506788974606764638961021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351437265618039037229389 506788974606764638961021)
                    ·
                      rfl

theorem cell22_1480452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1480452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480452 prefixEnd_1480452 := by exact prefixLift 1480452
  have htrace : WordTrace (prefixWord ++ tailWord_1480452) baseStart_1480452 baseEnd_1480452 := by
    simpa [prefixWord, tailWord_1480452, baseEnd_1480452] using wordTrace_append hprefix tailTrace_1480452
  have hstable : (prefixWord ++ tailWord_1480452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480452).length < 2 ^ (prefixWord ++ tailWord_1480452).sum := by decide
  have hdescent : baseEnd_1480452 < baseStart_1480452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480508 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1480508 : Nat := 118140960795 + 1480508 * 2 ^ 59
def prefixEnd_1480508 : Nat := 4983230072969 + 3 ^ 40 * 1480508 * 2
def baseEnd_1480508 : Nat := 506808144551199159560849

theorem tailTrace_1480508 : CollatzResearch.WordTrace tailWord_1480508 prefixEnd_1480508 506808144551199159560849 := by
  unfold tailWord_1480508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999281460189920740521089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35999041946919894320694785 26999281460189920740521089)
  ·
    refine ⟨20249461095142440555390817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26999281460189920740521089 20249461095142440555390817)
    ·
      refine ⟨15187095821356830416543113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20249461095142440555390817 15187095821356830416543113)
      ·
        refine ⟨11390321866017622812407335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15187095821356830416543113 11390321866017622812407335)
        ·
          refine ⟨17085482799026434218611003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390321866017622812407335 17085482799026434218611003)
          ·
            refine ⟨25628224198539651327916505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17085482799026434218611003 25628224198539651327916505)
            ·
              refine ⟨19221168148904738495937379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25628224198539651327916505 19221168148904738495937379)
              ·
                refine ⟨28831752223357107743906069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19221168148904738495937379 28831752223357107743906069)
                ·
                  refine ⟨1351488385469864425495597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28831752223357107743906069 1351488385469864425495597)
                  ·
                    refine ⟨506808144551199159560849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351488385469864425495597 506808144551199159560849)
                    ·
                      rfl

theorem cell22_1480508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1480508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480508 prefixEnd_1480508 := by exact prefixLift 1480508
  have htrace : WordTrace (prefixWord ++ tailWord_1480508) baseStart_1480508 baseEnd_1480508 := by
    simpa [prefixWord, tailWord_1480508, baseEnd_1480508] using wordTrace_append hprefix tailTrace_1480508
  have hstable : (prefixWord ++ tailWord_1480508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480508).length < 2 ^ (prefixWord ++ tailWord_1480508).sum := by decide
  have hdescent : baseEnd_1480508 < baseStart_1480508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1480536 : Nat := 118140960795 + 1480536 * 2 ^ 59
def prefixEnd_1480536 : Nat := 4983230072969 + 3 ^ 40 * 1480536 * 2
def baseEnd_1480536 : Nat := 506817729523416419860763

theorem tailTrace_1480536 : CollatzResearch.WordTrace tailWord_1480536 prefixEnd_1480536 506817729523416419860763 := by
  unfold tailWord_1480536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999792082139201131530731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35999722776185601508707641 26999792082139201131530731)
  ·
    refine ⟨40499688123208801697296097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26999792082139201131530731 40499688123208801697296097)
    ·
      refine ⟨30374766092406601272972073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40499688123208801697296097 30374766092406601272972073)
      ·
        refine ⟨22781074569304950954729055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30374766092406601272972073 22781074569304950954729055)
        ·
          refine ⟨34171611853957426432093583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781074569304950954729055 34171611853957426432093583)
          ·
            refine ⟨51257417780936139648140375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34171611853957426432093583 51257417780936139648140375)
            ·
              refine ⟨76886126671404209472210563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51257417780936139648140375 76886126671404209472210563)
              ·
                refine ⟨115329190007106314208315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76886126671404209472210563 115329190007106314208315845)
                ·
                  refine ⟨21624223126332433914059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115329190007106314208315845 21624223126332433914059221)
                  ·
                    refine ⟨506817729523416419860763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21624223126332433914059221 506817729523416419860763)
                    ·
                      rfl

theorem cell22_1480536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1480536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480536 prefixEnd_1480536 := by exact prefixLift 1480536
  have htrace : WordTrace (prefixWord ++ tailWord_1480536) baseStart_1480536 baseEnd_1480536 := by
    simpa [prefixWord, tailWord_1480536, baseEnd_1480536] using wordTrace_append hprefix tailTrace_1480536
  have hstable : (prefixWord ++ tailWord_1480536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480536).length < 2 ^ (prefixWord ++ tailWord_1480536).sum := by decide
  have hdescent : baseEnd_1480536 < baseStart_1480536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480606 : List Nat := [4, 3, 1, 3, 2, 1, 2, 6]
def baseStart_1480606 : Nat := 118140960795 + 1480606 * 2 ^ 59
def prefixEnd_1480606 : Nat := 4983230072969 + 3 ^ 40 * 1480606 * 2
def baseEnd_1480606 : Nat := 56315743550439952290061

theorem tailTrace_1480606 : CollatzResearch.WordTrace tailWord_1480606 prefixEnd_1480606 56315743550439952290061 := by
  unfold tailWord_1480606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750267159253100527263709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36001424849349869478739781 6750267159253100527263709)
  ·
    refine ⟨2531350184719912697723891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6750267159253100527263709 2531350184719912697723891)
    ·
      refine ⟨3797025277079869046585837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531350184719912697723891 3797025277079869046585837)
      ·
        refine ⟨1423884478904950892469689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3797025277079869046585837 1423884478904950892469689)
        ·
          refine ⟨1067913359178713169352267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423884478904950892469689 1067913359178713169352267)
          ·
            refine ⟨1601870038768069754028401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067913359178713169352267 1601870038768069754028401)
            ·
              refine ⟨1201402529076052315521301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601870038768069754028401 1201402529076052315521301)
              ·
                refine ⟨56315743550439952290061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1201402529076052315521301 56315743550439952290061)
                ·
                  rfl

theorem cell22_1480606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_1480606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480606 prefixEnd_1480606 := by exact prefixLift 1480606
  have htrace : WordTrace (prefixWord ++ tailWord_1480606) baseStart_1480606 baseEnd_1480606 := by
    simpa [prefixWord, tailWord_1480606, baseEnd_1480606] using wordTrace_append hprefix tailTrace_1480606
  have hstable : (prefixWord ++ tailWord_1480606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480606).length < 2 ^ (prefixWord ++ tailWord_1480606).sum := by decide
  have hdescent : baseEnd_1480606 < baseStart_1480606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480613 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1480613 : Nat := 118140960795 + 1480613 * 2 ^ 59
def prefixEnd_1480613 : Nat := 4983230072969 + 3 ^ 40 * 1480613 * 2
def baseEnd_1480613 : Nat := 506844088197013885685527

theorem tailTrace_1480613 : CollatzResearch.WordTrace tailWord_1480613 prefixEnd_1480613 506844088197013885685527 := by
  unfold tailWord_1480613
  simp only [CollatzResearch.WordTrace]
  refine ⟨54002392584999444413614493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36001595056666296275742995 54002392584999444413614493)
  ·
    refine ⟨20250897219374791655105435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54002392584999444413614493 20250897219374791655105435)
    ·
      refine ⟨30376345829062187482658153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20250897219374791655105435 30376345829062187482658153)
      ·
        refine ⟨22782259371796640611993615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30376345829062187482658153 22782259371796640611993615)
        ·
          refine ⟨34173389057694960917990423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22782259371796640611993615 34173389057694960917990423)
          ·
            refine ⟨51260083586542441376985635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34173389057694960917990423 51260083586542441376985635)
            ·
              refine ⟨76890125379813662065478453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51260083586542441376985635 76890125379813662065478453)
              ·
                refine ⟨7208449254357530818638605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76890125379813662065478453 7208449254357530818638605)
                ·
                  refine ⟨2703168470384074056989477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7208449254357530818638605 2703168470384074056989477)
                  ·
                    refine ⟨506844088197013885685527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703168470384074056989477 506844088197013885685527)
                    ·
                      rfl

theorem cell22_1480613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1480613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480613 prefixEnd_1480613 := by exact prefixLift 1480613
  have htrace : WordTrace (prefixWord ++ tailWord_1480613) baseStart_1480613 baseEnd_1480613 := by
    simpa [prefixWord, tailWord_1480613, baseEnd_1480613] using wordTrace_append hprefix tailTrace_1480613
  have hstable : (prefixWord ++ tailWord_1480613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480613).length < 2 ^ (prefixWord ++ tailWord_1480613).sum := by decide
  have hdescent : baseEnd_1480613 < baseStart_1480613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480660 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1480660 : Nat := 118140960795 + 1480660 * 2 ^ 59
def prefixEnd_1480660 : Nat := 4983230072969 + 3 ^ 40 * 1480660 * 2
def baseEnd_1480660 : Nat := 506860177257521429760383

theorem tailTrace_1480660 : CollatzResearch.WordTrace tailWord_1480660 prefixEnd_1480660 506860177257521429760383 := by
  unfold tailWord_1480660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27002053407914585720287717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36002737877219447627050289 27002053407914585720287717)
  ·
    refine ⟨5062885013983984822553947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27002053407914585720287717 5062885013983984822553947)
    ·
      refine ⟨7594327520975977233830921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062885013983984822553947 7594327520975977233830921)
      ·
        refine ⟨5695745640731982925373191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7594327520975977233830921 5695745640731982925373191)
        ·
          refine ⟨8543618461097974388059787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695745640731982925373191 8543618461097974388059787)
          ·
            refine ⟨12815427691646961582089681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8543618461097974388059787 12815427691646961582089681)
            ·
              refine ⟨9611570768735221186567261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12815427691646961582089681 9611570768735221186567261)
              ·
                refine ⟨3604339038275707944962723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9611570768735221186567261 3604339038275707944962723)
                ·
                  refine ⟨5406508557413561917444085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604339038275707944962723 5406508557413561917444085)
                  ·
                    refine ⟨506860177257521429760383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5406508557413561917444085 506860177257521429760383)
                    ·
                      rfl

theorem cell22_1480660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1480660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480660 prefixEnd_1480660 := by exact prefixLift 1480660
  have htrace : WordTrace (prefixWord ++ tailWord_1480660) baseStart_1480660 baseEnd_1480660 := by
    simpa [prefixWord, tailWord_1480660, baseEnd_1480660] using wordTrace_append hprefix tailTrace_1480660
  have hstable : (prefixWord ++ tailWord_1480660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480660).length < 2 ^ (prefixWord ++ tailWord_1480660).sum := by decide
  have hdescent : baseEnd_1480660 < baseStart_1480660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480673 : List Nat := [1, 2, 3, 1, 2, 1, 4, 8]
def baseStart_1480673 : Nat := 118140960795 + 1480673 * 2 ^ 59
def prefixEnd_1480673 : Nat := 4983230072969 + 3 ^ 40 * 1480673 * 2
def baseEnd_1480673 : Nat := 56318291935910414353927

theorem tailTrace_1480673 : CollatzResearch.WordTrace tailWord_1480673 prefixEnd_1480673 56318291935910414353927 := by
  unfold tailWord_1480673
  simp only [CollatzResearch.WordTrace]
  refine ⟨54004580964782074660798673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36003053976521383107199115 54004580964782074660798673)
  ·
    refine ⟨40503435723586555995599005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54004580964782074660798673 40503435723586555995599005)
    ·
      refine ⟨15188788396344958498349627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40503435723586555995599005 15188788396344958498349627)
      ·
        refine ⟨22783182594517437747524441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15188788396344958498349627 22783182594517437747524441)
        ·
          refine ⟨17087386945888078310643331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22783182594517437747524441 17087386945888078310643331)
          ·
            refine ⟨25631080418832117465964997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17087386945888078310643331 25631080418832117465964997)
            ·
              refine ⟨4805827578531022024868437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25631080418832117465964997 4805827578531022024868437)
              ·
                refine ⟨56318291935910414353927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4805827578531022024868437 56318291935910414353927)
                ·
                  rfl

theorem cell22_1480673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 8].length) (baseStart_1480673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480673 prefixEnd_1480673 := by exact prefixLift 1480673
  have htrace : WordTrace (prefixWord ++ tailWord_1480673) baseStart_1480673 baseEnd_1480673 := by
    simpa [prefixWord, tailWord_1480673, baseEnd_1480673] using wordTrace_append hprefix tailTrace_1480673
  have hstable : (prefixWord ++ tailWord_1480673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480673).length < 2 ^ (prefixWord ++ tailWord_1480673).sum := by decide
  have hdescent : baseEnd_1480673 < baseStart_1480673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480675 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_1480675 : Nat := 118140960795 + 1480675 * 2 ^ 59
def prefixEnd_1480675 : Nat := 4983230072969 + 3 ^ 40 * 1480675 * 2
def baseEnd_1480675 : Nat := 506865312064066390635337

theorem tailTrace_1480675 : CollatzResearch.WordTrace tailWord_1480675 prefixEnd_1480675 506865312064066390635337 := by
  unfold tailWord_1480675
  simp only [CollatzResearch.WordTrace]
  refine ⟨54004653910774829002371479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36003102607183219334914319 54004653910774829002371479)
  ·
    refine ⟨81006980866162243503557219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54004653910774829002371479 81006980866162243503557219)
    ·
      refine ⟨121510471299243365255335829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81006980866162243503557219 121510471299243365255335829)
      ·
        refine ⟨5695803342152032746343867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121510471299243365255335829 5695803342152032746343867)
        ·
          refine ⟨8543705013228049119515801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695803342152032746343867 8543705013228049119515801)
          ·
            refine ⟨6407778759921036839636851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8543705013228049119515801 6407778759921036839636851)
            ·
              refine ⟨9611668139881555259455277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407778759921036839636851 9611668139881555259455277)
              ·
                refine ⟨3604375552455583222295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9611668139881555259455277 3604375552455583222295729)
                ·
                  refine ⟨2703281664341687416721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604375552455583222295729 2703281664341687416721797)
                  ·
                    refine ⟨506865312064066390635337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703281664341687416721797 506865312064066390635337)
                    ·
                      rfl

theorem cell22_1480675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_1480675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480675 prefixEnd_1480675 := by exact prefixLift 1480675
  have htrace : WordTrace (prefixWord ++ tailWord_1480675) baseStart_1480675 baseEnd_1480675 := by
    simpa [prefixWord, tailWord_1480675, baseEnd_1480675] using wordTrace_append hprefix tailTrace_1480675
  have hstable : (prefixWord ++ tailWord_1480675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480675).length < 2 ^ (prefixWord ++ tailWord_1480675).sum := by decide
  have hdescent : baseEnd_1480675 < baseStart_1480675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480739 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 1, 3]
def baseStart_1480739 : Nat := 118140960795 + 1480739 * 2 ^ 59
def prefixEnd_1480739 : Nat := 4983230072969 + 3 ^ 40 * 1480739 * 2
def baseEnd_1480739 : Nat := 506887220571991557035141

theorem tailTrace_1480739 : CollatzResearch.WordTrace tailWord_1480739 prefixEnd_1480739 506887220571991557035141 := by
  unfold tailWord_1480739
  simp only [CollatzResearch.WordTrace]
  refine ⟨54006988182542967932701271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36004658788361978621800847 54006988182542967932701271)
  ·
    refine ⟨81010482273814451899051907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54006988182542967932701271 81010482273814451899051907)
    ·
      refine ⟨121515723410721677848577861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81010482273814451899051907 121515723410721677848577861)
      ·
        refine ⟨22784198139510314596608349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121515723410721677848577861 22784198139510314596608349)
        ·
          refine ⟨8544074302316367973728131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22784198139510314596608349 8544074302316367973728131)
          ·
            refine ⟨12816111453474551960592197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544074302316367973728131 12816111453474551960592197)
            ·
              refine ⟨2403020897526478492611037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12816111453474551960592197 2403020897526478492611037)
              ·
                refine ⟨901132836572429434729139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403020897526478492611037 901132836572429434729139)
                ·
                  refine ⟨1351699254858644152093709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901132836572429434729139 1351699254858644152093709)
                  ·
                    refine ⟨506887220571991557035141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351699254858644152093709 506887220571991557035141)
                    ·
                      rfl

theorem cell22_1480739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 3].length) (baseStart_1480739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480739 prefixEnd_1480739 := by exact prefixLift 1480739
  have htrace : WordTrace (prefixWord ++ tailWord_1480739) baseStart_1480739 baseEnd_1480739 := by
    simpa [prefixWord, tailWord_1480739, baseEnd_1480739] using wordTrace_append hprefix tailTrace_1480739
  have hstable : (prefixWord ++ tailWord_1480739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480739).length < 2 ^ (prefixWord ++ tailWord_1480739).sum := by decide
  have hdescent : baseEnd_1480739 < baseStart_1480739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480752 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_1480752 : Nat := 118140960795 + 1480752 * 2 ^ 59
def prefixEnd_1480752 : Nat := 4983230072969 + 3 ^ 40 * 1480752 * 2
def baseEnd_1480752 : Nat := 168963890245887952153367

theorem tailTrace_1480752 : CollatzResearch.WordTrace tailWord_1480752 prefixEnd_1480752 168963890245887952153367 := by
  unfold tailWord_1480752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003731165747935576462255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36004974887663914101949673 27003731165747935576462255)
  ·
    refine ⟨40505596748621903364693383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003731165747935576462255 40505596748621903364693383)
    ·
      refine ⟨60758395122932855047040075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40505596748621903364693383 60758395122932855047040075)
      ·
        refine ⟨91137592684399282570560113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60758395122932855047040075 91137592684399282570560113)
        ·
          refine ⟨68353194513299461927920085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91137592684399282570560113 68353194513299461927920085)
          ·
            refine ⟨1602027996405456138935627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68353194513299461927920085 1602027996405456138935627)
            ·
              refine ⟨2403041994608184208403441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602027996405456138935627 2403041994608184208403441)
              ·
                refine ⟨1802281495956138156302581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403041994608184208403441 1802281495956138156302581)
                ·
                  refine ⟨168963890245887952153367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802281495956138156302581 168963890245887952153367)
                  ·
                    rfl

theorem cell22_1480752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_1480752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480752 prefixEnd_1480752 := by exact prefixLift 1480752
  have htrace : WordTrace (prefixWord ++ tailWord_1480752) baseStart_1480752 baseEnd_1480752 := by
    simpa [prefixWord, tailWord_1480752, baseEnd_1480752] using wordTrace_append hprefix tailTrace_1480752
  have hstable : (prefixWord ++ tailWord_1480752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480752).length < 2 ^ (prefixWord ++ tailWord_1480752).sum := by decide
  have hdescent : baseEnd_1480752 < baseStart_1480752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480756 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1480756 : Nat := 118140960795 + 1480756 * 2 ^ 59
def prefixEnd_1480756 : Nat := 4983230072969 + 3 ^ 40 * 1480756 * 2
def baseEnd_1480756 : Nat := 506893040019409179360089

theorem tailTrace_1480756 : CollatzResearch.WordTrace tailWord_1480756 prefixEnd_1480756 506893040019409179360089 := by
  unfold tailWord_1480756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003804111740689918035061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36005072148987586557380081 27003804111740689918035061)
  ·
    refine ⟨2531606635475689679815787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27003804111740689918035061 2531606635475689679815787)
    ·
      refine ⟨3797409953213534519723681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531606635475689679815787 3797409953213534519723681)
      ·
        refine ⟨2848057464910150889792761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797409953213534519723681 2848057464910150889792761)
        ·
          refine ⟨2136043098682613167344571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848057464910150889792761 2136043098682613167344571)
          ·
            refine ⟨3204064648023919751016857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136043098682613167344571 3204064648023919751016857)
            ·
              refine ⟨2403048486017939813262643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204064648023919751016857 2403048486017939813262643)
              ·
                refine ⟨3604572729026909719893965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403048486017939813262643 3604572729026909719893965)
                ·
                  refine ⟨1351714773385091144960237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3604572729026909719893965 1351714773385091144960237)
                  ·
                    refine ⟨506893040019409179360089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351714773385091144960237 506893040019409179360089)
                    ·
                      rfl

theorem cell22_1480756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1480756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480756 prefixEnd_1480756 := by exact prefixLift 1480756
  have htrace : WordTrace (prefixWord ++ tailWord_1480756) baseStart_1480756 baseEnd_1480756 := by
    simpa [prefixWord, tailWord_1480756, baseEnd_1480756] using wordTrace_append hprefix tailTrace_1480756
  have hstable : (prefixWord ++ tailWord_1480756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480756).length < 2 ^ (prefixWord ++ tailWord_1480756).sum := by decide
  have hdescent : baseEnd_1480756 < baseStart_1480756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480763 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 10]
def baseStart_1480763 : Nat := 118140960795 + 1480763 * 2 ^ 59
def prefixEnd_1480763 : Nat := 4983230072969 + 3 ^ 40 * 1480763 * 2
def baseEnd_1480763 : Nat := 168965145420821164811689

theorem tailTrace_1480763 : CollatzResearch.WordTrace tailWord_1480763 prefixEnd_1480763 168965145420821164811689 := by
  unfold tailWord_1480763
  simp only [CollatzResearch.WordTrace]
  refine ⟨54007863534456020031574943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36005242356304013354383295 54007863534456020031574943)
  ·
    refine ⟨81011795301684030047362415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54007863534456020031574943 81011795301684030047362415)
    ·
      refine ⟨121517692952526045071043623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81011795301684030047362415 121517692952526045071043623)
      ·
        refine ⟨182276539428789067606565435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121517692952526045071043623 182276539428789067606565435)
        ·
          refine ⟨273414809143183601409848153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182276539428789067606565435 273414809143183601409848153)
          ·
            refine ⟨205061106857387701057386115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273414809143183601409848153 205061106857387701057386115)
            ·
              refine ⟨307591660286081551586079173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205061106857387701057386115 307591660286081551586079173)
              ·
                refine ⟨57673436303640290922389845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307591660286081551586079173 57673436303640290922389845)
                ·
                  refine ⟨168965145420821164811689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57673436303640290922389845 168965145420821164811689)
                  ·
                    rfl

theorem cell22_1480763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_1480763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480763 prefixEnd_1480763 := by exact prefixLift 1480763
  have htrace : WordTrace (prefixWord ++ tailWord_1480763) baseStart_1480763 baseEnd_1480763 := by
    simpa [prefixWord, tailWord_1480763, baseEnd_1480763] using wordTrace_append hprefix tailTrace_1480763
  have hstable : (prefixWord ++ tailWord_1480763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480763).length < 2 ^ (prefixWord ++ tailWord_1480763).sum := by decide
  have hdescent : baseEnd_1480763 < baseStart_1480763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480769 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 5]
def baseStart_1480769 : Nat := 118140960795 + 1480769 * 2 ^ 59
def prefixEnd_1480769 : Nat := 4983230072969 + 3 ^ 40 * 1480769 * 2
def baseEnd_1480769 : Nat := 168965830061693826261683

theorem tailTrace_1480769 : CollatzResearch.WordTrace tailWord_1480769 prefixEnd_1480769 168965830061693826261683 := by
  unfold tailWord_1480769
  simp only [CollatzResearch.WordTrace]
  refine ⟨54008082372434283056293361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36005388248289522037528907 54008082372434283056293361)
  ·
    refine ⟨40506061779325712292220021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54008082372434283056293361 40506061779325712292220021)
    ·
      refine ⟨3797443291811785527395627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40506061779325712292220021 3797443291811785527395627)
      ·
        refine ⟨5696164937717678291093441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797443291811785527395627 5696164937717678291093441)
        ·
          refine ⟨4272123703288258718320081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5696164937717678291093441 4272123703288258718320081)
          ·
            refine ⟨3204092777466194038740061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272123703288258718320081 3204092777466194038740061)
            ·
              refine ⟨1201534791549822764527523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3204092777466194038740061 1201534791549822764527523)
              ·
                refine ⟨1802302187324734146791285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201534791549822764527523 1802302187324734146791285)
                ·
                  refine ⟨168965830061693826261683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802302187324734146791285 168965830061693826261683)
                  ·
                    rfl

theorem cell22_1480769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_1480769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480769 prefixEnd_1480769 := by exact prefixLift 1480769
  have htrace : WordTrace (prefixWord ++ tailWord_1480769) baseStart_1480769 baseEnd_1480769 := by
    simpa [prefixWord, tailWord_1480769, baseEnd_1480769] using wordTrace_append hprefix tailTrace_1480769
  have hstable : (prefixWord ++ tailWord_1480769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480769).length < 2 ^ (prefixWord ++ tailWord_1480769).sum := by decide
  have hdescent : baseEnd_1480769 < baseStart_1480769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480780 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1480780 : Nat := 118140960795 + 1480780 * 2 ^ 59
def prefixEnd_1480780 : Nat := 4983230072969 + 3 ^ 40 * 1480780 * 2
def baseEnd_1480780 : Nat := 168967085236627038920005

theorem tailTrace_1480780 : CollatzResearch.WordTrace tailWord_1480780 prefixEnd_1480780 168967085236627038920005 := by
  unfold tailWord_1480780
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004241787697215967471897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36005655716929621289962529 27004241787697215967471897)
  ·
    refine ⟨20253181340772911975603923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27004241787697215967471897 20253181340772911975603923)
    ·
      refine ⟨30379772011159367963405885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20253181340772911975603923 30379772011159367963405885)
      ·
        refine ⟨11392414504184762986277207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30379772011159367963405885 11392414504184762986277207)
        ·
          refine ⟨17088621756277144479415811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392414504184762986277207 17088621756277144479415811)
          ·
            refine ⟨25632932634415716719123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17088621756277144479415811 25632932634415716719123717)
            ·
              refine ⟨4806174868952946884835697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25632932634415716719123717 4806174868952946884835697)
              ·
                refine ⟨3604631151714710163626773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806174868952946884835697 3604631151714710163626773)
                ·
                  refine ⟨168967085236627038920005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3604631151714710163626773 168967085236627038920005)
                  ·
                    rfl

theorem cell22_1480780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1480780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480780 prefixEnd_1480780 := by exact prefixLift 1480780
  have htrace : WordTrace (prefixWord ++ tailWord_1480780) baseStart_1480780 baseEnd_1480780 := by
    simpa [prefixWord, tailWord_1480780, baseEnd_1480780] using wordTrace_append hprefix tailTrace_1480780
  have hstable : (prefixWord ++ tailWord_1480780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480780).length < 2 ^ (prefixWord ++ tailWord_1480780).sum := by decide
  have hdescent : baseEnd_1480780 < baseStart_1480780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480782 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1480782 : Nat := 118140960795 + 1480782 * 2 ^ 59
def prefixEnd_1480782 : Nat := 4983230072969 + 3 ^ 40 * 1480782 * 2
def baseEnd_1480782 : Nat := 506901940350753778210009

theorem tailTrace_1480782 : CollatzResearch.WordTrace tailWord_1480782 prefixEnd_1480782 506901940350753778210009 := by
  unfold tailWord_1480782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751069565173398284564575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36005704347591457517677733 6751069565173398284564575)
  ·
    refine ⟨10126604347760097426846863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6751069565173398284564575 10126604347760097426846863)
    ·
      refine ⟨15189906521640146140270295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126604347760097426846863 15189906521640146140270295)
      ·
        refine ⟨22784859782460219210405443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189906521640146140270295 22784859782460219210405443)
        ·
          refine ⟨34177289673690328815608165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22784859782460219210405443 34177289673690328815608165)
          ·
            refine ⟨6408241813816936652926531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34177289673690328815608165 6408241813816936652926531)
            ·
              refine ⟨9612362720725404979389797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408241813816936652926531 9612362720725404979389797)
              ·
                refine ⟨1802318010136013433635587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9612362720725404979389797 1802318010136013433635587)
                ·
                  refine ⟨2703477015204020150453381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802318010136013433635587 2703477015204020150453381)
                  ·
                    refine ⟨506901940350753778210009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703477015204020150453381 506901940350753778210009)
                    ·
                      rfl

theorem cell22_1480782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1480782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480782 prefixEnd_1480782 := by exact prefixLift 1480782
  have htrace : WordTrace (prefixWord ++ tailWord_1480782) baseStart_1480782 baseEnd_1480782 := by
    simpa [prefixWord, tailWord_1480782, baseEnd_1480782] using wordTrace_append hprefix tailTrace_1480782
  have hstable : (prefixWord ++ tailWord_1480782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480782).length < 2 ^ (prefixWord ++ tailWord_1480782).sum := by decide
  have hdescent : baseEnd_1480782 < baseStart_1480782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480790 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1480790 : Nat := 118140960795 + 1480790 * 2 ^ 59
def prefixEnd_1480790 : Nat := 4983230072969 + 3 ^ 40 * 1480790 * 2
def baseEnd_1480790 : Nat := 506904678914244424009985

theorem tailTrace_1480790 : CollatzResearch.WordTrace tailWord_1480790 prefixEnd_1480790 506904678914244424009985 := by
  unfold tailWord_1480790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375553019084887727675489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36005898870238802428538549 3375553019084887727675489)
  ·
    refine ⟨2531664764313665795756617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375553019084887727675489 2531664764313665795756617)
    ·
      refine ⟨1898748573235249346817463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531664764313665795756617 1898748573235249346817463)
      ·
        refine ⟨2848122859852874020226195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898748573235249346817463 2848122859852874020226195)
        ·
          refine ⟨4272184289779311030339293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848122859852874020226195 4272184289779311030339293)
          ·
            refine ⟨1602069108667241636377235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4272184289779311030339293 1602069108667241636377235)
            ·
              refine ⟨2403103663000862454565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602069108667241636377235 2403103663000862454565853)
              ·
                refine ⟨901163873625323420462195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403103663000862454565853 901163873625323420462195)
                ·
                  refine ⟨1351745810437985130693293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901163873625323420462195 1351745810437985130693293)
                  ·
                    refine ⟨506904678914244424009985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351745810437985130693293 506904678914244424009985)
                    ·
                      rfl

theorem cell22_1480790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1480790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480790 prefixEnd_1480790 := by exact prefixLift 1480790
  have htrace : WordTrace (prefixWord ++ tailWord_1480790) baseStart_1480790 baseEnd_1480790 := by
    simpa [prefixWord, tailWord_1480790, baseEnd_1480790] using wordTrace_append hprefix tailTrace_1480790
  have hstable : (prefixWord ++ tailWord_1480790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480790).length < 2 ^ (prefixWord ++ tailWord_1480790).sum := by decide
  have hdescent : baseEnd_1480790 < baseStart_1480790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480812 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1480812 : Nat := 118140960795 + 1480812 * 2 ^ 59
def prefixEnd_1480812 : Nat := 4983230072969 + 3 ^ 40 * 1480812 * 2
def baseEnd_1480812 : Nat := 506912209963843699959917

theorem tailTrace_1480812 : CollatzResearch.WordTrace tailWord_1480812 prefixEnd_1480812 506912209963843699959917 := by
  unfold tailWord_1480812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004825355639250700054345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36006433807519000933405793 27004825355639250700054345)
  ·
    refine ⟨20253619016729438025040759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27004825355639250700054345 20253619016729438025040759)
    ·
      refine ⟨30380428525094157037561139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20253619016729438025040759 30380428525094157037561139)
      ·
        refine ⟨45570642787641235556341709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30380428525094157037561139 45570642787641235556341709)
        ·
          refine ⟨17088991045365463333628141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45570642787641235556341709 17088991045365463333628141)
          ·
            refine ⟨6408371642012048750110553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17088991045365463333628141 6408371642012048750110553)
            ·
              refine ⟨4806278731509036562582915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408371642012048750110553 4806278731509036562582915)
              ·
                refine ⟨7209418097263554843874373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806278731509036562582915 7209418097263554843874373)
                ·
                  refine ⟨1351765893236916533226445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7209418097263554843874373 1351765893236916533226445)
                  ·
                    refine ⟨506912209963843699959917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351765893236916533226445 506912209963843699959917)
                    ·
                      rfl

theorem cell22_1480812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1480812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480812 prefixEnd_1480812 := by exact prefixLift 1480812
  have htrace : WordTrace (prefixWord ++ tailWord_1480812) baseStart_1480812 baseEnd_1480812 := by
    simpa [prefixWord, tailWord_1480812, baseEnd_1480812] using wordTrace_append hprefix tailTrace_1480812
  have hstable : (prefixWord ++ tailWord_1480812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480812).length < 2 ^ (prefixWord ++ tailWord_1480812).sum := by decide
  have hdescent : baseEnd_1480812 < baseStart_1480812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480825 : List Nat := [1, 2, 1, 3, 4, 1, 1, 9]
def baseStart_1480825 : Nat := 118140960795 + 1480825 * 2 ^ 59
def prefixEnd_1480825 : Nat := 4983230072969 + 3 ^ 40 * 1480825 * 2
def baseEnd_1480825 : Nat := 56324073347723999931653

theorem tailTrace_1480825 : CollatzResearch.WordTrace tailWord_1480825 prefixEnd_1480825 56324073347723999931653 := by
  unfold tailWord_1480825
  simp only [CollatzResearch.WordTrace]
  refine ⟨54010124860231404620331929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36006749906820936413554619 54010124860231404620331929)
  ·
    refine ⟨40507593645173553465248947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54010124860231404620331929 40507593645173553465248947)
    ·
      refine ⟨60761390467760330197873421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40507593645173553465248947 60761390467760330197873421)
      ·
        refine ⟨22785521425410123824202533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60761390467760330197873421 22785521425410123824202533)
        ·
          refine ⟨4272285267264398217037975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22785521425410123824202533 4272285267264398217037975)
          ·
            refine ⟨6408427900896597325556963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272285267264398217037975 6408427900896597325556963)
            ·
              refine ⟨9612641851344895988335445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408427900896597325556963 9612641851344895988335445)
              ·
                refine ⟨56324073347723999931653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9612641851344895988335445 56324073347723999931653)
                ·
                  rfl

theorem cell22_1480825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 9].length) (baseStart_1480825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480825 prefixEnd_1480825 := by exact prefixLift 1480825
  have htrace : WordTrace (prefixWord ++ tailWord_1480825) baseStart_1480825 baseEnd_1480825 := by
    simpa [prefixWord, tailWord_1480825, baseEnd_1480825] using wordTrace_append hprefix tailTrace_1480825
  have hstable : (prefixWord ++ tailWord_1480825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480825).length < 2 ^ (prefixWord ++ tailWord_1480825).sum := by decide
  have hdescent : baseEnd_1480825 < baseStart_1480825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480829 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_1480829 : Nat := 118140960795 + 1480829 * 2 ^ 59
def prefixEnd_1480829 : Nat := 4983230072969 + 3 ^ 40 * 1480829 * 2
def baseEnd_1480829 : Nat := 506918029411261322284865

theorem tailTrace_1480829 : CollatzResearch.WordTrace tailWord_1480829 prefixEnd_1480829 506918029411261322284865 := by
  unfold tailWord_1480829
  simp only [CollatzResearch.WordTrace]
  refine ⟨54010270752216913303477541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36006847168144608868985027 54010270752216913303477541)
  ·
    refine ⟨10126925766040671244402039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54010270752216913303477541 10126925766040671244402039)
    ·
      refine ⟨15190388649061006866603059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126925766040671244402039 15190388649061006866603059)
      ·
        refine ⟨22785582973591510299904589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190388649061006866603059 22785582973591510299904589)
        ·
          refine ⟨8544593615096816362464221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22785582973591510299904589 8544593615096816362464221)
          ·
            refine ⟨3204222605661306135924083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8544593615096816362464221 3204222605661306135924083)
            ·
              refine ⟨4806333908491959203886125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204222605661306135924083 4806333908491959203886125)
              ·
                refine ⟨1802375215684484701457297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806333908491959203886125 1802375215684484701457297)
                ·
                  refine ⟨1351781411763363526092973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1802375215684484701457297 1351781411763363526092973)
                  ·
                    refine ⟨506918029411261322284865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351781411763363526092973 506918029411261322284865)
                    ·
                      rfl

theorem cell22_1480829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_1480829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480829 prefixEnd_1480829 := by exact prefixLift 1480829
  have htrace : WordTrace (prefixWord ++ tailWord_1480829) baseStart_1480829 baseEnd_1480829 := by
    simpa [prefixWord, tailWord_1480829, baseEnd_1480829] using wordTrace_append hprefix tailTrace_1480829
  have hstable : (prefixWord ++ tailWord_1480829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480829).length < 2 ^ (prefixWord ++ tailWord_1480829).sum := by decide
  have hdescent : baseEnd_1480829 < baseStart_1480829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480887 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 5]
def baseStart_1480887 : Nat := 118140960795 + 1480887 * 2 ^ 59
def prefixEnd_1480887 : Nat := 4983230072969 + 3 ^ 40 * 1480887 * 2
def baseEnd_1480887 : Nat := 168979294665522834778229

theorem tailTrace_1480887 : CollatzResearch.WordTrace tailWord_1480887 prefixEnd_1480887 168979294665522834778229 := by
  unfold tailWord_1480887
  simp only [CollatzResearch.WordTrace]
  refine ⟨54012386186006789209088915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36008257457337859472725943 54012386186006789209088915)
  ·
    refine ⟨81018579279010183813633373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54012386186006789209088915 81018579279010183813633373)
    ·
      refine ⟨30381967229628818930112515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81018579279010183813633373 30381967229628818930112515)
      ·
        refine ⟨45572950844443228395168773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30381967229628818930112515 45572950844443228395168773)
        ·
          refine ⟨8544928283333105324094145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45572950844443228395168773 8544928283333105324094145)
          ·
            refine ⟨6408696212499828993070609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8544928283333105324094145 6408696212499828993070609)
            ·
              refine ⟨4806522159374871744802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408696212499828993070609 4806522159374871744802957)
              ·
                refine ⟨1802445809765576904301109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806522159374871744802957 1802445809765576904301109)
                ·
                  refine ⟨168979294665522834778229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802445809765576904301109 168979294665522834778229)
                  ·
                    rfl

theorem cell22_1480887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].length) (baseStart_1480887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480887 prefixEnd_1480887 := by exact prefixLift 1480887
  have htrace : WordTrace (prefixWord ++ tailWord_1480887) baseStart_1480887 baseEnd_1480887 := by
    simpa [prefixWord, tailWord_1480887, baseEnd_1480887] using wordTrace_append hprefix tailTrace_1480887
  have hstable : (prefixWord ++ tailWord_1480887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480887).length < 2 ^ (prefixWord ++ tailWord_1480887).sum := by decide
  have hdescent : baseEnd_1480887 < baseStart_1480887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480977 : List Nat := [1, 2, 2, 1, 1, 7, 8]
def baseStart_1480977 : Nat := 118140960795 + 1480977 * 2 ^ 59
def prefixEnd_1480977 : Nat := 4983230072969 + 3 ^ 40 * 1480977 * 2
def baseEnd_1480977 : Nat := 18776618253179195169793

theorem tailTrace_1480977 : CollatzResearch.WordTrace tailWord_1480977 prefixEnd_1480977 18776618253179195169793 := by
  unfold tailWord_1480977
  simp only [CollatzResearch.WordTrace]
  refine ⟨54015668755680734579865185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36010445837120489719910123 54015668755680734579865185)
  ·
    refine ⟨40511751566760550934898889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54015668755680734579865185 40511751566760550934898889)
    ·
      refine ⟨30383813675070413201174167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40511751566760550934898889 30383813675070413201174167)
      ·
        refine ⟨45575720512605619801761251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30383813675070413201174167 45575720512605619801761251)
        ·
          refine ⟨68363580768908429702641877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45575720512605619801761251 68363580768908429702641877)
          ·
            refine ⟨1602271424271291321155669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68363580768908429702641877 1602271424271291321155669)
            ·
              refine ⟨18776618253179195169793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1602271424271291321155669 18776618253179195169793)
              ·
                rfl

theorem cell22_1480977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 8].length) (baseStart_1480977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480977 prefixEnd_1480977 := by exact prefixLift 1480977
  have htrace : WordTrace (prefixWord ++ tailWord_1480977) baseStart_1480977 baseEnd_1480977 := by
    simpa [prefixWord, tailWord_1480977, baseEnd_1480977] using wordTrace_append hprefix tailTrace_1480977
  have hstable : (prefixWord ++ tailWord_1480977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480977).length < 2 ^ (prefixWord ++ tailWord_1480977).sum := by decide
  have hdescent : baseEnd_1480977 < baseStart_1480977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480994 : List Nat := [3, 3, 1, 1, 3, 2, 2, 7]
def baseStart_1480994 : Nat := 118140960795 + 1480994 * 2 ^ 59
def prefixEnd_1480994 : Nat := 4983230072969 + 3 ^ 40 * 1480994 * 2
def baseEnd_1480994 : Nat := 56330501364806210212151

theorem tailTrace_1480994 : CollatzResearch.WordTrace tailWord_1480994 prefixEnd_1480994 56330501364806210212151 := by
  unfold tailWord_1480994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504072199154786620808509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36010859197746097655489357 13504072199154786620808509)
  ·
    refine ⟨5064027074683044982803191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13504072199154786620808509 5064027074683044982803191)
    ·
      refine ⟨7596040612024567474204787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064027074683044982803191 7596040612024567474204787)
      ·
        refine ⟨11394060918036851211307181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596040612024567474204787 11394060918036851211307181)
        ·
          refine ⟨4272772844263819204240193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11394060918036851211307181 4272772844263819204240193)
          ·
            refine ⟨3204579633197864403180145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272772844263819204240193 3204579633197864403180145)
            ·
              refine ⟨2403434724898398302385109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204579633197864403180145 2403434724898398302385109)
              ·
                refine ⟨56330501364806210212151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2403434724898398302385109 56330501364806210212151)
                ·
                  rfl

theorem cell22_1480994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_1480994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1480994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1480994 prefixEnd_1480994 := by exact prefixLift 1480994
  have htrace : WordTrace (prefixWord ++ tailWord_1480994) baseStart_1480994 baseEnd_1480994 := by
    simpa [prefixWord, tailWord_1480994, baseEnd_1480994] using wordTrace_append hprefix tailTrace_1480994
  have hstable : (prefixWord ++ tailWord_1480994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480994).length < 2 ^ (prefixWord ++ tailWord_1480994).sum := by decide
  have hdescent : baseEnd_1480994 < baseStart_1480994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481067 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 6]
def baseStart_1481067 : Nat := 118140960795 + 1481067 * 2 ^ 59
def prefixEnd_1481067 : Nat := 4983230072969 + 3 ^ 40 * 1481067 * 2
def baseEnd_1481067 : Nat := 168999833891702678278045

theorem tailTrace_1481067 : CollatzResearch.WordTrace tailWord_1481067 prefixEnd_1481067 168999833891702678278045 := by
  unfold tailWord_1481067
  simp only [CollatzResearch.WordTrace]
  refine ⟨54018951325354679950641455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36012634216903119967094303 54018951325354679950641455)
  ·
    refine ⟨81028426988032019925962183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54018951325354679950641455 81028426988032019925962183)
    ·
      refine ⟨121542640482048029888943275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81028426988032019925962183 121542640482048029888943275)
      ·
        refine ⟨182313960723072044833414913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121542640482048029888943275 182313960723072044833414913)
        ·
          refine ⟨136735470542304033625061185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182313960723072044833414913 136735470542304033625061185)
          ·
            refine ⟨102551602906728025218795889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136735470542304033625061185 102551602906728025218795889)
            ·
              refine ⟨76913702180046018914096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102551602906728025218795889 76913702180046018914096917)
              ·
                refine ⟨3605329789689657136598293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76913702180046018914096917 3605329789689657136598293)
                ·
                  refine ⟨168999833891702678278045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3605329789689657136598293 168999833891702678278045)
                  ·
                    rfl

theorem cell22_1481067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_1481067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481067 prefixEnd_1481067 := by exact prefixLift 1481067
  have htrace : WordTrace (prefixWord ++ tailWord_1481067) baseStart_1481067 baseEnd_1481067 := by
    simpa [prefixWord, tailWord_1481067, baseEnd_1481067] using wordTrace_append hprefix tailTrace_1481067
  have hstable : (prefixWord ++ tailWord_1481067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481067).length < 2 ^ (prefixWord ++ tailWord_1481067).sum := by decide
  have hdescent : baseEnd_1481067 < baseStart_1481067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481069 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1481069 : Nat := 118140960795 + 1481069 * 2 ^ 59
def prefixEnd_1481069 : Nat := 4983230072969 + 3 ^ 40 * 1481069 * 2
def baseEnd_1481069 : Nat := 507000186315980696284129

theorem tailTrace_1481069 : CollatzResearch.WordTrace tailWord_1481069 prefixEnd_1481069 507000186315980696284129 := by
  unfold tailWord_1481069
  simp only [CollatzResearch.WordTrace]
  refine ⟨54019024271347434292214261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36012682847564956194809507 54019024271347434292214261)
  ·
    refine ⟨5064283525438821964895087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54019024271347434292214261 5064283525438821964895087)
    ·
      refine ⟨7596425288158232947342631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064283525438821964895087 7596425288158232947342631)
      ·
        refine ⟨11394637932237349421013947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596425288158232947342631 11394637932237349421013947)
        ·
          refine ⟨17091956898356024131520921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394637932237349421013947 17091956898356024131520921)
          ·
            refine ⟨12818967673767018098640691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17091956898356024131520921 12818967673767018098640691)
            ·
              refine ⟨19228451510650527147961037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818967673767018098640691 19228451510650527147961037)
              ·
                refine ⟨7210669316493947680485389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19228451510650527147961037 7210669316493947680485389)
                ·
                  refine ⟨2704000993685230380182021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7210669316493947680485389 2704000993685230380182021)
                  ·
                    refine ⟨507000186315980696284129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704000993685230380182021 507000186315980696284129)
                    ·
                      rfl

theorem cell22_1481069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1481069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481069 prefixEnd_1481069 := by exact prefixLift 1481069
  have htrace : WordTrace (prefixWord ++ tailWord_1481069) baseStart_1481069 baseEnd_1481069 := by
    simpa [prefixWord, tailWord_1481069, baseEnd_1481069] using wordTrace_append hprefix tailTrace_1481069
  have hstable : (prefixWord ++ tailWord_1481069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481069).length < 2 ^ (prefixWord ++ tailWord_1481069).sum := by decide
  have hdescent : baseEnd_1481069 < baseStart_1481069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481090 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1481090 : Nat := 118140960795 + 1481090 * 2 ^ 59
def prefixEnd_1481090 : Nat := 4983230072969 + 3 ^ 40 * 1481090 * 2
def baseEnd_1481090 : Nat := 169002458348381213836355

theorem tailTrace_1481090 : CollatzResearch.WordTrace tailWord_1481090 prefixEnd_1481090 169002458348381213836355 := by
  unfold tailWord_1481090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504947551067838719682181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36013193469514236585819149 13504947551067838719682181)
  ·
    refine ⟨2532177665825219759940409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13504947551067838719682181 2532177665825219759940409)
    ·
      refine ⟨1899133249368914819955307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532177665825219759940409 1899133249368914819955307)
      ·
        refine ⟨2848699874053372229932961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899133249368914819955307 2848699874053372229932961)
        ·
          refine ⟨2136524905540029172449721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848699874053372229932961 2136524905540029172449721)
          ·
            refine ⟨1602393679155021879337291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136524905540029172449721 1602393679155021879337291)
            ·
              refine ⟨2403590518732532819005937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602393679155021879337291 2403590518732532819005937)
              ·
                refine ⟨1802692889049399614254453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403590518732532819005937 1802692889049399614254453)
                ·
                  refine ⟨169002458348381213836355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802692889049399614254453 169002458348381213836355)
                  ·
                    rfl

theorem cell22_1481090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1481090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481090 prefixEnd_1481090 := by exact prefixLift 1481090
  have htrace : WordTrace (prefixWord ++ tailWord_1481090) baseStart_1481090 baseEnd_1481090 := by
    simpa [prefixWord, tailWord_1481090, baseEnd_1481090] using wordTrace_append hprefix tailTrace_1481090
  have hstable : (prefixWord ++ tailWord_1481090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481090).length < 2 ^ (prefixWord ++ tailWord_1481090).sum := by decide
  have hdescent : baseEnd_1481090 < baseStart_1481090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481114 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1481114 : Nat := 118140960795 + 1481114 * 2 ^ 59
def prefixEnd_1481114 : Nat := 4983230072969 + 3 ^ 40 * 1481114 * 2
def baseEnd_1481114 : Nat := 507015590735615578908991

theorem tailTrace_1481114 : CollatzResearch.WordTrace tailWord_1481114 prefixEnd_1481114 507015590735615578908991 := by
  unfold tailWord_1481114
  simp only [CollatzResearch.WordTrace]
  refine ⟨13505166389046101744400599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36013777037456271318401597 13505166389046101744400599)
  ·
    refine ⟨20257749583569152616600899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13505166389046101744400599 20257749583569152616600899)
    ·
      refine ⟨30386624375353728924901349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20257749583569152616600899 30386624375353728924901349)
      ·
        refine ⟨5697492070378824173419003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30386624375353728924901349 5697492070378824173419003)
        ·
          refine ⟨8546238105568236260128505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697492070378824173419003 8546238105568236260128505)
          ·
            refine ⟨6409678579176177195096379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8546238105568236260128505 6409678579176177195096379)
            ·
              refine ⟨9614517868764265792644569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409678579176177195096379 9614517868764265792644569)
              ·
                refine ⟨7210888401573199344483427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9614517868764265792644569 7210888401573199344483427)
                ·
                  refine ⟨10816332602359799016725141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210888401573199344483427 10816332602359799016725141)
                  ·
                    refine ⟨507015590735615578908991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10816332602359799016725141 507015590735615578908991)
                    ·
                      rfl

theorem cell22_1481114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1481114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481114 prefixEnd_1481114 := by exact prefixLift 1481114
  have htrace : WordTrace (prefixWord ++ tailWord_1481114) baseStart_1481114 baseEnd_1481114 := by
    simpa [prefixWord, tailWord_1481114, baseEnd_1481114] using wordTrace_append hprefix tailTrace_1481114
  have hstable : (prefixWord ++ tailWord_1481114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481114).length < 2 ^ (prefixWord ++ tailWord_1481114).sum := by decide
  have hdescent : baseEnd_1481114 < baseStart_1481114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481161 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_1481161 : Nat := 118140960795 + 1481161 * 2 ^ 59
def prefixEnd_1481161 : Nat := 4983230072969 + 3 ^ 40 * 1481161 * 2
def baseEnd_1481161 : Nat := 507031679796123122983847

theorem tailTrace_1481161 : CollatzResearch.WordTrace tailWord_1481161 prefixEnd_1481161 507031679796123122983847 := by
  unfold tailWord_1481161
  simp only [CollatzResearch.WordTrace]
  refine ⟨54022379787014134004563337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36014919858009422669708891 54022379787014134004563337)
  ·
    refine ⟨40516784840260600503422503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54022379787014134004563337 40516784840260600503422503)
    ·
      refine ⟨60775177260390900755133755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40516784840260600503422503 60775177260390900755133755)
      ·
        refine ⟨91162765890586351132700633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60775177260390900755133755 91162765890586351132700633)
        ·
          refine ⟨68372074417939763349525475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91162765890586351132700633 68372074417939763349525475)
          ·
            refine ⟨102558111626909645024288213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68372074417939763349525475 102558111626909645024288213)
            ·
              refine ⟨2403705741255694805256755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102558111626909645024288213 2403705741255694805256755)
              ·
                refine ⟨3605558611883542207885133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403705741255694805256755 3605558611883542207885133)
                ·
                  refine ⟨1352084479456328327956925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605558611883542207885133 1352084479456328327956925)
                  ·
                    refine ⟨507031679796123122983847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352084479456328327956925 507031679796123122983847)
                    ·
                      rfl

theorem cell22_1481161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_1481161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481161 prefixEnd_1481161 := by exact prefixLift 1481161
  have htrace : WordTrace (prefixWord ++ tailWord_1481161) baseStart_1481161 baseEnd_1481161 := by
    simpa [prefixWord, tailWord_1481161, baseEnd_1481161] using wordTrace_append hprefix tailTrace_1481161
  have hstable : (prefixWord ++ tailWord_1481161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481161).length < 2 ^ (prefixWord ++ tailWord_1481161).sum := by decide
  have hdescent : baseEnd_1481161 < baseStart_1481161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481206 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1481206 : Nat := 118140960795 + 1481206 * 2 ^ 59
def prefixEnd_1481206 : Nat := 4983230072969 + 3 ^ 40 * 1481206 * 2
def baseEnd_1481206 : Nat := 507047084215758005608709

theorem tailTrace_1481206 : CollatzResearch.WordTrace tailWord_1481206 prefixEnd_1481206 507047084215758005608709 := by
  unfold tailWord_1481206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376501316990694168121967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36016014047900737793300981 3376501316990694168121967)
  ·
    refine ⟨5064751975486041252182951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376501316990694168121967 5064751975486041252182951)
    ·
      refine ⟨7597127963229061878274427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064751975486041252182951 7597127963229061878274427)
      ·
        refine ⟨11395691944843592817411641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597127963229061878274427 11395691944843592817411641)
        ·
          refine ⟨8546768958632694613058731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11395691944843592817411641 8546768958632694613058731)
          ·
            refine ⟨12820153437949041919588097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546768958632694613058731 12820153437949041919588097)
            ·
              refine ⟨9615115078461781439691073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12820153437949041919588097 9615115078461781439691073)
              ·
                refine ⟨7211336308846336079768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9615115078461781439691073 7211336308846336079768305)
                ·
                  refine ⟨5408502231634752059826229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7211336308846336079768305 5408502231634752059826229)
                  ·
                    refine ⟨507047084215758005608709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5408502231634752059826229 507047084215758005608709)
                    ·
                      rfl

theorem cell22_1481206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1481206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481206 prefixEnd_1481206 := by exact prefixLift 1481206
  have htrace : WordTrace (prefixWord ++ tailWord_1481206) baseStart_1481206 baseEnd_1481206 := by
    simpa [prefixWord, tailWord_1481206, baseEnd_1481206] using wordTrace_append hprefix tailTrace_1481206
  have hstable : (prefixWord ++ tailWord_1481206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481206).length < 2 ^ (prefixWord ++ tailWord_1481206).sum := by decide
  have hdescent : baseEnd_1481206 < baseStart_1481206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481219 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 6]
def baseStart_1481219 : Nat := 118140960795 + 1481219 * 2 ^ 59
def prefixEnd_1481219 : Nat := 4983230072969 + 3 ^ 40 * 1481219 * 2
def baseEnd_1481219 : Nat := 169017178127143435011223

theorem tailTrace_1481219 : CollatzResearch.WordTrace tailWord_1481219 prefixEnd_1481219 169017178127143435011223 := by
  unfold tailWord_1481219
  simp only [CollatzResearch.WordTrace]
  refine ⟨54024495220804009910174711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36016330147202673273449807 54024495220804009910174711)
  ·
    refine ⟨81036742831206014865262067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54024495220804009910174711 81036742831206014865262067)
    ·
      refine ⟨121555114246809022297893101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81036742831206014865262067 121555114246809022297893101)
      ·
        refine ⟨45583167842553383361709913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121555114246809022297893101 45583167842553383361709913)
        ·
          refine ⟨34187375881915037521282435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45583167842553383361709913 34187375881915037521282435)
          ·
            refine ⟨51281063822872556281923653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34187375881915037521282435 51281063822872556281923653)
            ·
              refine ⟨9615199466788604302860685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51281063822872556281923653 9615199466788604302860685)
              ·
                refine ⟨3605699800045726613572757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9615199466788604302860685 3605699800045726613572757)
                ·
                  refine ⟨169017178127143435011223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3605699800045726613572757 169017178127143435011223)
                  ·
                    rfl

theorem cell22_1481219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_1481219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481219 prefixEnd_1481219 := by exact prefixLift 1481219
  have htrace : WordTrace (prefixWord ++ tailWord_1481219) baseStart_1481219 baseEnd_1481219 := by
    simpa [prefixWord, tailWord_1481219, baseEnd_1481219] using wordTrace_append hprefix tailTrace_1481219
  have hstable : (prefixWord ++ tailWord_1481219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481219).length < 2 ^ (prefixWord ++ tailWord_1481219).sum := by decide
  have hdescent : baseEnd_1481219 < baseStart_1481219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481251 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_1481251 : Nat := 118140960795 + 1481251 * 2 ^ 59
def prefixEnd_1481251 : Nat := 4983230072969 + 3 ^ 40 * 1481251 * 2
def baseEnd_1481251 : Nat := 507062488635392888233571

theorem tailTrace_1481251 : CollatzResearch.WordTrace tailWord_1481251 prefixEnd_1481251 507062488635392888233571 := by
  unfold tailWord_1481251
  simp only [CollatzResearch.WordTrace]
  refine ⟨54025662356688079375339607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36017108237792052916893071 54025662356688079375339607)
  ·
    refine ⟨81038493535032119063009411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54025662356688079375339607 81038493535032119063009411)
    ·
      refine ⟨121557740302548178594514117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81038493535032119063009411 121557740302548178594514117)
      ·
        refine ⟨22792076306727783486471397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121557740302548178594514117 22792076306727783486471397)
        ·
          refine ⟨4273514307511459403713387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22792076306727783486471397 4273514307511459403713387)
          ·
            refine ⟨6410271461267189105570081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273514307511459403713387 6410271461267189105570081)
            ·
              refine ⟨4807703595950391829177561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6410271461267189105570081 4807703595950391829177561)
              ·
                refine ⟨3605777696962793871883171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807703595950391829177561 3605777696962793871883171)
                ·
                  refine ⟨5408666545444190807824757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605777696962793871883171 5408666545444190807824757)
                  ·
                    refine ⟨507062488635392888233571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5408666545444190807824757 507062488635392888233571)
                    ·
                      rfl

theorem cell22_1481251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_1481251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481251 prefixEnd_1481251 := by exact prefixLift 1481251
  have htrace : WordTrace (prefixWord ++ tailWord_1481251) baseStart_1481251 baseEnd_1481251 := by
    simpa [prefixWord, tailWord_1481251, baseEnd_1481251] using wordTrace_append hprefix tailTrace_1481251
  have hstable : (prefixWord ++ tailWord_1481251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481251).length < 2 ^ (prefixWord ++ tailWord_1481251).sum := by decide
  have hdescent : baseEnd_1481251 < baseStart_1481251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481266 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1481266 : Nat := 118140960795 + 1481266 * 2 ^ 59
def prefixEnd_1481266 : Nat := 4983230072969 + 3 ^ 40 * 1481266 * 2
def baseEnd_1481266 : Nat := 507067623441937849108525

theorem tailTrace_1481266 : CollatzResearch.WordTrace tailWord_1481266 prefixEnd_1481266 507067623441937849108525 := by
  unfold tailWord_1481266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506552362908434234283913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36017472967755824624757101 13506552362908434234283913)
  ·
    refine ⟨10129914272181325675712935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13506552362908434234283913 10129914272181325675712935)
    ·
      refine ⟨15194871408271988513569403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10129914272181325675712935 15194871408271988513569403)
      ·
        refine ⟨22792307112407982770354105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15194871408271988513569403 22792307112407982770354105)
        ·
          refine ⟨17094230334305987077765579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22792307112407982770354105 17094230334305987077765579)
          ·
            refine ⟨25641345501458980616648369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094230334305987077765579 25641345501458980616648369)
            ·
              refine ⟨19231009126094235462486277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25641345501458980616648369 19231009126094235462486277)
              ·
                refine ⟨3605814211142669149216177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19231009126094235462486277 3605814211142669149216177)
                ·
                  refine ⟨2704360658357001861912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605814211142669149216177 2704360658357001861912133)
                  ·
                    refine ⟨507067623441937849108525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704360658357001861912133 507067623441937849108525)
                    ·
                      rfl

theorem cell22_1481266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1481266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481266 prefixEnd_1481266 := by exact prefixLift 1481266
  have htrace : WordTrace (prefixWord ++ tailWord_1481266) baseStart_1481266 baseEnd_1481266 := by
    simpa [prefixWord, tailWord_1481266, baseEnd_1481266] using wordTrace_append hprefix tailTrace_1481266
  have hstable : (prefixWord ++ tailWord_1481266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481266).length < 2 ^ (prefixWord ++ tailWord_1481266).sum := by decide
  have hdescent : baseEnd_1481266 < baseStart_1481266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481270 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1481270 : Nat := 118140960795 + 1481270 * 2 ^ 59
def prefixEnd_1481270 : Nat := 4983230072969 + 3 ^ 40 * 1481270 * 2
def baseEnd_1481270 : Nat := 169022997574561057336171

theorem tailTrace_1481270 : CollatzResearch.WordTrace tailWord_1481270 prefixEnd_1481270 169022997574561057336171 := by
  unfold tailWord_1481270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376647208976202851267579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36017570229079497080187509 3376647208976202851267579)
  ·
    refine ⟨5064970813464304276901369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376647208976202851267579 5064970813464304276901369)
    ·
      refine ⟨3798728110098228207676027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064970813464304276901369 3798728110098228207676027)
      ·
        refine ⟨5698092165147342311514041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798728110098228207676027 5698092165147342311514041)
        ·
          refine ⟨4273569123860506733635531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5698092165147342311514041 4273569123860506733635531)
          ·
            refine ⟨6410353685790760100453297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273569123860506733635531 6410353685790760100453297)
            ·
              refine ⟨4807765264343070075339973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6410353685790760100453297 4807765264343070075339973)
              ·
                refine ⟨901455987064325639126245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4807765264343070075339973 901455987064325639126245)
                ·
                  refine ⟨169022997574561057336171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901455987064325639126245 169022997574561057336171)
                  ·
                    rfl

theorem cell22_1481270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1481270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481270 prefixEnd_1481270 := by exact prefixLift 1481270
  have htrace : WordTrace (prefixWord ++ tailWord_1481270) baseStart_1481270 baseEnd_1481270 := by
    simpa [prefixWord, tailWord_1481270, baseEnd_1481270] using wordTrace_append hprefix tailTrace_1481270
  have hstable : (prefixWord ++ tailWord_1481270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481270).length < 2 ^ (prefixWord ++ tailWord_1481270).sum := by decide
  have hdescent : baseEnd_1481270 < baseStart_1481270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481285 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_1481285 : Nat := 118140960795 + 1481285 * 2 ^ 59
def prefixEnd_1481285 : Nat := 4983230072969 + 3 ^ 40 * 1481285 * 2
def baseEnd_1481285 : Nat := 507074127530228132883467

theorem tailTrace_1481285 : CollatzResearch.WordTrace tailWord_1481285 prefixEnd_1481285 507074127530228132883467 := by
  unfold tailWord_1481285
  simp only [CollatzResearch.WordTrace]
  refine ⟨54026902438564903182077309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36017934959043268788051539 54026902438564903182077309)
  ·
    refine ⟨20260088414461838693278991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54026902438564903182077309 20260088414461838693278991)
    ·
      refine ⟨30390132621692758039918487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20260088414461838693278991 30390132621692758039918487)
      ·
        refine ⟨45585198932539137059877731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30390132621692758039918487 45585198932539137059877731)
        ·
          refine ⟨68377798398808705589816597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45585198932539137059877731 68377798398808705589816597)
          ·
            refine ⟨3205209299944158074522653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68377798398808705589816597 3205209299944158074522653)
            ·
              refine ⟨1201953487479059277945995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205209299944158074522653 1201953487479059277945995)
              ·
                refine ⟨1802930231218588916918993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201953487479059277945995 1802930231218588916918993)
                ·
                  refine ⟨1352197673413941687689245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1802930231218588916918993 1352197673413941687689245)
                  ·
                    refine ⟨507074127530228132883467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352197673413941687689245 507074127530228132883467)
                    ·
                      rfl

theorem cell22_1481285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_1481285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481285 prefixEnd_1481285 := by exact prefixLift 1481285
  have htrace : WordTrace (prefixWord ++ tailWord_1481285) baseStart_1481285 baseEnd_1481285 := by
    simpa [prefixWord, tailWord_1481285, baseEnd_1481285] using wordTrace_append hprefix tailTrace_1481285
  have hstable : (prefixWord ++ tailWord_1481285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481285).length < 2 ^ (prefixWord ++ tailWord_1481285).sum := by decide
  have hdescent : baseEnd_1481285 < baseStart_1481285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481296 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_1481296 : Nat := 118140960795 + 1481296 * 2 ^ 59
def prefixEnd_1481296 : Nat := 4983230072969 + 3 ^ 40 * 1481296 * 2
def baseEnd_1481296 : Nat := 507077893055027770858433

theorem tailTrace_1481296 : CollatzResearch.WordTrace tailWord_1481296 prefixEnd_1481296 507077893055027770858433 := by
  unfold tailWord_1481296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013651820762526030363871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36018202427683368040485161 27013651820762526030363871)
  ·
    refine ⟨40520477731143789045545807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27013651820762526030363871 40520477731143789045545807)
    ·
      refine ⟨60780716596715683568318711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40520477731143789045545807 60780716596715683568318711)
      ·
        refine ⟨91171074895073525352478067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60780716596715683568318711 91171074895073525352478067)
        ·
          refine ⟨136756612342610288028717101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91171074895073525352478067 136756612342610288028717101)
          ·
            refine ⟨51283729628478858010768913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136756612342610288028717101 51283729628478858010768913)
            ·
              refine ⟨38462797221359143508076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51283729628478858010768913 38462797221359143508076685)
              ·
                refine ⟨14423548958009678815528757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38462797221359143508076685 14423548958009678815528757)
                ·
                  refine ⟨1352207714813407388955821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14423548958009678815528757 1352207714813407388955821)
                  ·
                    refine ⟨507077893055027770858433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352207714813407388955821 507077893055027770858433)
                    ·
                      rfl

theorem cell22_1481296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_1481296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481296 prefixEnd_1481296 := by exact prefixLift 1481296
  have htrace : WordTrace (prefixWord ++ tailWord_1481296) baseStart_1481296 baseEnd_1481296 := by
    simpa [prefixWord, tailWord_1481296, baseEnd_1481296] using wordTrace_append hprefix tailTrace_1481296
  have hstable : (prefixWord ++ tailWord_1481296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481296).length < 2 ^ (prefixWord ++ tailWord_1481296).sum := by decide
  have hdescent : baseEnd_1481296 < baseStart_1481296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481373 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1481373 : Nat := 118140960795 + 1481373 * 2 ^ 59
def prefixEnd_1481373 : Nat := 4983230072969 + 3 ^ 40 * 1481373 * 2
def baseEnd_1481373 : Nat := 507104251728625236683197

theorem tailTrace_1481373 : CollatzResearch.WordTrace tailWord_1481373 prefixEnd_1481373 507104251728625236683197 := by
  unfold tailWord_1481373
  simp only [CollatzResearch.WordTrace]
  refine ⟨54030112062246094211280773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36020074708164062807520515 54030112062246094211280773)
  ·
    refine ⟨10130646011671142664615145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54030112062246094211280773 10130646011671142664615145)
    ·
      refine ⟨7597984508753356998461359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10130646011671142664615145 7597984508753356998461359)
      ·
        refine ⟨11396976763130035497692039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597984508753356998461359 11396976763130035497692039)
        ·
          refine ⟨17095465144695053246538059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396976763130035497692039 17095465144695053246538059)
          ·
            refine ⟨25643197717042579869807089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095465144695053246538059 25643197717042579869807089)
            ·
              refine ⟨19232398287781934902355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25643197717042579869807089 19232398287781934902355317)
              ·
                refine ⟨1803037339479556397095811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19232398287781934902355317 1803037339479556397095811)
                ·
                  refine ⟨2704556009219334595643717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803037339479556397095811 2704556009219334595643717)
                  ·
                    refine ⟨507104251728625236683197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704556009219334595643717 507104251728625236683197)
                    ·
                      rfl

theorem cell22_1481373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1481373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481373 prefixEnd_1481373 := by exact prefixLift 1481373
  have htrace : WordTrace (prefixWord ++ tailWord_1481373) baseStart_1481373 baseEnd_1481373 := by
    simpa [prefixWord, tailWord_1481373, baseEnd_1481373] using wordTrace_append hprefix tailTrace_1481373
  have hstable : (prefixWord ++ tailWord_1481373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481373).length < 2 ^ (prefixWord ++ tailWord_1481373).sum := by decide
  have hdescent : baseEnd_1481373 < baseStart_1481373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481390 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1481390 : Nat := 118140960795 + 1481390 * 2 ^ 59
def prefixEnd_1481390 : Nat := 4983230072969 + 3 ^ 40 * 1481390 * 2
def baseEnd_1481390 : Nat := 507110071176042859008145

theorem tailTrace_1481390 : CollatzResearch.WordTrace tailWord_1481390 prefixEnd_1481390 507110071176042859008145 := by
  unfold tailWord_1481390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753841512898063264331203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36020488068789670743099749 6753841512898063264331203)
  ·
    refine ⟨10130762269347094896496805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753841512898063264331203 10130762269347094896496805)
    ·
      refine ⟨1899517925502580293093151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10130762269347094896496805 1899517925502580293093151)
      ·
        refine ⟨2849276888253870439639727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899517925502580293093151 2849276888253870439639727)
        ·
          refine ⟨4273915332380805659459591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849276888253870439639727 4273915332380805659459591)
          ·
            refine ⟨6410872998571208489189387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273915332380805659459591 6410872998571208489189387)
            ·
              refine ⟨9616309497856812733784081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410872998571208489189387 9616309497856812733784081)
              ·
                refine ⟨7212232123392609550338061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616309497856812733784081 7212232123392609550338061)
                ·
                  refine ⟨2704587046272228581376773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7212232123392609550338061 2704587046272228581376773)
                  ·
                    refine ⟨507110071176042859008145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704587046272228581376773 507110071176042859008145)
                    ·
                      rfl

theorem cell22_1481390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1481390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481390 prefixEnd_1481390 := by exact prefixLift 1481390
  have htrace : WordTrace (prefixWord ++ tailWord_1481390) baseStart_1481390 baseEnd_1481390 := by
    simpa [prefixWord, tailWord_1481390, baseEnd_1481390] using wordTrace_append hprefix tailTrace_1481390
  have hstable : (prefixWord ++ tailWord_1481390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481390).length < 2 ^ (prefixWord ++ tailWord_1481390).sum := by decide
  have hdescent : baseEnd_1481390 < baseStart_1481390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481401 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1481401 : Nat := 118140960795 + 1481401 * 2 ^ 59
def prefixEnd_1481401 : Nat := 4983230072969 + 3 ^ 40 * 1481401 * 2
def baseEnd_1481401 : Nat := 507113836700842496983111

theorem tailTrace_1481401 : CollatzResearch.WordTrace tailWord_1481401 prefixEnd_1481401 507113836700842496983111 := by
  unfold tailWord_1481401
  simp only [CollatzResearch.WordTrace]
  refine ⟨54031133306144654993300057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36020755537429769995533371 54031133306144654993300057)
  ·
    refine ⟨40523349979608491244975043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54031133306144654993300057 40523349979608491244975043)
    ·
      refine ⟨60785024969412736867462565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40523349979608491244975043 60785024969412736867462565)
      ·
        refine ⟨11397192181764888162649231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60785024969412736867462565 11397192181764888162649231)
        ·
          refine ⟨17095788272647332243973847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11397192181764888162649231 17095788272647332243973847)
          ·
            refine ⟨25643682408970998365960771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095788272647332243973847 25643682408970998365960771)
            ·
              refine ⟨38465523613456497548941157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25643682408970998365960771 38465523613456497548941157)
              ·
                refine ⟨7212285677523093290426467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38465523613456497548941157 7212285677523093290426467)
                ·
                  refine ⟨10818428516284639935639701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212285677523093290426467 10818428516284639935639701)
                  ·
                    refine ⟨507113836700842496983111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10818428516284639935639701 507113836700842496983111)
                    ·
                      rfl

theorem cell22_1481401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1481401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481401 prefixEnd_1481401 := by exact prefixLift 1481401
  have htrace : WordTrace (prefixWord ++ tailWord_1481401) baseStart_1481401 baseEnd_1481401 := by
    simpa [prefixWord, tailWord_1481401, baseEnd_1481401] using wordTrace_append hprefix tailTrace_1481401
  have hstable : (prefixWord ++ tailWord_1481401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481401).length < 2 ^ (prefixWord ++ tailWord_1481401).sum := by decide
  have hdescent : baseEnd_1481401 < baseStart_1481401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481418 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1481418 : Nat := 118140960795 + 1481418 * 2 ^ 59
def prefixEnd_1481418 : Nat := 4983230072969 + 3 ^ 40 * 1481418 * 2
def baseEnd_1481418 : Nat := 507119656148260119308059

theorem tailTrace_1481418 : CollatzResearch.WordTrace tailWord_1481418 prefixEnd_1481418 507119656148260119308059 := by
  unfold tailWord_1481418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507938336770766724167227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36021168898055377931112605 13507938336770766724167227)
  ·
    refine ⟨20261907505156150086250841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13507938336770766724167227 20261907505156150086250841)
    ·
      refine ⟨15196430628867112564688131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20261907505156150086250841 15196430628867112564688131)
      ·
        refine ⟨22794645943300668847032197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15196430628867112564688131 22794645943300668847032197)
        ·
          refine ⟨4273996114368875408818537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22794645943300668847032197 4273996114368875408818537)
          ·
            refine ⟨3205497085776656556613903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4273996114368875408818537 3205497085776656556613903)
            ·
              refine ⟨4808245628664984834920855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205497085776656556613903 4808245628664984834920855)
              ·
                refine ⟨7212368442997477252381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808245628664984834920855 7212368442997477252381283)
                ·
                  refine ⟨10818552664496215878571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212368442997477252381283 10818552664496215878571925)
                  ·
                    refine ⟨507119656148260119308059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10818552664496215878571925 507119656148260119308059)
                    ·
                      rfl

theorem cell22_1481418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1481418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481418 prefixEnd_1481418 := by exact prefixLift 1481418
  have htrace : WordTrace (prefixWord ++ tailWord_1481418) baseStart_1481418 baseEnd_1481418 := by
    simpa [prefixWord, tailWord_1481418, baseEnd_1481418] using wordTrace_append hprefix tailTrace_1481418
  have hstable : (prefixWord ++ tailWord_1481418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481418).length < 2 ^ (prefixWord ++ tailWord_1481418).sum := by decide
  have hdescent : baseEnd_1481418 < baseStart_1481418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481525 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1481525 : Nat := 118140960795 + 1481525 * 2 ^ 59
def prefixEnd_1481525 : Nat := 4983230072969 + 3 ^ 40 * 1481525 * 2
def baseEnd_1481525 : Nat := 507156284434947506882731

theorem tailTrace_1481525 : CollatzResearch.WordTrace tailWord_1481525 prefixEnd_1481525 507156284434947506882731 := by
  unfold tailWord_1481525
  simp only [CollatzResearch.WordTrace]
  refine ⟨54035655957695424170814029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36023770638463616113876019 54035655957695424170814029)
  ·
    refine ⟨20263370984135784064055261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54035655957695424170814029 20263370984135784064055261)
    ·
      refine ⟨7598764119050919024020723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20263370984135784064055261 7598764119050919024020723)
      ·
        refine ⟨11398146178576378536031085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598764119050919024020723 11398146178576378536031085)
        ·
          refine ⟨4274304816966141951011657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11398146178576378536031085 4274304816966141951011657)
          ·
            refine ⟨3205728612724606463258743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274304816966141951011657 3205728612724606463258743)
            ·
              refine ⟨4808592919086909694888115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205728612724606463258743 4808592919086909694888115)
              ·
                refine ⟨7212889378630364542332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808592919086909694888115 7212889378630364542332173)
                ·
                  refine ⟨2704833516986386703374565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7212889378630364542332173 2704833516986386703374565)
                  ·
                    refine ⟨507156284434947506882731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704833516986386703374565 507156284434947506882731)
                    ·
                      rfl

theorem cell22_1481525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1481525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481525 prefixEnd_1481525 := by exact prefixLift 1481525
  have htrace : WordTrace (prefixWord ++ tailWord_1481525) baseStart_1481525 baseEnd_1481525 := by
    simpa [prefixWord, tailWord_1481525, baseEnd_1481525] using wordTrace_append hprefix tailTrace_1481525
  have hstable : (prefixWord ++ tailWord_1481525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481525).length < 2 ^ (prefixWord ++ tailWord_1481525).sum := by decide
  have hdescent : baseEnd_1481525 < baseStart_1481525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481572 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1481572 : Nat := 118140960795 + 1481572 * 2 ^ 59
def prefixEnd_1481572 : Nat := 4983230072969 + 3 ^ 40 * 1481572 * 2
def baseEnd_1481572 : Nat := 507172373495455050957587

theorem tailTrace_1481572 : CollatzResearch.WordTrace tailWord_1481572 prefixEnd_1481572 507172373495455050957587 := by
  unfold tailWord_1481572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018685094262575598887485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36024913459016767465183313 27018685094262575598887485)
  ·
    refine ⟨10132006910348465849582807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27018685094262575598887485 10132006910348465849582807)
    ·
      refine ⟨15198010365522698774374211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10132006910348465849582807 15198010365522698774374211)
      ·
        refine ⟨22797015548284048161561317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15198010365522698774374211 22797015548284048161561317)
        ·
          refine ⟨4274440415303259030292747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22797015548284048161561317 4274440415303259030292747)
          ·
            refine ⟨6411660622954888545439121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274440415303259030292747 6411660622954888545439121)
            ·
              refine ⟨4808745467216166409079341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411660622954888545439121 4808745467216166409079341)
              ·
                refine ⟨1803279550206062403404753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4808745467216166409079341 1803279550206062403404753)
                ·
                  refine ⟨1352459662654546802553565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803279550206062403404753 1352459662654546802553565)
                  ·
                    refine ⟨507172373495455050957587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352459662654546802553565 507172373495455050957587)
                    ·
                      rfl

theorem cell22_1481572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1481572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481572 prefixEnd_1481572 := by exact prefixLift 1481572
  have htrace : WordTrace (prefixWord ++ tailWord_1481572) baseStart_1481572 baseEnd_1481572 := by
    simpa [prefixWord, tailWord_1481572, baseEnd_1481572] using wordTrace_append hprefix tailTrace_1481572
  have hstable : (prefixWord ++ tailWord_1481572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481572).length < 2 ^ (prefixWord ++ tailWord_1481572).sum := by decide
  have hdescent : baseEnd_1481572 < baseStart_1481572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481585 : List Nat := [1, 2, 2, 2, 1, 5, 3, 6]
def baseStart_1481585 : Nat := 118140960795 + 1481585 * 2 ^ 59
def prefixEnd_1481585 : Nat := 4983230072969 + 3 ^ 40 * 1481585 * 2
def baseEnd_1481585 : Nat := 56352980406791927820283

theorem tailTrace_1481585 : CollatzResearch.WordTrace tailWord_1481585 prefixEnd_1481585 56352980406791927820283 := by
  unfold tailWord_1481585
  simp only [CollatzResearch.WordTrace]
  refine ⟨54037844337478054417998209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36025229558318702945332139 54037844337478054417998209)
  ·
    refine ⟨40528383253108540813498657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54037844337478054417998209 40528383253108540813498657)
    ·
      refine ⟨30396287439831405610123993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40528383253108540813498657 30396287439831405610123993)
      ·
        refine ⟨22797215579873554207592995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30396287439831405610123993 22797215579873554207592995)
        ·
          refine ⟨34195823369810331311389493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22797215579873554207592995 34195823369810331311389493)
          ·
            refine ⟨3205858440919718560442765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34195823369810331311389493 3205858440919718560442765)
            ·
              refine ⟨1202196915344894460166037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205858440919718560442765 1202196915344894460166037)
              ·
                refine ⟨56352980406791927820283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1202196915344894460166037 56352980406791927820283)
                ·
                  rfl

theorem cell22_1481585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 6].length) (baseStart_1481585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481585 prefixEnd_1481585 := by exact prefixLift 1481585
  have htrace : WordTrace (prefixWord ++ tailWord_1481585) baseStart_1481585 baseEnd_1481585 := by
    simpa [prefixWord, tailWord_1481585, baseEnd_1481585] using wordTrace_append hprefix tailTrace_1481585
  have hstable : (prefixWord ++ tailWord_1481585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481585).length < 2 ^ (prefixWord ++ tailWord_1481585).sum := by decide
  have hdescent : baseEnd_1481585 < baseStart_1481585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481668 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1481668 : Nat := 118140960795 + 1481668 * 2 ^ 59
def prefixEnd_1481668 : Nat := 4983230072969 + 3 ^ 40 * 1481668 * 2
def baseEnd_1481668 : Nat := 507205236257342800557293

theorem tailTrace_1481668 : CollatzResearch.WordTrace tailWord_1481668 prefixEnd_1481668 507205236257342800557293 := by
  unfold tailWord_1481668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020435798088679796634829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36027247730784906395513105 27020435798088679796634829)
  ·
    refine ⟨10132663424283254923738061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27020435798088679796634829 10132663424283254923738061)
    ·
      refine ⟨3799748784106220596401773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10132663424283254923738061 3799748784106220596401773)
      ·
        refine ⟨1424905794039832723650665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3799748784106220596401773 1424905794039832723650665)
        ·
          refine ⟨1068679345529874542737999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424905794039832723650665 1068679345529874542737999)
          ·
            refine ⟨1603019018294811814106999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068679345529874542737999 1603019018294811814106999)
            ·
              refine ⟨2404528527442217721160499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603019018294811814106999 2404528527442217721160499)
              ·
                refine ⟨3606792791163326581740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404528527442217721160499 3606792791163326581740749)
                ·
                  refine ⟨1352547296686247468152781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3606792791163326581740749 1352547296686247468152781)
                  ·
                    refine ⟨507205236257342800557293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352547296686247468152781 507205236257342800557293)
                    ·
                      rfl

theorem cell22_1481668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1481668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481668 prefixEnd_1481668 := by exact prefixLift 1481668
  have htrace : WordTrace (prefixWord ++ tailWord_1481668) baseStart_1481668 baseEnd_1481668 := by
    simpa [prefixWord, tailWord_1481668, baseEnd_1481668] using wordTrace_append hprefix tailTrace_1481668
  have hstable : (prefixWord ++ tailWord_1481668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481668).length < 2 ^ (prefixWord ++ tailWord_1481668).sum := by decide
  have hdescent : baseEnd_1481668 < baseStart_1481668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481673 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_1481673 : Nat := 118140960795 + 1481673 * 2 ^ 59
def prefixEnd_1481673 : Nat := 4983230072969 + 3 ^ 40 * 1481673 * 2
def baseEnd_1481673 : Nat := 507206947859524454182277

theorem tailTrace_1481673 : CollatzResearch.WordTrace tailWord_1481673 prefixEnd_1481673 507206947859524454182277 := by
  unfold tailWord_1481673
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041053961159245447201673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36027369307439496964801115 54041053961159245447201673)
  ·
    refine ⟨40530790470869434085401255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54041053961159245447201673 40530790470869434085401255)
    ·
      refine ⟨60796185706304151128101883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40530790470869434085401255 60796185706304151128101883)
      ·
        refine ⟨91194278559456226692152825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60796185706304151128101883 91194278559456226692152825)
        ·
          refine ⟨68395708919592170019114619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91194278559456226692152825 68395708919592170019114619)
          ·
            refine ⟨102593563379388255028671929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68395708919592170019114619 102593563379388255028671929)
            ·
              refine ⟨76945172534541191271503947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102593563379388255028671929 76945172534541191271503947)
              ·
                refine ⟨115417758801811786907255921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76945172534541191271503947 115417758801811786907255921)
                ·
                  refine ⟨86563319101358840180441941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115417758801811786907255921 86563319101358840180441941)
                  ·
                    refine ⟨507206947859524454182277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86563319101358840180441941 507206947859524454182277)
                    ·
                      rfl

theorem cell22_1481673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_1481673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481673 prefixEnd_1481673 := by exact prefixLift 1481673
  have htrace : WordTrace (prefixWord ++ tailWord_1481673) baseStart_1481673 baseEnd_1481673 := by
    simpa [prefixWord, tailWord_1481673, baseEnd_1481673] using wordTrace_append hprefix tailTrace_1481673
  have hstable : (prefixWord ++ tailWord_1481673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481673).length < 2 ^ (prefixWord ++ tailWord_1481673).sum := by decide
  have hdescent : baseEnd_1481673 < baseStart_1481673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481675 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 6]
def baseStart_1481675 : Nat := 118140960795 + 1481675 * 2 ^ 59
def prefixEnd_1481675 : Nat := 4983230072969 + 3 ^ 40 * 1481675 * 2
def baseEnd_1481675 : Nat := 169069210833465705210757

theorem tailTrace_1481675 : CollatzResearch.WordTrace tailWord_1481675 prefixEnd_1481675 169069210833465705210757 := by
  unfold tailWord_1481675
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041126907151999788774479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36027417938101333192516319 54041126907151999788774479)
  ·
    refine ⟨81061690360727999683161719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54041126907151999788774479 81061690360727999683161719)
    ·
      refine ⟨121592535541091999524742579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81061690360727999683161719 121592535541091999524742579)
      ·
        refine ⟨182388803311637999287113869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121592535541091999524742579 182388803311637999287113869)
        ·
          refine ⟨68395801241864249732667701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182388803311637999287113869 68395801241864249732667701)
          ·
            refine ⟨6412106366424773412437597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68395801241864249732667701 6412106366424773412437597)
            ·
              refine ⟨2404539887409290029664099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6412106366424773412437597 2404539887409290029664099)
              ·
                refine ⟨3606809831113935044496149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404539887409290029664099 3606809831113935044496149)
                ·
                  refine ⟨169069210833465705210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3606809831113935044496149 169069210833465705210757)
                  ·
                    rfl

theorem cell22_1481675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_1481675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481675 prefixEnd_1481675 := by exact prefixLift 1481675
  have htrace : WordTrace (prefixWord ++ tailWord_1481675) baseStart_1481675 baseEnd_1481675 := by
    simpa [prefixWord, tailWord_1481675, baseEnd_1481675] using wordTrace_append hprefix tailTrace_1481675
  have hstable : (prefixWord ++ tailWord_1481675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481675).length < 2 ^ (prefixWord ++ tailWord_1481675).sum := by decide
  have hdescent : baseEnd_1481675 < baseStart_1481675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481724 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1481724 : Nat := 118140960795 + 1481724 * 2 ^ 59
def prefixEnd_1481724 : Nat := 4983230072969 + 3 ^ 40 * 1481724 * 2
def baseEnd_1481724 : Nat := 507224406201777321157121

theorem tailTrace_1481724 : CollatzResearch.WordTrace tailWord_1481724 prefixEnd_1481724 507224406201777321157121 := by
  unfold tailWord_1481724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021457041987240578654113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36028609389316320771538817 27021457041987240578654113)
  ·
    refine ⟨20266092781490430433990585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27021457041987240578654113 20266092781490430433990585)
    ·
      refine ⟨15199569586117822825492939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20266092781490430433990585 15199569586117822825492939)
      ·
        refine ⟨22799354379176734238239409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199569586117822825492939 22799354379176734238239409)
        ·
          refine ⟨17099515784382550678679557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22799354379176734238239409 17099515784382550678679557)
          ·
            refine ⟨3206159209571728252252417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17099515784382550678679557 3206159209571728252252417)
            ·
              refine ⟨2404619407178796189189313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206159209571728252252417 2404619407178796189189313)
              ·
                refine ⟨1803464555384097141891985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404619407178796189189313 1803464555384097141891985)
                ·
                  refine ⟨1352598416538072856418989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803464555384097141891985 1352598416538072856418989)
                  ·
                    refine ⟨507224406201777321157121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352598416538072856418989 507224406201777321157121)
                    ·
                      rfl

theorem cell22_1481724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1481724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481724 prefixEnd_1481724 := by exact prefixLift 1481724
  have htrace : WordTrace (prefixWord ++ tailWord_1481724) baseStart_1481724 baseEnd_1481724 := by
    simpa [prefixWord, tailWord_1481724, baseEnd_1481724] using wordTrace_append hprefix tailTrace_1481724
  have hstable : (prefixWord ++ tailWord_1481724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481724).length < 2 ^ (prefixWord ++ tailWord_1481724).sum := by decide
  have hdescent : baseEnd_1481724 < baseStart_1481724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481726 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1481726 : Nat := 118140960795 + 1481726 * 2 ^ 59
def prefixEnd_1481726 : Nat := 4983230072969 + 3 ^ 40 * 1481726 * 2
def baseEnd_1481726 : Nat := 169075030280883327535705

theorem tailTrace_1481726 : CollatzResearch.WordTrace tailWord_1481726 prefixEnd_1481726 169075030280883327535705 := by
  unfold tailWord_1481726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6755373378745904437360129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36028658019978156999254021 6755373378745904437360129)
  ·
    refine ⟨5066530034059428328020097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6755373378745904437360129 5066530034059428328020097)
    ·
      refine ⟨3799897525544571246015073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5066530034059428328020097 3799897525544571246015073)
      ·
        refine ⟨2849923144158428434511305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3799897525544571246015073 2849923144158428434511305)
        ·
          refine ⟨2137442358118821325883479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849923144158428434511305 2137442358118821325883479)
          ·
            refine ⟨3206163537178231988825219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137442358118821325883479 3206163537178231988825219)
            ·
              refine ⟨4809245305767347983237829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206163537178231988825219 4809245305767347983237829)
              ·
                refine ⟨901733494831377746857093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4809245305767347983237829 901733494831377746857093)
                ·
                  refine ⟨169075030280883327535705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901733494831377746857093 169075030280883327535705)
                  ·
                    rfl

theorem cell22_1481726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1481726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481726 prefixEnd_1481726 := by exact prefixLift 1481726
  have htrace : WordTrace (prefixWord ++ tailWord_1481726) baseStart_1481726 baseEnd_1481726 := by
    simpa [prefixWord, tailWord_1481726, baseEnd_1481726] using wordTrace_append hprefix tailTrace_1481726
  have hstable : (prefixWord ++ tailWord_1481726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481726).length < 2 ^ (prefixWord ++ tailWord_1481726).sum := by decide
  have hdescent : baseEnd_1481726 < baseStart_1481726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481752 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_1481752 : Nat := 118140960795 + 1481752 * 2 ^ 59
def prefixEnd_1481752 : Nat := 4983230072969 + 3 ^ 40 * 1481752 * 2
def baseEnd_1481752 : Nat := 507233991173994581457035

theorem tailTrace_1481752 : CollatzResearch.WordTrace tailWord_1481752 prefixEnd_1481752 507233991173994581457035 := by
  unfold tailWord_1481752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021967663936520969663755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36029290218582027959551673 27021967663936520969663755)
  ·
    refine ⟨40532951495904781454495633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27021967663936520969663755 40532951495904781454495633)
    ·
      refine ⟨30399713621928586090871725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40532951495904781454495633 30399713621928586090871725)
      ·
        refine ⟨11399892608223219784076897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30399713621928586090871725 11399892608223219784076897)
        ·
          refine ⟨8549919456167414838057673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11399892608223219784076897 8549919456167414838057673)
          ·
            refine ⟨6412439592125561128543255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8549919456167414838057673 6412439592125561128543255)
            ·
              refine ⟨9618659388188341692814883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412439592125561128543255 9618659388188341692814883)
              ·
                refine ⟨14427989082282512539222325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618659388188341692814883 14427989082282512539222325)
                ·
                  refine ⟨1352623976463985550552093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14427989082282512539222325 1352623976463985550552093)
                  ·
                    refine ⟨507233991173994581457035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352623976463985550552093 507233991173994581457035)
                    ·
                      rfl

theorem cell22_1481752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_1481752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481752 prefixEnd_1481752 := by exact prefixLift 1481752
  have htrace : WordTrace (prefixWord ++ tailWord_1481752) baseStart_1481752 baseEnd_1481752 := by
    simpa [prefixWord, tailWord_1481752, baseEnd_1481752] using wordTrace_append hprefix tailTrace_1481752
  have hstable : (prefixWord ++ tailWord_1481752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481752).length < 2 ^ (prefixWord ++ tailWord_1481752).sum := by decide
  have hdescent : baseEnd_1481752 < baseStart_1481752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481756 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1481756 : Nat := 118140960795 + 1481756 * 2 ^ 59
def prefixEnd_1481756 : Nat := 4983230072969 + 3 ^ 40 * 1481756 * 2
def baseEnd_1481756 : Nat := 507235360455739904357023

theorem tailTrace_1481756 : CollatzResearch.WordTrace tailWord_1481756 prefixEnd_1481756 507235360455739904357023 := by
  unfold tailWord_1481756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27022040609929275311236561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36029387479905700414982081 27022040609929275311236561)
  ·
    refine ⟨20266530457446956483427421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27022040609929275311236561 20266530457446956483427421)
    ·
      refine ⟨7599948921542608681285283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20266530457446956483427421 7599948921542608681285283)
      ·
        refine ⟨11399923382313913021927925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599948921542608681285283 11399923382313913021927925)
        ·
          refine ⟨1068742817091929345805743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11399923382313913021927925 1068742817091929345805743)
          ·
            refine ⟨1603114225637894018708615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068742817091929345805743 1603114225637894018708615)
            ·
              refine ⟨2404671338456841028062923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603114225637894018708615 2404671338456841028062923)
              ·
                refine ⟨3607007007685261542094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404671338456841028062923 3607007007685261542094385)
                ·
                  refine ⟨2705255255763946156570789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607007007685261542094385 2705255255763946156570789)
                  ·
                    refine ⟨507235360455739904357023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705255255763946156570789 507235360455739904357023)
                    ·
                      rfl

theorem cell22_1481756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1481756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481756 prefixEnd_1481756 := by exact prefixLift 1481756
  have htrace : WordTrace (prefixWord ++ tailWord_1481756) baseStart_1481756 baseEnd_1481756 := by
    simpa [prefixWord, tailWord_1481756, baseEnd_1481756] using wordTrace_append hprefix tailTrace_1481756
  have hstable : (prefixWord ++ tailWord_1481756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481756).length < 2 ^ (prefixWord ++ tailWord_1481756).sum := by decide
  have hdescent : baseEnd_1481756 < baseStart_1481756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481765 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 7]
def baseStart_1481765 : Nat := 118140960795 + 1481765 * 2 ^ 59
def prefixEnd_1481765 : Nat := 4983230072969 + 3 ^ 40 * 1481765 * 2
def baseEnd_1481765 : Nat := 169079480446555626960665

theorem tailTrace_1481765 : CollatzResearch.WordTrace tailWord_1481765 prefixEnd_1481765 169079480446555626960665 := by
  unfold tailWord_1481765
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044409476825945159550749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36029606317883963439700499 54044409476825945159550749)
  ·
    refine ⟨20266653553809729434831531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54044409476825945159550749 20266653553809729434831531)
    ·
      refine ⟨30399980330714594152247297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20266653553809729434831531 30399980330714594152247297)
      ·
        refine ⟨22799985248035945614185473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30399980330714594152247297 22799985248035945614185473)
        ·
          refine ⟨17099988936026959210639105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22799985248035945614185473 17099988936026959210639105)
          ·
            refine ⟨12824991702020219407979329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17099988936026959210639105 12824991702020219407979329)
            ·
              refine ⟨9618743776515164555984497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12824991702020219407979329 9618743776515164555984497)
              ·
                refine ⟨7214057832386373416988373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9618743776515164555984497 7214057832386373416988373)
                ·
                  refine ⟨169079480446555626960665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7214057832386373416988373 169079480446555626960665)
                  ·
                    rfl

theorem cell22_1481765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_1481765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481765 prefixEnd_1481765 := by exact prefixLift 1481765
  have htrace : WordTrace (prefixWord ++ tailWord_1481765) baseStart_1481765 baseEnd_1481765 := by
    simpa [prefixWord, tailWord_1481765, baseEnd_1481765] using wordTrace_append hprefix tailTrace_1481765
  have hstable : (prefixWord ++ tailWord_1481765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481765).length < 2 ^ (prefixWord ++ tailWord_1481765).sum := by decide
  have hdescent : baseEnd_1481765 < baseStart_1481765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481799 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 5]
def baseStart_1481799 : Nat := 118140960795 + 1481799 * 2 ^ 59
def prefixEnd_1481799 : Nat := 4983230072969 + 3 ^ 40 * 1481799 * 2
def baseEnd_1481799 : Nat := 169083360078167375177297

theorem tailTrace_1481799 : CollatzResearch.WordTrace tailWord_1481799 prefixEnd_1481799 169083360078167375177297 := by
  unfold tailWord_1481799
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045649558702768966288451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36030433039135179310858967 54045649558702768966288451)
  ·
    refine ⟨81068474338054153449432677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54045649558702768966288451 81068474338054153449432677)
    ·
      refine ⟨15200338938385153771768627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81068474338054153449432677 15200338938385153771768627)
      ·
        refine ⟨22800508407577730657652941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15200338938385153771768627 22800508407577730657652941)
        ·
          refine ⟨8550190652841648996619853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22800508407577730657652941 8550190652841648996619853)
          ·
            refine ⟨3206321494815618373732445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8550190652841648996619853 3206321494815618373732445)
            ·
              refine ⟨1202370560555856890149667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206321494815618373732445 1202370560555856890149667)
              ·
                refine ⟨1803555840833785335224501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202370560555856890149667 1803555840833785335224501)
                ·
                  refine ⟨169083360078167375177297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803555840833785335224501 169083360078167375177297)
                  ·
                    rfl

theorem cell22_1481799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 5].length) (baseStart_1481799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481799 prefixEnd_1481799 := by exact prefixLift 1481799
  have htrace : WordTrace (prefixWord ++ tailWord_1481799) baseStart_1481799 baseEnd_1481799 := by
    simpa [prefixWord, tailWord_1481799, baseEnd_1481799] using wordTrace_append hprefix tailTrace_1481799
  have hstable : (prefixWord ++ tailWord_1481799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481799).length < 2 ^ (prefixWord ++ tailWord_1481799).sum := by decide
  have hdescent : baseEnd_1481799 < baseStart_1481799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481812 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1481812 : Nat := 118140960795 + 1481812 * 2 ^ 59
def prefixEnd_1481812 : Nat := 4983230072969 + 3 ^ 40 * 1481812 * 2
def baseEnd_1481812 : Nat := 507254530400174424956851

theorem tailTrace_1481812 : CollatzResearch.WordTrace tailWord_1481812 prefixEnd_1481812 507254530400174424956851 := by
  unfold tailWord_1481812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27023061853827836093255845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36030749138437114791007793 27023061853827836093255845)
  ·
    refine ⟨5066824097592719267485471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27023061853827836093255845 5066824097592719267485471)
    ·
      refine ⟨7600236146389078901228207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5066824097592719267485471 7600236146389078901228207)
      ·
        refine ⟨11400354219583618351842311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600236146389078901228207 11400354219583618351842311)
        ·
          refine ⟨17100531329375427527763467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400354219583618351842311 17100531329375427527763467)
          ·
            refine ⟨25650796994063141291645201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100531329375427527763467 25650796994063141291645201)
            ·
              refine ⟨19238097745547355968733901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25650796994063141291645201 19238097745547355968733901)
              ·
                refine ⟨7214286654580258488275213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19238097745547355968733901 7214286654580258488275213)
                ·
                  refine ⟨2705357495467596933103205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7214286654580258488275213 2705357495467596933103205)
                  ·
                    refine ⟨507254530400174424956851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705357495467596933103205 507254530400174424956851)
                    ·
                      rfl

theorem cell22_1481812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1481812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481812 prefixEnd_1481812 := by exact prefixLift 1481812
  have htrace : WordTrace (prefixWord ++ tailWord_1481812) baseStart_1481812 baseEnd_1481812 := by
    simpa [prefixWord, tailWord_1481812, baseEnd_1481812] using wordTrace_append hprefix tailTrace_1481812
  have hstable : (prefixWord ++ tailWord_1481812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481812).length < 2 ^ (prefixWord ++ tailWord_1481812).sum := by decide
  have hdescent : baseEnd_1481812 < baseStart_1481812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481859 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 2, 3]
def baseStart_1481859 : Nat := 118140960795 + 1481859 * 2 ^ 59
def prefixEnd_1481859 : Nat := 4983230072969 + 3 ^ 40 * 1481859 * 2
def baseEnd_1481859 : Nat := 507270619460681969031707

theorem tailTrace_1481859 : CollatzResearch.WordTrace tailWord_1481859 prefixEnd_1481859 507270619460681969031707 := by
  unfold tailWord_1481859
  simp only [CollatzResearch.WordTrace]
  refine ⟨54047837938485399213472631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36031891958990266142315087 54047837938485399213472631)
  ·
    refine ⟨81071756907728098820208947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54047837938485399213472631 81071756907728098820208947)
    ·
      refine ⟨121607635361592148230313421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81071756907728098820208947 121607635361592148230313421)
      ·
        refine ⟨45602863260597055586367533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121607635361592148230313421 45602863260597055586367533)
        ·
          refine ⟨17101073722723895844887825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45602863260597055586367533 17101073722723895844887825)
          ·
            refine ⟨12825805292042921883665869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17101073722723895844887825 12825805292042921883665869)
            ·
              refine ⟨4809676984516095706374701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12825805292042921883665869 4809676984516095706374701)
              ·
                refine ⟨1803628869193535889890513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4809676984516095706374701 1803628869193535889890513)
                ·
                  refine ⟨1352721651895151917417885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803628869193535889890513 1352721651895151917417885)
                  ·
                    refine ⟨507270619460681969031707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352721651895151917417885 507270619460681969031707)
                    ·
                      rfl

theorem cell22_1481859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].length) (baseStart_1481859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481859 prefixEnd_1481859 := by exact prefixLift 1481859
  have htrace : WordTrace (prefixWord ++ tailWord_1481859) baseStart_1481859 baseEnd_1481859 := by
    simpa [prefixWord, tailWord_1481859, baseEnd_1481859] using wordTrace_append hprefix tailTrace_1481859
  have hstable : (prefixWord ++ tailWord_1481859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481859).length < 2 ^ (prefixWord ++ tailWord_1481859).sum := by decide
  have hdescent : baseEnd_1481859 < baseStart_1481859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481874 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1481874 : Nat := 118140960795 + 1481874 * 2 ^ 59
def prefixEnd_1481874 : Nat := 4983230072969 + 3 ^ 40 * 1481874 * 2
def baseEnd_1481874 : Nat := 507275754267226929906661

theorem tailTrace_1481874 : CollatzResearch.WordTrace tailWord_1481874 prefixEnd_1481874 507275754267226929906661 := by
  unfold tailWord_1481874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13512096258357764193817169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36032256688954037850179117 13512096258357764193817169)
  ·
    refine ⟨10134072193768323145362877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13512096258357764193817169 10134072193768323145362877)
    ·
      refine ⟨3800277072663121179511079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10134072193768323145362877 3800277072663121179511079)
      ·
        refine ⟨5700415608994681769266619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800277072663121179511079 5700415608994681769266619)
        ·
          refine ⟨8550623413492022653899929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700415608994681769266619 8550623413492022653899929)
          ·
            refine ⟨6412967560119016990424947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8550623413492022653899929 6412967560119016990424947)
            ·
              refine ⟨9619451340178525485637421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412967560119016990424947 9619451340178525485637421)
              ·
                refine ⟨3607294252566947057114033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9619451340178525485637421 3607294252566947057114033)
                ·
                  refine ⟨2705470689425210292835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607294252566947057114033 2705470689425210292835525)
                  ·
                    refine ⟨507275754267226929906661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705470689425210292835525 507275754267226929906661)
                    ·
                      rfl

theorem cell22_1481874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1481874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481874 prefixEnd_1481874 := by exact prefixLift 1481874
  have htrace : WordTrace (prefixWord ++ tailWord_1481874) baseStart_1481874 baseEnd_1481874 := by
    simpa [prefixWord, tailWord_1481874, baseEnd_1481874] using wordTrace_append hprefix tailTrace_1481874
  have hstable : (prefixWord ++ tailWord_1481874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481874).length < 2 ^ (prefixWord ++ tailWord_1481874).sum := by decide
  have hdescent : baseEnd_1481874 < baseStart_1481874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481921 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1481921 : Nat := 118140960795 + 1481921 * 2 ^ 59
def prefixEnd_1481921 : Nat := 4983230072969 + 3 ^ 40 * 1481921 * 2
def baseEnd_1481921 : Nat := 507291843327734473981517

theorem tailTrace_1481921 : CollatzResearch.WordTrace tailWord_1481921 prefixEnd_1481921 507291843327734473981517 := by
  unfold tailWord_1481921
  simp only [CollatzResearch.WordTrace]
  refine ⟨54050099264260783802229617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36033399509507189201486411 54050099264260783802229617)
  ·
    refine ⟨40537574448195587851672213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54050099264260783802229617 40537574448195587851672213)
    ·
      refine ⟨1900198802259168180547135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40537574448195587851672213 1900198802259168180547135)
      ·
        refine ⟨2850298203388752270820703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900198802259168180547135 2850298203388752270820703)
        ·
          refine ⟨4275447305083128406231055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850298203388752270820703 4275447305083128406231055)
          ·
            refine ⟨6413170957624692609346583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275447305083128406231055 6413170957624692609346583)
            ·
              refine ⟨9619756436437038914019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413170957624692609346583 9619756436437038914019875)
              ·
                refine ⟨14429634654655558371029813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619756436437038914019875 14429634654655558371029813)
                ·
                  refine ⟨1352778248873958597284045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14429634654655558371029813 1352778248873958597284045)
                  ·
                    refine ⟨507291843327734473981517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352778248873958597284045 507291843327734473981517)
                    ·
                      rfl

theorem cell22_1481921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1481921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481921 prefixEnd_1481921 := by exact prefixLift 1481921
  have htrace : WordTrace (prefixWord ++ tailWord_1481921) baseStart_1481921 baseEnd_1481921 := by
    simpa [prefixWord, tailWord_1481921, baseEnd_1481921] using wordTrace_append hprefix tailTrace_1481921
  have hstable : (prefixWord ++ tailWord_1481921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481921).length < 2 ^ (prefixWord ++ tailWord_1481921).sum := by decide
  have hdescent : baseEnd_1481921 < baseStart_1481921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481938 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1481938 : Nat := 118140960795 + 1481938 * 2 ^ 59
def prefixEnd_1481938 : Nat := 4983230072969 + 3 ^ 40 * 1481938 * 2
def baseEnd_1481938 : Nat := 507297662775152096306465

theorem tailTrace_1481938 : CollatzResearch.WordTrace tailWord_1481938 prefixEnd_1481938 507297662775152096306465 := by
  unfold tailWord_1481938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13512679826299798926399617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36033812870132797137065645 13512679826299798926399617)
  ·
    refine ⟨10134509869724849194799713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13512679826299798926399617 10134509869724849194799713)
    ·
      refine ⟨7600882402293636896099785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10134509869724849194799713 7600882402293636896099785)
      ·
        refine ⟨5700661801720227672074839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7600882402293636896099785 5700661801720227672074839)
        ·
          refine ⟨8550992702580341508112259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700661801720227672074839 8550992702580341508112259)
          ·
            refine ⟨12826489053870512262168389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550992702580341508112259 12826489053870512262168389)
            ·
              refine ⟨2404966697600721049156573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12826489053870512262168389 2404966697600721049156573)
              ·
                refine ⟨901862511600270393433715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2404966697600721049156573 901862511600270393433715)
                ·
                  refine ⟨1352793767400405590150573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901862511600270393433715 1352793767400405590150573)
                  ·
                    refine ⟨507297662775152096306465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352793767400405590150573 507297662775152096306465)
                    ·
                      rfl

theorem cell22_1481938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1481938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481938 prefixEnd_1481938 := by exact prefixLift 1481938
  have htrace : WordTrace (prefixWord ++ tailWord_1481938) baseStart_1481938 baseEnd_1481938 := by
    simpa [prefixWord, tailWord_1481938, baseEnd_1481938] using wordTrace_append hprefix tailTrace_1481938
  have hstable : (prefixWord ++ tailWord_1481938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481938).length < 2 ^ (prefixWord ++ tailWord_1481938).sum := by decide
  have hdescent : baseEnd_1481938 < baseStart_1481938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481996 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_1481996 : Nat := 118140960795 + 1481996 * 2 ^ 59
def prefixEnd_1481996 : Nat := 4983230072969 + 3 ^ 40 * 1481996 * 2
def baseEnd_1481996 : Nat := 169105839120153092785429

theorem tailTrace_1481996 : CollatzResearch.WordTrace tailWord_1481996 prefixEnd_1481996 169105839120153092785429 := by
  unfold tailWord_1481996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27026417369494535805604921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36035223159326047740806561 27026417369494535805604921)
  ·
    refine ⟨20269813027120901854203691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27026417369494535805604921 20269813027120901854203691)
    ·
      refine ⟨30404719540681352781305537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20269813027120901854203691 30404719540681352781305537)
      ·
        refine ⟨22803539655511014585979153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30404719540681352781305537 22803539655511014585979153)
        ·
          refine ⟨17102654741633260939484365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22803539655511014585979153 17102654741633260939484365)
          ·
            refine ⟨6413495528112472852306637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17102654741633260939484365 6413495528112472852306637)
            ·
              refine ⟨2405060823042177319614989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6413495528112472852306637 2405060823042177319614989)
              ·
                refine ⟨901897808640816494855621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2405060823042177319614989 901897808640816494855621)
                ·
                  refine ⟨169105839120153092785429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901897808640816494855621 169105839120153092785429)
                  ·
                    rfl

theorem cell22_1481996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_1481996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1481996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1481996 prefixEnd_1481996 := by exact prefixLift 1481996
  have htrace : WordTrace (prefixWord ++ tailWord_1481996) baseStart_1481996 baseEnd_1481996 := by
    simpa [prefixWord, tailWord_1481996, baseEnd_1481996] using wordTrace_append hprefix tailTrace_1481996
  have hstable : (prefixWord ++ tailWord_1481996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481996).length < 2 ^ (prefixWord ++ tailWord_1481996).sum := by decide
  have hdescent : baseEnd_1481996 < baseStart_1481996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482024 : List Nat := [2, 1, 5, 1, 2, 1, 1, 9]
def baseStart_1482024 : Nat := 118140960795 + 1482024 * 2 ^ 59
def prefixEnd_1482024 : Nat := 4983230072969 + 3 ^ 40 * 1482024 * 2
def baseEnd_1482024 : Nat := 56369678036964059850689

theorem tailTrace_1482024 : CollatzResearch.WordTrace tailWord_1482024 prefixEnd_1482024 56369678036964059850689 := by
  unfold tailWord_1482024
  simp only [CollatzResearch.WordTrace]
  refine ⟨27026927991443816196614563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36035903988591754928819417 27026927991443816196614563)
  ·
    refine ⟨40540391987165724294921845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27026927991443816196614563 40540391987165724294921845)
    ·
      refine ⟨3800661748796786652648923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40540391987165724294921845 3800661748796786652648923)
      ·
        refine ⟨5700992623195179978973385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800661748796786652648923 5700992623195179978973385)
        ·
          refine ⟨4275744467396384984230039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5700992623195179978973385 4275744467396384984230039)
          ·
            refine ⟨6413616701094577476345059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275744467396384984230039 6413616701094577476345059)
            ·
              refine ⟨9620425051641866214517589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413616701094577476345059 9620425051641866214517589)
              ·
                refine ⟨56369678036964059850689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9620425051641866214517589 56369678036964059850689)
                ·
                  rfl

theorem cell22_1482024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_1482024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482024 prefixEnd_1482024 := by exact prefixLift 1482024
  have htrace : WordTrace (prefixWord ++ tailWord_1482024) baseStart_1482024 baseEnd_1482024 := by
    simpa [prefixWord, tailWord_1482024, baseEnd_1482024] using wordTrace_append hprefix tailTrace_1482024
  have hstable : (prefixWord ++ tailWord_1482024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482024).length < 2 ^ (prefixWord ++ tailWord_1482024).sum := by decide
  have hdescent : baseEnd_1482024 < baseStart_1482024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482084 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1482084 : Nat := 118140960795 + 1482084 * 2 ^ 59
def prefixEnd_1482084 : Nat := 4983230072969 + 3 ^ 40 * 1482084 * 2
def baseEnd_1482084 : Nat := 507347641558856382156017

theorem tailTrace_1482084 : CollatzResearch.WordTrace tailWord_1482084 prefixEnd_1482084 507347641558856382156017 := by
  unfold tailWord_1482084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27028022181335131320206653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36037362908446841760275537 27028022181335131320206653)
  ·
    refine ⟨10135508318000674245077495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27028022181335131320206653 10135508318000674245077495)
    ·
      refine ⟨15203262477001011367616243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10135508318000674245077495 15203262477001011367616243)
      ·
        refine ⟨22804893715501517051424365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203262477001011367616243 22804893715501517051424365)
        ·
          refine ⟨8551835143313068894284137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22804893715501517051424365 8551835143313068894284137)
          ·
            refine ⟨6413876357484801670713103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8551835143313068894284137 6413876357484801670713103)
            ·
              refine ⟨9620814536227202506069655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413876357484801670713103 9620814536227202506069655)
              ·
                refine ⟨14431221804340803759104483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620814536227202506069655 14431221804340803759104483)
                ·
                  refine ⟨21646832706511205638656725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14431221804340803759104483 21646832706511205638656725)
                  ·
                    refine ⟨507347641558856382156017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21646832706511205638656725 507347641558856382156017)
                    ·
                      rfl

theorem cell22_1482084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1482084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482084 prefixEnd_1482084 := by exact prefixLift 1482084
  have htrace : WordTrace (prefixWord ++ tailWord_1482084) baseStart_1482084 baseEnd_1482084 := by
    simpa [prefixWord, tailWord_1482084, baseEnd_1482084] using wordTrace_append hprefix tailTrace_1482084
  have hstable : (prefixWord ++ tailWord_1482084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482084).length < 2 ^ (prefixWord ++ tailWord_1482084).sum := by decide
  have hdescent : baseEnd_1482084 < baseStart_1482084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482144 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_1482144 : Nat := 118140960795 + 1482144 * 2 ^ 59
def prefixEnd_1482144 : Nat := 4983230072969 + 3 ^ 40 * 1482144 * 2
def baseEnd_1482144 : Nat := 507368180785036225655833

theorem tailTrace_1482144 : CollatzResearch.WordTrace tailWord_1482144 prefixEnd_1482144 507368180785036225655833 := by
  unfold tailWord_1482144
  simp only [CollatzResearch.WordTrace]
  refine ⟨27029116371226446443798743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36038821828301928591731657 27029116371226446443798743)
  ·
    refine ⟨40543674556839669665698115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27029116371226446443798743 40543674556839669665698115)
    ·
      refine ⟨60815511835259504498547173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40543674556839669665698115 60815511835259504498547173)
      ·
        refine ⟨11402908469111157093477595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60815511835259504498547173 11402908469111157093477595)
        ·
          refine ⟨17104362703666735640216393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11402908469111157093477595 17104362703666735640216393)
          ·
            refine ⟨12828272027750051730162295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17104362703666735640216393 12828272027750051730162295)
            ·
              refine ⟨19242408041625077595243443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12828272027750051730162295 19242408041625077595243443)
              ·
                refine ⟨28863612062437616392865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19242408041625077595243443 28863612062437616392865165)
                ·
                  refine ⟨10823854523414106147324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28863612062437616392865165 10823854523414106147324437)
                  ·
                    refine ⟨507368180785036225655833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10823854523414106147324437 507368180785036225655833)
                    ·
                      rfl

theorem cell22_1482144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_1482144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482144 prefixEnd_1482144 := by exact prefixLift 1482144
  have htrace : WordTrace (prefixWord ++ tailWord_1482144) baseStart_1482144 baseEnd_1482144 := by
    simpa [prefixWord, tailWord_1482144, baseEnd_1482144] using wordTrace_append hprefix tailTrace_1482144
  have hstable : (prefixWord ++ tailWord_1482144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482144).length < 2 ^ (prefixWord ++ tailWord_1482144).sum := by decide
  have hdescent : baseEnd_1482144 < baseStart_1482144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482161 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1482161 : Nat := 118140960795 + 1482161 * 2 ^ 59
def prefixEnd_1482161 : Nat := 4983230072969 + 3 ^ 40 * 1482161 * 2
def baseEnd_1482161 : Nat := 507374000232453847980781

theorem tailTrace_1482161 : CollatzResearch.WordTrace tailWord_1482161 prefixEnd_1482161 507374000232453847980781 := by
  unfold tailWord_1482161
  simp only [CollatzResearch.WordTrace]
  refine ⟨54058852783391304790966337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36039235188927536527310891 54058852783391304790966337)
  ·
    refine ⟨40544139587543478593224753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54058852783391304790966337 40544139587543478593224753)
    ·
      refine ⟨30408104690657608944918565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40544139587543478593224753 30408104690657608944918565)
      ·
        refine ⟨5701519629498301677172231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30408104690657608944918565 5701519629498301677172231)
        ·
          refine ⟨8552279444247452515758347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701519629498301677172231 8552279444247452515758347)
          ·
            refine ⟨12828419166371178773637521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552279444247452515758347 12828419166371178773637521)
            ·
              refine ⟨9621314374778384080228141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12828419166371178773637521 9621314374778384080228141)
              ·
                refine ⟨3607992890541894030085553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9621314374778384080228141 3607992890541894030085553)
                ·
                  refine ⟨2705994667906420522564165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607992890541894030085553 2705994667906420522564165)
                  ·
                    refine ⟨507374000232453847980781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705994667906420522564165 507374000232453847980781)
                    ·
                      rfl

theorem cell22_1482161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1482161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482161 prefixEnd_1482161 := by exact prefixLift 1482161
  have htrace : WordTrace (prefixWord ++ tailWord_1482161) baseStart_1482161 baseEnd_1482161 := by
    simpa [prefixWord, tailWord_1482161, baseEnd_1482161] using wordTrace_append hprefix tailTrace_1482161
  have hstable : (prefixWord ++ tailWord_1482161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482161).length < 2 ^ (prefixWord ++ tailWord_1482161).sum := by decide
  have hdescent : baseEnd_1482161 < baseStart_1482161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482165 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 4]
def baseStart_1482165 : Nat := 118140960795 + 1482165 * 2 ^ 59
def prefixEnd_1482165 : Nat := 4983230072969 + 3 ^ 40 * 1482165 * 2
def baseEnd_1482165 : Nat := 169125123171399723626923

theorem tailTrace_1482165 : CollatzResearch.WordTrace tailWord_1482165 prefixEnd_1482165 169125123171399723626923 := by
  unfold tailWord_1482165
  simp only [CollatzResearch.WordTrace]
  refine ⟨54058998675376813474111949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36039332450251208982741299 54058998675376813474111949)
  ·
    refine ⟨20272124503266305052791981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54058998675376813474111949 20272124503266305052791981)
    ·
      refine ⟨7602046688724864394796993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20272124503266305052791981 7602046688724864394796993)
      ·
        refine ⟨5701535016543648296097745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602046688724864394796993 5701535016543648296097745)
        ·
          refine ⟨4276151262407736222073309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5701535016543648296097745 4276151262407736222073309)
          ·
            refine ⟨1603556723402901083277491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4276151262407736222073309 1603556723402901083277491)
            ·
              refine ⟨2405335085104351624916237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603556723402901083277491 2405335085104351624916237)
              ·
                refine ⟨902000656914131859343589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2405335085104351624916237 902000656914131859343589)
                ·
                  refine ⟨169125123171399723626923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902000656914131859343589 169125123171399723626923)
                  ·
                    rfl

theorem cell22_1482165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_1482165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482165 prefixEnd_1482165 := by exact prefixLift 1482165
  have htrace : WordTrace (prefixWord ++ tailWord_1482165) baseStart_1482165 baseEnd_1482165 := by
    simpa [prefixWord, tailWord_1482165, baseEnd_1482165] using wordTrace_append hprefix tailTrace_1482165
  have hstable : (prefixWord ++ tailWord_1482165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482165).length < 2 ^ (prefixWord ++ tailWord_1482165).sum := by decide
  have hdescent : baseEnd_1482165 < baseStart_1482165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482219 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_1482219 : Nat := 118140960795 + 1482219 * 2 ^ 59
def prefixEnd_1482219 : Nat := 4983230072969 + 3 ^ 40 * 1482219 * 2
def baseEnd_1482219 : Nat := 507393854817761030030603

theorem tailTrace_1482219 : CollatzResearch.WordTrace tailWord_1482219 prefixEnd_1482219 507393854817761030030603 := by
  unfold tailWord_1482219
  simp only [CollatzResearch.WordTrace]
  refine ⟨54060968217181180696577711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36040645478120787131051807 54060968217181180696577711)
  ·
    refine ⟨81091452325771771044866567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54060968217181180696577711 81091452325771771044866567)
    ·
      refine ⟨121637178488657656567299851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81091452325771771044866567 121637178488657656567299851)
      ·
        refine ⟨182455767732986484850949777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121637178488657656567299851 182455767732986484850949777)
        ·
          refine ⟨136841825799739863638212333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182455767732986484850949777 136841825799739863638212333)
          ·
            refine ⟨51315684674902448864329625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136841825799739863638212333 51315684674902448864329625)
            ·
              refine ⟨38486763506176836648247219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51315684674902448864329625 38486763506176836648247219)
              ·
                refine ⟨57730145259265254972370829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38486763506176836648247219 57730145259265254972370829)
                ·
                  refine ⟨21648804472224470614639061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57730145259265254972370829 21648804472224470614639061)
                  ·
                    refine ⟨507393854817761030030603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21648804472224470614639061 507393854817761030030603)
                    ·
                      rfl

theorem cell22_1482219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_1482219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482219 prefixEnd_1482219 := by exact prefixLift 1482219
  have htrace : WordTrace (prefixWord ++ tailWord_1482219) baseStart_1482219 baseEnd_1482219 := by
    simpa [prefixWord, tailWord_1482219, baseEnd_1482219] using wordTrace_append hprefix tailTrace_1482219
  have hstable : (prefixWord ++ tailWord_1482219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482219).length < 2 ^ (prefixWord ++ tailWord_1482219).sum := by decide
  have hdescent : baseEnd_1482219 < baseStart_1482219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482268 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1482268 : Nat := 118140960795 + 1482268 * 2 ^ 59
def prefixEnd_1482268 : Nat := 4983230072969 + 3 ^ 40 * 1482268 * 2
def baseEnd_1482268 : Nat := 507410628519141235555453

theorem tailTrace_1482268 : CollatzResearch.WordTrace tailWord_1482268 prefixEnd_1482268 507410628519141235555453 := by
  unfold tailWord_1482268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031377697001831032555729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36041836929335774710074305 27031377697001831032555729)
  ·
    refine ⟨20273533272751373274416797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27031377697001831032555729 20273533272751373274416797)
    ·
      refine ⟨7602574977281764977906299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20273533272751373274416797 7602574977281764977906299)
      ·
        refine ⟨11403862465922647466859449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602574977281764977906299 11403862465922647466859449)
        ·
          refine ⟨8552896849441985600144587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11403862465922647466859449 8552896849441985600144587)
          ·
            refine ⟨12829345274162978400216881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552896849441985600144587 12829345274162978400216881)
            ·
              refine ⟨9622008955622233800162661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12829345274162978400216881 9622008955622233800162661)
              ·
                refine ⟨1804126679179168837530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9622008955622233800162661 1804126679179168837530499)
                ·
                  refine ⟨2706190018768753256295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804126679179168837530499 2706190018768753256295749)
                  ·
                    refine ⟨507410628519141235555453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706190018768753256295749 507410628519141235555453)
                    ·
                      rfl

theorem cell22_1482268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1482268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482268 prefixEnd_1482268 := by exact prefixLift 1482268
  have htrace : WordTrace (prefixWord ++ tailWord_1482268) baseStart_1482268 baseEnd_1482268 := by
    simpa [prefixWord, tailWord_1482268, baseEnd_1482268] using wordTrace_append hprefix tailTrace_1482268
  have hstable : (prefixWord ++ tailWord_1482268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482268).length < 2 ^ (prefixWord ++ tailWord_1482268).sum := by decide
  have hdescent : baseEnd_1482268 < baseStart_1482268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482298 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_1482298 : Nat := 118140960795 + 1482298 * 2 ^ 59
def prefixEnd_1482298 : Nat := 4983230072969 + 3 ^ 40 * 1482298 * 2
def baseEnd_1482298 : Nat := 507420898132231157305361

theorem tailTrace_1482298 : CollatzResearch.WordTrace tailWord_1482298 prefixEnd_1482298 507420898132231157305361 := by
  unfold tailWord_1482298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515962395973744297175887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36042566389263318125802365 13515962395973744297175887)
  ·
    refine ⟨20273943593960616445763831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13515962395973744297175887 20273943593960616445763831)
    ·
      refine ⟨30410915390940924668645747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20273943593960616445763831 30410915390940924668645747)
      ·
        refine ⟨45616373086411387002968621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30410915390940924668645747 45616373086411387002968621)
        ·
          refine ⟨17106139907404270126113233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45616373086411387002968621 17106139907404270126113233)
          ·
            refine ⟨12829604930553202594584925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17106139907404270126113233 12829604930553202594584925)
            ·
              refine ⟨4811101848957450972969347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12829604930553202594584925 4811101848957450972969347)
              ·
                refine ⟨7216652773436176459454021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811101848957450972969347 7216652773436176459454021)
                ·
                  refine ⟨1353122395019283086147629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7216652773436176459454021 1353122395019283086147629)
                  ·
                    refine ⟨507420898132231157305361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353122395019283086147629 507420898132231157305361)
                    ·
                      rfl

theorem cell22_1482298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_1482298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482298 prefixEnd_1482298 := by exact prefixLift 1482298
  have htrace : WordTrace (prefixWord ++ tailWord_1482298) baseStart_1482298 baseEnd_1482298 := by
    simpa [prefixWord, tailWord_1482298, baseEnd_1482298] using wordTrace_append hprefix tailTrace_1482298
  have hstable : (prefixWord ++ tailWord_1482298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482298).length < 2 ^ (prefixWord ++ tailWord_1482298).sum := by decide
  have hdescent : baseEnd_1482298 < baseStart_1482298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482343 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1482343 : Nat := 118140960795 + 1482343 * 2 ^ 59
def prefixEnd_1482343 : Nat := 4983230072969 + 3 ^ 40 * 1482343 * 2
def baseEnd_1482343 : Nat := 507436302551866039930223

theorem tailTrace_1482343 : CollatzResearch.WordTrace tailWord_1482343 prefixEnd_1482343 507436302551866039930223 := by
  unfold tailWord_1482343
  simp only [CollatzResearch.WordTrace]
  refine ⟨54065490868731949874091683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36043660579154633249394455 54065490868731949874091683)
  ·
    refine ⟨81098236303097924811137525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54065490868731949874091683 81098236303097924811137525)
    ·
      refine ⟨7602959653415430451044143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81098236303097924811137525 7602959653415430451044143)
      ·
        refine ⟨11404439480123145676566215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602959653415430451044143 11404439480123145676566215)
        ·
          refine ⟨17106659220184718514849323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404439480123145676566215 17106659220184718514849323)
          ·
            refine ⟨25659988830277077772273985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17106659220184718514849323 25659988830277077772273985)
            ·
              refine ⟨19244991622707808329205489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25659988830277077772273985 19244991622707808329205489)
              ·
                refine ⟨14433743717030856246904117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244991622707808329205489 14433743717030856246904117)
                ·
                  refine ⟨1353163473471642773147261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14433743717030856246904117 1353163473471642773147261)
                  ·
                    refine ⟨507436302551866039930223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353163473471642773147261 507436302551866039930223)
                    ·
                      rfl

theorem cell22_1482343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1482343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482343 prefixEnd_1482343 := by exact prefixLift 1482343
  have htrace : WordTrace (prefixWord ++ tailWord_1482343) baseStart_1482343 baseEnd_1482343 := by
    simpa [prefixWord, tailWord_1482343, baseEnd_1482343] using wordTrace_append hprefix tailTrace_1482343
  have hstable : (prefixWord ++ tailWord_1482343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482343).length < 2 ^ (prefixWord ++ tailWord_1482343).sum := by decide
  have hdescent : baseEnd_1482343 < baseStart_1482343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
