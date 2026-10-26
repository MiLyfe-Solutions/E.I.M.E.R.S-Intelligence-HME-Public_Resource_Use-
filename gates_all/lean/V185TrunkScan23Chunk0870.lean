import V185TrunkScan23Chunk0869

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5148882 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5148882 : Nat := 118140960795 + 5148882 * 2 ^ 59
def prefixEnd_5148882 : Nat := 4983230072969 + 3 ^ 40 * 5148882 * 2
def baseEnd_5148882 : Nat := 2643851299283229209195729

theorem tailTrace_5148882 : CollatzResearch.WordTrace tailWord_5148882 prefixEnd_5148882 2643851299283229209195729 := by
  unfold tailWord_5148882
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948788633121836970340225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125196769688324898587573933 46948788633121836970340225)
  ·
    refine ⟨35211591474841377727755169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46948788633121836970340225 35211591474841377727755169)
    ·
      refine ⟨26408693606131033295816377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35211591474841377727755169 26408693606131033295816377)
      ·
        refine ⟨19806520204598274971862283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26408693606131033295816377 19806520204598274971862283)
        ·
          refine ⟨29709780306897412457793425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19806520204598274971862283 29709780306897412457793425)
          ·
            refine ⟨22282335230173059343345069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29709780306897412457793425 22282335230173059343345069)
            ·
              refine ⟨8355875711314897253754401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22282335230173059343345069 8355875711314897253754401)
              ·
                refine ⟨6266906783486172940315801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355875711314897253754401 6266906783486172940315801)
                ·
                  refine ⟨4700180087614629705236851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266906783486172940315801 4700180087614629705236851)
                  ·
                    refine ⟨7050270131421944557855277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700180087614629705236851 7050270131421944557855277)
                    ·
                      refine ⟨2643851299283229209195729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050270131421944557855277 2643851299283229209195729)
                      ·
                        rfl

theorem cell23_5148882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5148882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148882 prefixEnd_5148882 := by exact prefixLift 5148882
  have htrace : WordTrace (prefixWord ++ tailWord_5148882) baseStart_5148882 baseEnd_5148882 := by
    simpa [prefixWord, tailWord_5148882, baseEnd_5148882] using wordTrace_append hprefix tailTrace_5148882
  have hstable : (prefixWord ++ tailWord_5148882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148882).length < 2 ^ (prefixWord ++ tailWord_5148882).sum := by decide
  have hdescent : baseEnd_5148882 < baseStart_5148882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148899 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5148899 : Nat := 118140960795 + 5148899 * 2 ^ 59
def prefixEnd_5148899 : Nat := 4983230072969 + 3 ^ 40 * 5148899 * 2
def baseEnd_5148899 : Nat := 2643860028454355642683151

theorem tailTrace_5148899 : CollatzResearch.WordTrace tailWord_5148899 prefixEnd_5148899 2643860028454355642683151 := by
  unfold tailWord_5148899
  simp only [CollatzResearch.WordTrace]
  refine ⟨187795774573425759784729751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125197183048950506523153167 187795774573425759784729751)
  ·
    refine ⟨281693661860138639677094627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187795774573425759784729751 281693661860138639677094627)
    ·
      refine ⟨422540492790207959515641941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281693661860138639677094627 422540492790207959515641941)
      ·
        refine ⟨4951646399885249525573929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 422540492790207959515641941 4951646399885249525573929)
        ·
          refine ⟨3713734799913937144180447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951646399885249525573929 3713734799913937144180447)
          ·
            refine ⟨5570602199870905716270671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713734799913937144180447 5570602199870905716270671)
            ·
              refine ⟨8355903299806358574406007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570602199870905716270671 8355903299806358574406007)
              ·
                refine ⟨12533854949709537861609011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355903299806358574406007 12533854949709537861609011)
                ·
                  refine ⟨18800782424564306792413517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12533854949709537861609011 18800782424564306792413517)
                  ·
                    refine ⟨7050293409211615047155069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18800782424564306792413517 7050293409211615047155069)
                    ·
                      refine ⟨2643860028454355642683151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050293409211615047155069 2643860028454355642683151)
                      ·
                        rfl

theorem cell23_5148899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5148899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148899 prefixEnd_5148899 := by exact prefixLift 5148899
  have htrace : WordTrace (prefixWord ++ tailWord_5148899) baseStart_5148899 baseEnd_5148899 := by
    simpa [prefixWord, tailWord_5148899, baseEnd_5148899] using wordTrace_append hprefix tailTrace_5148899
  have hstable : (prefixWord ++ tailWord_5148899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148899).length < 2 ^ (prefixWord ++ tailWord_5148899).sum := by decide
  have hdescent : baseEnd_5148899 < baseStart_5148899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148909 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5148909 : Nat := 118140960795 + 5148909 * 2 ^ 59
def prefixEnd_5148909 : Nat := 4983230072969 + 3 ^ 40 * 5148909 * 2
def baseEnd_5148909 : Nat := 2643865163260900603558105

theorem tailTrace_5148909 : CollatzResearch.WordTrace tailWord_5148909 prefixEnd_5148909 2643865163260900603558105 := by
  unfold tailWord_5148909
  simp only [CollatzResearch.WordTrace]
  refine ⟨187796139303389531492593781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125197426202259687661729187 187796139303389531492593781)
  ·
    refine ⟨17605888059692768577430667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187796139303389531492593781 17605888059692768577430667)
    ·
      refine ⟨26408832089539152866146001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17605888059692768577430667 26408832089539152866146001)
      ·
        refine ⟨19806624067154364649609501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26408832089539152866146001 19806624067154364649609501)
        ·
          refine ⟨7427484025182886743603563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19806624067154364649609501 7427484025182886743603563)
          ·
            refine ⟨11141226037774330115405345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427484025182886743603563 11141226037774330115405345)
            ·
              refine ⟨8355919528330747586554009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141226037774330115405345 8355919528330747586554009)
              ·
                refine ⟨6266939646248060689915507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355919528330747586554009 6266939646248060689915507)
                ·
                  refine ⟨9400409469372091034873261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266939646248060689915507 9400409469372091034873261)
                  ·
                    refine ⟨3525153551014534138077473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9400409469372091034873261 3525153551014534138077473)
                    ·
                      refine ⟨2643865163260900603558105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525153551014534138077473 2643865163260900603558105)
                      ·
                        rfl

theorem cell23_5148909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5148909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148909 prefixEnd_5148909 := by exact prefixLift 5148909
  have htrace : WordTrace (prefixWord ++ tailWord_5148909) baseStart_5148909 baseEnd_5148909 := by
    simpa [prefixWord, tailWord_5148909, baseEnd_5148909] using wordTrace_append hprefix tailTrace_5148909
  have hstable : (prefixWord ++ tailWord_5148909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148909).length < 2 ^ (prefixWord ++ tailWord_5148909).sum := by decide
  have hdescent : baseEnd_5148909 < baseStart_5148909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148918 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5148918 : Nat := 118140960795 + 5148918 * 2 ^ 59
def prefixEnd_5148918 : Nat := 4983230072969 + 3 ^ 40 * 5148918 * 2
def baseEnd_5148918 : Nat := 2643869784586791068345563

theorem tailTrace_5148918 : CollatzResearch.WordTrace tailWord_5148918 prefixEnd_5148918 2643869784586791068345563 := by
  unfold tailWord_5148918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737279222522307876854463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125197645040237950686447605 11737279222522307876854463)
  ·
    refine ⟨17605918833783461815281695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11737279222522307876854463 17605918833783461815281695)
    ·
      refine ⟨26408878250675192722922543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17605918833783461815281695 26408878250675192722922543)
      ·
        refine ⟨39613317376012789084383815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26408878250675192722922543 39613317376012789084383815)
        ·
          refine ⟨59419976064019183626575723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39613317376012789084383815 59419976064019183626575723)
          ·
            refine ⟨89129964096028775439863585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59419976064019183626575723 89129964096028775439863585)
            ·
              refine ⟨66847473072021581579897689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89129964096028775439863585 66847473072021581579897689)
              ·
                refine ⟨50135604804016186184923267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66847473072021581579897689 50135604804016186184923267)
                ·
                  refine ⟨75203407206024279277384901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50135604804016186184923267 75203407206024279277384901)
                  ·
                    refine ⟨14100638851129552364509669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75203407206024279277384901 14100638851129552364509669)
                    ·
                      refine ⟨2643869784586791068345563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14100638851129552364509669 2643869784586791068345563)
                      ·
                        rfl

theorem cell23_5148918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5148918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148918 prefixEnd_5148918 := by exact prefixLift 5148918
  have htrace : WordTrace (prefixWord ++ tailWord_5148918) baseStart_5148918 baseEnd_5148918 := by
    simpa [prefixWord, tailWord_5148918, baseEnd_5148918] using wordTrace_append hprefix tailTrace_5148918
  have hstable : (prefixWord ++ tailWord_5148918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148918).length < 2 ^ (prefixWord ++ tailWord_5148918).sum := by decide
  have hdescent : baseEnd_5148918 < baseStart_5148918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148938 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_5148938 : Nat := 118140960795 + 5148938 * 2 ^ 59
def prefixEnd_5148938 : Nat := 4983230072969 + 3 ^ 40 * 5148938 * 2
def baseEnd_5148938 : Nat := 2643880054199880990095471

theorem tailTrace_5148938 : CollatzResearch.WordTrace tailWord_5148938 prefixEnd_5148938 2643880054199880990095471 := by
  unfold tailWord_5148938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46949299255071117361349867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125198131346856312963599645 46949299255071117361349867)
  ·
    refine ⟨70423948882606676042024801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46949299255071117361349867 70423948882606676042024801)
    ·
      refine ⟨52817961661955007031518601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70423948882606676042024801 52817961661955007031518601)
      ·
        refine ⟨39613471246466255273638951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52817961661955007031518601 39613471246466255273638951)
        ·
          refine ⟨59420206869699382910458427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39613471246466255273638951 59420206869699382910458427)
          ·
            refine ⟨89130310304549074365687641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59420206869699382910458427 89130310304549074365687641)
            ·
              refine ⟨66847732728411805774265731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89130310304549074365687641 66847732728411805774265731)
              ·
                refine ⟨100271599092617708661398597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66847732728411805774265731 100271599092617708661398597)
                ·
                  refine ⟨18800924829865820374012237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100271599092617708661398597 18800924829865820374012237)
                  ·
                    refine ⟨7050346811199682640254589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18800924829865820374012237 7050346811199682640254589)
                    ·
                      refine ⟨2643880054199880990095471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050346811199682640254589 2643880054199880990095471)
                      ·
                        rfl

theorem cell23_5148938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_5148938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148938 prefixEnd_5148938 := by exact prefixLift 5148938
  have htrace : WordTrace (prefixWord ++ tailWord_5148938) baseStart_5148938 baseEnd_5148938 := by
    simpa [prefixWord, tailWord_5148938, baseEnd_5148938] using wordTrace_append hprefix tailTrace_5148938
  have hstable : (prefixWord ++ tailWord_5148938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148938).length < 2 ^ (prefixWord ++ tailWord_5148938).sum := by decide
  have hdescent : baseEnd_5148938 < baseStart_5148938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148996 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 5]
def baseStart_5148996 : Nat := 118140960795 + 5148996 * 2 ^ 59
def prefixEnd_5148996 : Nat := 4983230072969 + 3 ^ 40 * 5148996 * 2
def baseEnd_5148996 : Nat := 293767759564204640352245

theorem tailTrace_5148996 : CollatzResearch.WordTrace tailWord_5148996 prefixEnd_5148996 293767759564204640352245 := by
  unfold tailWord_5148996
  simp only [CollatzResearch.WordTrace]
  refine ⟨93899656227037172675505421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125199541636049563567340561 93899656227037172675505421)
  ·
    refine ⟨35212371085138939753314533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93899656227037172675505421 35212371085138939753314533)
    ·
      refine ⟨6602319578463551203746475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35212371085138939753314533 6602319578463551203746475)
      ·
        refine ⟨9903479367695326805619713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602319578463551203746475 9903479367695326805619713)
        ·
          refine ⟨7427609525771495104214785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903479367695326805619713 7427609525771495104214785)
          ·
            refine ⟨5570707144328621328161089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427609525771495104214785 5570707144328621328161089)
            ·
              refine ⟨4178030358246465996120817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570707144328621328161089 4178030358246465996120817)
              ·
                refine ⟨3133522768684849497090613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178030358246465996120817 3133522768684849497090613)
                ·
                  refine ⟨293767759564204640352245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133522768684849497090613 293767759564204640352245)
                  ·
                    rfl

theorem cell23_5148996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_5148996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148996 prefixEnd_5148996 := by exact prefixLift 5148996
  have htrace : WordTrace (prefixWord ++ tailWord_5148996) baseStart_5148996 baseEnd_5148996 := by
    simpa [prefixWord, tailWord_5148996, baseEnd_5148996] using wordTrace_append hprefix tailTrace_5148996
  have hstable : (prefixWord ++ tailWord_5148996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148996).length < 2 ^ (prefixWord ++ tailWord_5148996).sum := by decide
  have hdescent : baseEnd_5148996 < baseStart_5148996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149012 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_5149012 : Nat := 118140960795 + 5149012 * 2 ^ 59
def prefixEnd_5149012 : Nat := 4983230072969 + 3 ^ 40 * 5149012 * 2
def baseEnd_5149012 : Nat := 2643918051768313700570131

theorem tailTrace_5149012 : CollatzResearch.WordTrace tailWord_5149012 prefixEnd_5149012 2643918051768313700570131 := by
  unfold tailWord_5149012
  simp only [CollatzResearch.WordTrace]
  refine ⟨93899948011008190041796645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125199930681344253389062193 93899948011008190041796645)
  ·
    refine ⟨17606240252064035632836871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93899948011008190041796645 17606240252064035632836871)
    ·
      refine ⟨26409360378096053449255307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17606240252064035632836871 26409360378096053449255307)
      ·
        refine ⟨39614040567144080173882961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26409360378096053449255307 39614040567144080173882961)
        ·
          refine ⟨29710530425358060130412221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39614040567144080173882961 29710530425358060130412221)
          ·
            refine ⟨11141448909509272548904583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29710530425358060130412221 11141448909509272548904583)
            ·
              refine ⟨16712173364263908823356875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11141448909509272548904583 16712173364263908823356875)
              ·
                refine ⟨25068260046395863235035313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16712173364263908823356875 25068260046395863235035313)
                ·
                  refine ⟨18801195034796897426276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25068260046395863235035313 18801195034796897426276485)
                  ·
                    refine ⟨3525224069024418267426841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18801195034796897426276485 3525224069024418267426841)
                    ·
                      refine ⟨2643918051768313700570131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525224069024418267426841 2643918051768313700570131)
                      ·
                        rfl

theorem cell23_5149012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_5149012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149012 prefixEnd_5149012 := by exact prefixLift 5149012
  have htrace : WordTrace (prefixWord ++ tailWord_5149012) baseStart_5149012 baseEnd_5149012 := by
    simpa [prefixWord, tailWord_5149012, baseEnd_5149012] using wordTrace_append hprefix tailTrace_5149012
  have hstable : (prefixWord ++ tailWord_5149012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149012).length < 2 ^ (prefixWord ++ tailWord_5149012).sum := by decide
  have hdescent : baseEnd_5149012 < baseStart_5149012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149032 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5149032 : Nat := 118140960795 + 5149032 * 2 ^ 59
def prefixEnd_5149032 : Nat := 4983230072969 + 3 ^ 40 * 5149032 * 2
def baseEnd_5149032 : Nat := 2643928321381403622320039

theorem tailTrace_5149032 : CollatzResearch.WordTrace tailWord_5149032 prefixEnd_5149032 2643928321381403622320039 := by
  unfold tailWord_5149032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93900312740971961749660675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125200416987962615666214233 93900312740971961749660675)
  ·
    refine ⟨140850469111457942624491013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93900312740971961749660675 140850469111457942624491013)
    ·
      refine ⟨26409462958398364242092065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140850469111457942624491013 26409462958398364242092065)
      ·
        refine ⟨19807097218798773181569049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26409462958398364242092065 19807097218798773181569049)
        ·
          refine ⟨14855322914099079886176787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19807097218798773181569049 14855322914099079886176787)
          ·
            refine ⟨22282984371148619829265181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14855322914099079886176787 22282984371148619829265181)
            ·
              refine ⟨8356119139180732435974443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22282984371148619829265181 8356119139180732435974443)
              ·
                refine ⟨12534178708771098653961665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356119139180732435974443 12534178708771098653961665)
                ·
                  refine ⟨9400634031578323990471249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12534178708771098653961665 9400634031578323990471249)
                  ·
                    refine ⟨7050475523683742992853437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9400634031578323990471249 7050475523683742992853437)
                    ·
                      refine ⟨2643928321381403622320039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050475523683742992853437 2643928321381403622320039)
                      ·
                        rfl

theorem cell23_5149032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5149032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149032 prefixEnd_5149032 := by exact prefixLift 5149032
  have htrace : WordTrace (prefixWord ++ tailWord_5149032) baseStart_5149032 baseEnd_5149032 := by
    simpa [prefixWord, tailWord_5149032, baseEnd_5149032] using wordTrace_append hprefix tailTrace_5149032
  have hstable : (prefixWord ++ tailWord_5149032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149032).length < 2 ^ (prefixWord ++ tailWord_5149032).sum := by decide
  have hdescent : baseEnd_5149032 < baseStart_5149032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149082 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_5149082 : Nat := 118140960795 + 5149082 * 2 ^ 59
def prefixEnd_5149082 : Nat := 4983230072969 + 3 ^ 40 * 5149082 * 2
def baseEnd_5149082 : Nat := 881317998471376142231603

theorem tailTrace_5149082 : CollatzResearch.WordTrace tailWord_5149082 prefixEnd_5149082 881317998471376142231603 := by
  unfold tailWord_5149082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46950612282940695509660375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125201632754508521359094333 46950612282940695509660375)
  ·
    refine ⟨70425918424411043264490563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46950612282940695509660375 70425918424411043264490563)
    ·
      refine ⟨105638877636616564896735845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70425918424411043264490563 105638877636616564896735845)
      ·
        refine ⟨19807289556865605918137971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105638877636616564896735845 19807289556865605918137971)
        ·
          refine ⟨29710934335298408877206957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19807289556865605918137971 29710934335298408877206957)
          ·
            refine ⟨11141600375736903328952609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29710934335298408877206957 11141600375736903328952609)
            ·
              refine ⟨8356200281802677496714457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141600375736903328952609 8356200281802677496714457)
              ·
                refine ⟨6267150211352008122535843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8356200281802677496714457 6267150211352008122535843)
                ·
                  refine ⟨9400725317028012183803765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267150211352008122535843 9400725317028012183803765)
                  ·
                    refine ⟨881317998471376142231603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9400725317028012183803765 881317998471376142231603)
                    ·
                      rfl

theorem cell23_5149082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_5149082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149082 prefixEnd_5149082 := by exact prefixLift 5149082
  have htrace : WordTrace (prefixWord ++ tailWord_5149082) baseStart_5149082 baseEnd_5149082 := by
    simpa [prefixWord, tailWord_5149082, baseEnd_5149082] using wordTrace_append hprefix tailTrace_5149082
  have hstable : (prefixWord ++ tailWord_5149082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149082).length < 2 ^ (prefixWord ++ tailWord_5149082).sum := by decide
  have hdescent : baseEnd_5149082 < baseStart_5149082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149105 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5149105 : Nat := 118140960795 + 5149105 * 2 ^ 59
def prefixEnd_5149105 : Nat := 4983230072969 + 3 ^ 40 * 5149105 * 2
def baseEnd_5149105 : Nat := 2643965805469181836707203

theorem tailTrace_5149105 : CollatzResearch.WordTrace tailWord_5149105 prefixEnd_5149105 2643965805469181836707203 := by
  unfold tailWord_5149105
  simp only [CollatzResearch.WordTrace]
  refine ⟨187803288010679456966728769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125202192007119637977819179 187803288010679456966728769)
  ·
    refine ⟨140852466008009592725046577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187803288010679456966728769 140852466008009592725046577)
    ·
      refine ⟨105639349506007194543784933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140852466008009592725046577 105639349506007194543784933)
      ·
        refine ⟨19807378032376348976959675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105639349506007194543784933 19807378032376348976959675)
        ·
          refine ⟨29711067048564523465439513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19807378032376348976959675 29711067048564523465439513)
          ·
            refine ⟨22283300286423392599079635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29711067048564523465439513 22283300286423392599079635)
            ·
              refine ⟨33424950429635088898619453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22283300286423392599079635 33424950429635088898619453)
              ·
                refine ⟨12534356411113158336982295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33424950429635088898619453 12534356411113158336982295)
                ·
                  refine ⟨18801534616669737505473443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12534356411113158336982295 18801534616669737505473443)
                  ·
                    refine ⟨28202301925004606258210165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18801534616669737505473443 28202301925004606258210165)
                    ·
                      refine ⟨2643965805469181836707203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28202301925004606258210165 2643965805469181836707203)
                      ·
                        rfl

theorem cell23_5149105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5149105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149105 prefixEnd_5149105 := by exact prefixLift 5149105
  have htrace : WordTrace (prefixWord ++ tailWord_5149105) baseStart_5149105 baseEnd_5149105 := by
    simpa [prefixWord, tailWord_5149105, baseEnd_5149105] using wordTrace_append hprefix tailTrace_5149105
  have hstable : (prefixWord ++ tailWord_5149105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149105).length < 2 ^ (prefixWord ++ tailWord_5149105).sum := by decide
  have hdescent : baseEnd_5149105 < baseStart_5149105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149135 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_5149135 : Nat := 118140960795 + 5149135 * 2 ^ 59
def prefixEnd_5149135 : Nat := 4983230072969 + 3 ^ 40 * 5149135 * 2
def baseEnd_5149135 : Nat := 2643981209888816719332065

theorem tailTrace_5149135 : CollatzResearch.WordTrace tailWord_5149135 prefixEnd_5149135 2643981209888816719332065 := by
  unfold tailWord_5149135
  simp only [CollatzResearch.WordTrace]
  refine ⟨187804382200570772090320859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125202921467047181393547239 187804382200570772090320859)
  ·
    refine ⟨281706573300856158135481289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187804382200570772090320859 281706573300856158135481289)
    ·
      refine ⟨211279929975642118601610967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281706573300856158135481289 211279929975642118601610967)
      ·
        refine ⟨316919894963463177902416451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211279929975642118601610967 316919894963463177902416451)
        ·
          refine ⟨475379842445194766853624677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316919894963463177902416451 475379842445194766853624677)
          ·
            refine ⟨89133720458474018785054627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475379842445194766853624677 89133720458474018785054627)
            ·
              refine ⟨133700580687711028177581941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89133720458474018785054627 133700580687711028177581941)
              ·
                refine ⟨12534429439472908891648307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133700580687711028177581941 12534429439472908891648307)
                ·
                  refine ⟨18801644159209363337472461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12534429439472908891648307 18801644159209363337472461)
                  ·
                    refine ⟨7050616559703511251552173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18801644159209363337472461 7050616559703511251552173)
                    ·
                      refine ⟨2643981209888816719332065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050616559703511251552173 2643981209888816719332065)
                      ·
                        rfl

theorem cell23_5149135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_5149135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149135 prefixEnd_5149135 := by exact prefixLift 5149135
  have htrace : WordTrace (prefixWord ++ tailWord_5149135) baseStart_5149135 baseEnd_5149135 := by
    simpa [prefixWord, tailWord_5149135, baseEnd_5149135] using wordTrace_append hprefix tailTrace_5149135
  have hstable : (prefixWord ++ tailWord_5149135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149135).length < 2 ^ (prefixWord ++ tailWord_5149135).sum := by decide
  have hdescent : baseEnd_5149135 < baseStart_5149135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149169 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_5149169 : Nat := 118140960795 + 5149169 * 2 ^ 59
def prefixEnd_5149169 : Nat := 4983230072969 + 3 ^ 40 * 5149169 * 2
def baseEnd_5149169 : Nat := 2643998668231069586306909

theorem tailTrace_5149169 : CollatzResearch.WordTrace tailWord_5149169 prefixEnd_5149169 2643998668231069586306909 := by
  unfold tailWord_5149169
  simp only [CollatzResearch.WordTrace]
  refine ⟨187805622282447595897058561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125203748188298397264705707 187805622282447595897058561)
  ·
    refine ⟨140854216711835696922793921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187805622282447595897058561 140854216711835696922793921)
    ·
      refine ⟨105640662533876772692095441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140854216711835696922793921 105640662533876772692095441)
      ·
        refine ⟨79230496900407579519071581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105640662533876772692095441 79230496900407579519071581)
        ·
          refine ⟨29711436337652842319651843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79230496900407579519071581 29711436337652842319651843)
          ·
            refine ⟨44567154506479263479477765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29711436337652842319651843 44567154506479263479477765)
            ·
              refine ⟨8356341469964861902402081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44567154506479263479477765 8356341469964861902402081)
              ·
                refine ⟨6267256102473646426801561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8356341469964861902402081 6267256102473646426801561)
                ·
                  refine ⟨4700442076855234820101171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6267256102473646426801561 4700442076855234820101171)
                  ·
                    refine ⟨7050663115282852230151757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700442076855234820101171 7050663115282852230151757)
                    ·
                      refine ⟨2643998668231069586306909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050663115282852230151757 2643998668231069586306909)
                      ·
                        rfl

theorem cell23_5149169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_5149169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149169 prefixEnd_5149169 := by exact prefixLift 5149169
  have htrace : WordTrace (prefixWord ++ tailWord_5149169) baseStart_5149169 baseEnd_5149169 := by
    simpa [prefixWord, tailWord_5149169, baseEnd_5149169] using wordTrace_append hprefix tailTrace_5149169
  have hstable : (prefixWord ++ tailWord_5149169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149169).length < 2 ^ (prefixWord ++ tailWord_5149169).sum := by decide
  have hdescent : baseEnd_5149169 < baseStart_5149169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149185 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5149185 : Nat := 118140960795 + 5149185 * 2 ^ 59
def prefixEnd_5149185 : Nat := 4983230072969 + 3 ^ 40 * 5149185 * 2
def baseEnd_5149185 : Nat := 881335627973847174568945

theorem tailTrace_5149185 : CollatzResearch.WordTrace tailWord_5149185 prefixEnd_5149185 881335627973847174568945 := by
  unfold tailWord_5149185
  simp only [CollatzResearch.WordTrace]
  refine ⟨187806205850389630629641009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125204137233593087086427339 187806205850389630629641009)
  ·
    refine ⟨140854654387792222972230757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187806205850389630629641009 140854654387792222972230757)
    ·
      refine ⟨26410247697711041807293267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140854654387792222972230757 26410247697711041807293267)
      ·
        refine ⟨39615371546566562710939901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26410247697711041807293267 39615371546566562710939901)
        ·
          refine ⟨14855764329962461016602463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39615371546566562710939901 14855764329962461016602463)
          ·
            refine ⟨22283646494943691524903695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14855764329962461016602463 22283646494943691524903695)
            ·
              refine ⟨33425469742415537287355543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22283646494943691524903695 33425469742415537287355543)
              ·
                refine ⟨50138204613623305931033315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33425469742415537287355543 50138204613623305931033315)
                ·
                  refine ⟨75207306920434958896549973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50138204613623305931033315 75207306920434958896549973)
                  ·
                    refine ⟨881335627973847174568945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75207306920434958896549973 881335627973847174568945)
                    ·
                      rfl

theorem cell23_5149185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5149185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149185 prefixEnd_5149185 := by exact prefixLift 5149185
  have htrace : WordTrace (prefixWord ++ tailWord_5149185) baseStart_5149185 baseEnd_5149185 := by
    simpa [prefixWord, tailWord_5149185, baseEnd_5149185] using wordTrace_append hprefix tailTrace_5149185
  have hstable : (prefixWord ++ tailWord_5149185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149185).length < 2 ^ (prefixWord ++ tailWord_5149185).sum := by decide
  have hdescent : baseEnd_5149185 < baseStart_5149185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149186 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5149186 : Nat := 118140960795 + 5149186 * 2 ^ 59
def prefixEnd_5149186 : Nat := 4983230072969 + 3 ^ 40 * 5149186 * 2
def baseEnd_5149186 : Nat := 2644007397402196019794331

theorem tailTrace_5149186 : CollatzResearch.WordTrace tailWord_5149186 prefixEnd_5149186 2644007397402196019794331 := by
  unfold tailWord_5149186
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951560580846501950106853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125204161548924005200284941 46951560580846501950106853)
  ·
    refine ⟨8803417608908719115645035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46951560580846501950106853 8803417608908719115645035)
    ·
      refine ⟨13205126413363078673467553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803417608908719115645035 13205126413363078673467553)
      ·
        refine ⟨9903844810022309005100665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13205126413363078673467553 9903844810022309005100665)
        ·
          refine ⟨7427883607516731753825499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903844810022309005100665 7427883607516731753825499)
          ·
            refine ⟨11141825411275097630738249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427883607516731753825499 11141825411275097630738249)
            ·
              refine ⟨8356369058456323223053687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141825411275097630738249 8356369058456323223053687)
              ·
                refine ⟨12534553587684484834580531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356369058456323223053687 12534553587684484834580531)
                ·
                  refine ⟨18801830381526727251870797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12534553587684484834580531 18801830381526727251870797)
                  ·
                    refine ⟨7050686393072522719451549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18801830381526727251870797 7050686393072522719451549)
                    ·
                      refine ⟨2644007397402196019794331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050686393072522719451549 2644007397402196019794331)
                      ·
                        rfl

theorem cell23_5149186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5149186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149186 prefixEnd_5149186 := by exact prefixLift 5149186
  have htrace : WordTrace (prefixWord ++ tailWord_5149186) baseStart_5149186 baseEnd_5149186 := by
    simpa [prefixWord, tailWord_5149186, baseEnd_5149186] using wordTrace_append hprefix tailTrace_5149186
  have hstable : (prefixWord ++ tailWord_5149186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149186).length < 2 ^ (prefixWord ++ tailWord_5149186).sum := by decide
  have hdescent : baseEnd_5149186 < baseStart_5149186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149205 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_5149205 : Nat := 118140960795 + 5149205 * 2 ^ 59
def prefixEnd_5149205 : Nat := 4983230072969 + 3 ^ 40 * 5149205 * 2
def baseEnd_5149205 : Nat := 2644017153534631445456743

theorem tailTrace_5149205 : CollatzResearch.WordTrace tailWord_5149205 prefixEnd_5149205 2644017153534631445456743 := by
  unfold tailWord_5149205
  simp only [CollatzResearch.WordTrace]
  refine ⟨187806935310317174045369069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125204623540211449363579379 187806935310317174045369069)
  ·
    refine ⟨70427600741368940267013401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187806935310317174045369069 70427600741368940267013401)
    ·
      refine ⟨52820700556026705200260051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70427600741368940267013401 52820700556026705200260051)
      ·
        refine ⟨79231050834040057800390077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52820700556026705200260051 79231050834040057800390077)
        ·
          refine ⟨29711644062765021675146279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79231050834040057800390077 29711644062765021675146279)
          ·
            refine ⟨44567466094147532512719419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29711644062765021675146279 44567466094147532512719419)
            ·
              refine ⟨66851199141221298769079129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44567466094147532512719419 66851199141221298769079129)
              ·
                refine ⟨50138399355915974076809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66851199141221298769079129 50138399355915974076809347)
                ·
                  refine ⟨75207599033873961115214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50138399355915974076809347 75207599033873961115214021)
                  ·
                    refine ⟨14101424818851367709102629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75207599033873961115214021 14101424818851367709102629)
                    ·
                      refine ⟨2644017153534631445456743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14101424818851367709102629 2644017153534631445456743)
                      ·
                        rfl

theorem cell23_5149205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_5149205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149205 prefixEnd_5149205 := by exact prefixLift 5149205
  have htrace : WordTrace (prefixWord ++ tailWord_5149205) baseStart_5149205 baseEnd_5149205 := by
    simpa [prefixWord, tailWord_5149205, baseEnd_5149205] using wordTrace_append hprefix tailTrace_5149205
  have hstable : (prefixWord ++ tailWord_5149205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149205).length < 2 ^ (prefixWord ++ tailWord_5149205).sum := by decide
  have hdescent : baseEnd_5149205 < baseStart_5149205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149213 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5149213 : Nat := 118140960795 + 5149213 * 2 ^ 59
def prefixEnd_5149213 : Nat := 4983230072969 + 3 ^ 40 * 5149213 * 2
def baseEnd_5149213 : Nat := 2644021261379867414156707

theorem tailTrace_5149213 : CollatzResearch.WordTrace tailWord_5149213 prefixEnd_5149213 2644021261379867414156707 := by
  unfold tailWord_5149213
  simp only [CollatzResearch.WordTrace]
  refine ⟨187807227094288191411660293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125204818062858794274440195 187807227094288191411660293)
  ·
    refine ⟨35213855080179035889686305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187807227094288191411660293 35213855080179035889686305)
    ·
      refine ⟨26410391310134276917264729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35213855080179035889686305 26410391310134276917264729)
      ·
        refine ⟨19807793482600707687948547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26410391310134276917264729 19807793482600707687948547)
        ·
          refine ⟨29711690223901061531922821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19807793482600707687948547 29711690223901061531922821)
          ·
            refine ⟨5570941916981449037235529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29711690223901061531922821 5570941916981449037235529)
            ·
              refine ⟨4178206437736086777926647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570941916981449037235529 4178206437736086777926647)
              ·
                refine ⟨6267309656604130166889971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178206437736086777926647 6267309656604130166889971)
                ·
                  refine ⟨9400964484906195250334957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267309656604130166889971 9400964484906195250334957)
                  ·
                    refine ⟨3525361681839823218875609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9400964484906195250334957 3525361681839823218875609)
                    ·
                      refine ⟨2644021261379867414156707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525361681839823218875609 2644021261379867414156707)
                      ·
                        rfl

theorem cell23_5149213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5149213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149213 prefixEnd_5149213 := by exact prefixLift 5149213
  have htrace : WordTrace (prefixWord ++ tailWord_5149213) baseStart_5149213 baseEnd_5149213 := by
    simpa [prefixWord, tailWord_5149213, baseEnd_5149213] using wordTrace_append hprefix tailTrace_5149213
  have hstable : (prefixWord ++ tailWord_5149213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149213).length < 2 ^ (prefixWord ++ tailWord_5149213).sum := by decide
  have hdescent : baseEnd_5149213 < baseStart_5149213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149220 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5149220 : Nat := 118140960795 + 5149220 * 2 ^ 59
def prefixEnd_5149220 : Nat := 4983230072969 + 3 ^ 40 * 5149220 * 2
def baseEnd_5149220 : Nat := 2644024855744448886769175

theorem tailTrace_5149220 : CollatzResearch.WordTrace tailWord_5149220 prefixEnd_5149220 2644024855744448886769175 := by
  unfold tailWord_5149220
  simp only [CollatzResearch.WordTrace]
  refine ⟨93903741202631415803582557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125204988270175221071443409 93903741202631415803582557)
  ·
    refine ⟨35213902950986780926343459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93903741202631415803582557 35213902950986780926343459)
    ·
      refine ⟨52820854426480171389515189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35213902950986780926343459 52820854426480171389515189)
      ·
        refine ⟨4951955102482516067767049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52820854426480171389515189 4951955102482516067767049)
        ·
          refine ⟨3713966326861887050825287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951955102482516067767049 3713966326861887050825287)
          ·
            refine ⟨5570949490292830576237931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713966326861887050825287 5570949490292830576237931)
            ·
              refine ⟨8356424235439245864356897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570949490292830576237931 8356424235439245864356897)
              ·
                refine ⟨6267318176579434398267673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8356424235439245864356897 6267318176579434398267673)
                ·
                  refine ⟨4700488632434575798700755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6267318176579434398267673 4700488632434575798700755)
                  ·
                    refine ⟨7050732948651863698051133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700488632434575798700755 7050732948651863698051133)
                    ·
                      refine ⟨2644024855744448886769175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050732948651863698051133 2644024855744448886769175)
                      ·
                        rfl

theorem cell23_5149220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5149220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149220 prefixEnd_5149220 := by exact prefixLift 5149220
  have htrace : WordTrace (prefixWord ++ tailWord_5149220) baseStart_5149220 baseEnd_5149220 := by
    simpa [prefixWord, tailWord_5149220, baseEnd_5149220] using wordTrace_append hprefix tailTrace_5149220
  have hstable : (prefixWord ++ tailWord_5149220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149220).length < 2 ^ (prefixWord ++ tailWord_5149220).sum := by decide
  have hdescent : baseEnd_5149220 < baseStart_5149220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149226 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5149226 : Nat := 118140960795 + 5149226 * 2 ^ 59
def prefixEnd_5149226 : Nat := 4983230072969 + 3 ^ 40 * 5149226 * 2
def baseEnd_5149226 : Nat := 2644027936628375863294147

theorem tailTrace_5149226 : CollatzResearch.WordTrace tailWord_5149226 prefixEnd_5149226 2644027936628375863294147 := by
  unfold tailWord_5149226
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951925310810273657970883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125205134162160729754589021 46951925310810273657970883)
  ·
    refine ⟨70427887966215410486956325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46951925310810273657970883 70427887966215410486956325)
    ·
      refine ⟨13205228993665389466304311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70427887966215410486956325 13205228993665389466304311)
      ·
        refine ⟨19807843490498084199456467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13205228993665389466304311 19807843490498084199456467)
        ·
          refine ⟨29711765235747126299184701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19807843490498084199456467 29711765235747126299184701)
          ·
            refine ⟨11141911963405172362194263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29711765235747126299184701 11141911963405172362194263)
            ·
              refine ⟨16712867945107758543291395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11141911963405172362194263 16712867945107758543291395)
              ·
                refine ⟨25069301917661637814937093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16712867945107758543291395 25069301917661637814937093)
                ·
                  refine ⟨4700494109561557090300705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25069301917661637814937093 4700494109561557090300705)
                  ·
                    refine ⟨3525370582171167817725529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700494109561557090300705 3525370582171167817725529)
                    ·
                      refine ⟨2644027936628375863294147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525370582171167817725529 2644027936628375863294147)
                      ·
                        rfl

theorem cell23_5149226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5149226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149226 prefixEnd_5149226 := by exact prefixLift 5149226
  have htrace : WordTrace (prefixWord ++ tailWord_5149226) baseStart_5149226 baseEnd_5149226 := by
    simpa [prefixWord, tailWord_5149226, baseEnd_5149226] using wordTrace_append hprefix tailTrace_5149226
  have hstable : (prefixWord ++ tailWord_5149226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149226).length < 2 ^ (prefixWord ++ tailWord_5149226).sum := by decide
  have hdescent : baseEnd_5149226 < baseStart_5149226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149232 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 5]
def baseStart_5149232 : Nat := 118140960795 + 5149232 * 2 ^ 59
def prefixEnd_5149232 : Nat := 4983230072969 + 3 ^ 40 * 5149232 * 2
def baseEnd_5149232 : Nat := 293781224168033648868791

theorem tailTrace_5149232 : CollatzResearch.WordTrace tailWord_5149232 prefixEnd_5149232 293781224168033648868791 := by
  unfold tailWord_5149232
  simp only [CollatzResearch.WordTrace]
  refine ⟨93903960040609678828300975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125205280054146238437734633 93903960040609678828300975)
  ·
    refine ⟨140855940060914518242451463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93903960040609678828300975 140855940060914518242451463)
    ·
      refine ⟨211283910091371777363677195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140855940060914518242451463 211283910091371777363677195)
      ·
        refine ⟨316925865137057666045515793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211283910091371777363677195 316925865137057666045515793)
        ·
          refine ⟨237694398852793249534136845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316925865137057666045515793 237694398852793249534136845)
          ·
            refine ⟨89135399569797468575301317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237694398852793249534136845 89135399569797468575301317)
            ·
              refine ⟨16712887419337025357868997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89135399569797468575301317 16712887419337025357868997)
              ·
                refine ⟨3133666391125692254600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16712887419337025357868997 3133666391125692254600437)
                ·
                  refine ⟨293781224168033648868791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133666391125692254600437 293781224168033648868791)
                  ·
                    rfl

theorem cell23_5149232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 5].length) (baseStart_5149232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149232 prefixEnd_5149232 := by exact prefixLift 5149232
  have htrace : WordTrace (prefixWord ++ tailWord_5149232) baseStart_5149232 baseEnd_5149232 := by
    simpa [prefixWord, tailWord_5149232, baseEnd_5149232] using wordTrace_append hprefix tailTrace_5149232
  have hstable : (prefixWord ++ tailWord_5149232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149232).length < 2 ^ (prefixWord ++ tailWord_5149232).sum := by decide
  have hdescent : baseEnd_5149232 < baseStart_5149232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149242 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_5149242 : Nat := 118140960795 + 5149242 * 2 ^ 59
def prefixEnd_5149242 : Nat := 4983230072969 + 3 ^ 40 * 5149242 * 2
def baseEnd_5149242 : Nat := 2644036152318847800694073

theorem tailTrace_5149242 : CollatzResearch.WordTrace tailWord_5149242 prefixEnd_5149242 2644036152318847800694073 := by
  unfold tailWord_5149242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46952071202795782341116495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125205523207455419576310653 46952071202795782341116495)
  ·
    refine ⟨70428106804193673511674743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46952071202795782341116495 70428106804193673511674743)
    ·
      refine ⟨105642160206290510267512115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70428106804193673511674743 105642160206290510267512115)
      ·
        refine ⟨158463240309435765401268173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105642160206290510267512115 158463240309435765401268173)
        ·
          refine ⟨59423715116038412025475565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158463240309435765401268173 59423715116038412025475565)
          ·
            refine ⟨22283893168514404509553337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59423715116038412025475565 22283893168514404509553337)
            ·
              refine ⟨16712919876385803382165003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22283893168514404509553337 16712919876385803382165003)
              ·
                refine ⟨25069379814578705073247505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16712919876385803382165003 25069379814578705073247505)
                ·
                  refine ⟨18802034860934028804935629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25069379814578705073247505 18802034860934028804935629)
                  ·
                    refine ⟨7050763072850260801850861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18802034860934028804935629 7050763072850260801850861)
                    ·
                      refine ⟨2644036152318847800694073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050763072850260801850861 2644036152318847800694073)
                      ·
                        rfl

theorem cell23_5149242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_5149242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149242 prefixEnd_5149242 := by exact prefixLift 5149242
  have htrace : WordTrace (prefixWord ++ tailWord_5149242) baseStart_5149242 baseEnd_5149242 := by
    simpa [prefixWord, tailWord_5149242, baseEnd_5149242] using wordTrace_append hprefix tailTrace_5149242
  have hstable : (prefixWord ++ tailWord_5149242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149242).length < 2 ^ (prefixWord ++ tailWord_5149242).sum := by decide
  have hdescent : baseEnd_5149242 < baseStart_5149242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149295 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_5149295 : Nat := 118140960795 + 5149295 * 2 ^ 59
def prefixEnd_5149295 : Nat := 4983230072969 + 3 ^ 40 * 5149295 * 2
def baseEnd_5149295 : Nat := 2644063366793536093331329

theorem tailTrace_5149295 : CollatzResearch.WordTrace tailWord_5149295 prefixEnd_5149295 2644063366793536093331329 := by
  unfold tailWord_5149295
  simp only [CollatzResearch.WordTrace]
  refine ⟨187810217879991119416145339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125206811919994079610763559 187810217879991119416145339)
  ·
    refine ⟨281715326819986679124218009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187810217879991119416145339 281715326819986679124218009)
    ·
      refine ⟨211286495114990009343163507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281715326819986679124218009 211286495114990009343163507)
      ·
        refine ⟨316929742672485014014745261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211286495114990009343163507 316929742672485014014745261)
        ·
          refine ⟨118848653502181880255529473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316929742672485014014745261 118848653502181880255529473)
          ·
            refine ⟨89136490126636410191647105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118848653502181880255529473 89136490126636410191647105)
            ·
              refine ⟨66852367594977307643735329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89136490126636410191647105 66852367594977307643735329)
              ·
                refine ⟨50139275696232980732801497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66852367594977307643735329 50139275696232980732801497)
                ·
                  refine ⟨37604456772174735549601123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50139275696232980732801497 37604456772174735549601123)
                  ·
                    refine ⟨56406685158262103324401685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37604456772174735549601123 56406685158262103324401685)
                    ·
                      refine ⟨2644063366793536093331329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56406685158262103324401685 2644063366793536093331329)
                      ·
                        rfl

theorem cell23_5149295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_5149295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149295 prefixEnd_5149295 := by exact prefixLift 5149295
  have htrace : WordTrace (prefixWord ++ tailWord_5149295) baseStart_5149295 baseEnd_5149295 := by
    simpa [prefixWord, tailWord_5149295, baseEnd_5149295] using wordTrace_append hprefix tailTrace_5149295
  have hstable : (prefixWord ++ tailWord_5149295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149295).length < 2 ^ (prefixWord ++ tailWord_5149295).sum := by decide
  have hdescent : baseEnd_5149295 < baseStart_5149295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149319 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_5149319 : Nat := 118140960795 + 5149319 * 2 ^ 59
def prefixEnd_5149319 : Nat := 4983230072969 + 3 ^ 40 * 5149319 * 2
def baseEnd_5149319 : Nat := 2644075690329243999431219

theorem tailTrace_5149319 : CollatzResearch.WordTrace tailWord_5149319 prefixEnd_5149319 2644075690329243999431219 := by
  unfold tailWord_5149319
  simp only [CollatzResearch.WordTrace]
  refine ⟨187811093231904171515019011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125207395487936114343346007 187811093231904171515019011)
  ·
    refine ⟨281716639847856257272528517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187811093231904171515019011 281716639847856257272528517)
    ·
      refine ⟨52821869971473048238599097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281716639847856257272528517 52821869971473048238599097)
      ·
        refine ⟨39616402478604786178949323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52821869971473048238599097 39616402478604786178949323)
        ·
          refine ⟨59424603717907179268423985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39616402478604786178949323 59424603717907179268423985)
          ·
            refine ⟨44568452788430384451317989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59424603717907179268423985 44568452788430384451317989)
            ·
              refine ⟨8356584897830697084622123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44568452788430384451317989 8356584897830697084622123)
              ·
                refine ⟨12534877346746045626933185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356584897830697084622123 12534877346746045626933185)
                ·
                  refine ⟨9401158010059534220199889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12534877346746045626933185 9401158010059534220199889)
                  ·
                    refine ⟨7050868507544650665149917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9401158010059534220199889 7050868507544650665149917)
                    ·
                      refine ⟨2644075690329243999431219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050868507544650665149917 2644075690329243999431219)
                      ·
                        rfl

theorem cell23_5149319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_5149319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149319 prefixEnd_5149319 := by exact prefixLift 5149319
  have htrace : WordTrace (prefixWord ++ tailWord_5149319) baseStart_5149319 baseEnd_5149319 := by
    simpa [prefixWord, tailWord_5149319, baseEnd_5149319] using wordTrace_append hprefix tailTrace_5149319
  have hstable : (prefixWord ++ tailWord_5149319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149319).length < 2 ^ (prefixWord ++ tailWord_5149319).sum := by decide
  have hdescent : baseEnd_5149319 < baseStart_5149319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149326 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_5149326 : Nat := 118140960795 + 5149326 * 2 ^ 59
def prefixEnd_5149326 : Nat := 4983230072969 + 3 ^ 40 * 5149326 * 2
def baseEnd_5149326 : Nat := 881359761564608490681229

theorem tailTrace_5149326 : CollatzResearch.WordTrace tailWord_5149326 prefixEnd_5149326 881359761564608490681229 := by
  unfold tailWord_5149326
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476418567859851463815479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125207565695252541140349221 23476418567859851463815479)
  ·
    refine ⟨35214627851789777195723219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23476418567859851463815479 35214627851789777195723219)
    ·
      refine ⟨52821941777684665793584829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35214627851789777195723219 52821941777684665793584829)
      ·
        refine ⟨19808228166631749672594311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52821941777684665793584829 19808228166631749672594311)
        ·
          refine ⟨29712342249947624508891467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19808228166631749672594311 29712342249947624508891467)
          ·
            refine ⟨44568513374921436763337201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29712342249947624508891467 44568513374921436763337201)
            ·
              refine ⟨33426385031191077572502901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44568513374921436763337201 33426385031191077572502901)
              ·
                refine ⟨3133723596674163522422147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33426385031191077572502901 3133723596674163522422147)
                ·
                  refine ⟨4700585395011245283633221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133723596674163522422147 4700585395011245283633221)
                  ·
                    refine ⟨881359761564608490681229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700585395011245283633221 881359761564608490681229)
                    ·
                      rfl

theorem cell23_5149326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_5149326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149326 prefixEnd_5149326 := by exact prefixLift 5149326
  have htrace : WordTrace (prefixWord ++ tailWord_5149326) baseStart_5149326 baseEnd_5149326 := by
    simpa [prefixWord, tailWord_5149326, baseEnd_5149326] using wordTrace_append hprefix tailTrace_5149326
  have hstable : (prefixWord ++ tailWord_5149326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149326).length < 2 ^ (prefixWord ++ tailWord_5149326).sum := by decide
  have hdescent : baseEnd_5149326 < baseStart_5149326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149349 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_5149349 : Nat := 118140960795 + 5149349 * 2 ^ 59
def prefixEnd_5149349 : Nat := 4983230072969 + 3 ^ 40 * 5149349 * 2
def baseEnd_5149349 : Nat := 2644091094748878882056081

theorem tailTrace_5149349 : CollatzResearch.WordTrace tailWord_5149349 prefixEnd_5149349 2644091094748878882056081 := by
  unfold tailWord_5149349
  simp only [CollatzResearch.WordTrace]
  refine ⟨187812187421795486638611101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125208124947863657759074067 187812187421795486638611101)
  ·
    refine ⟨70429570283173307489479163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187812187421795486638611101 70429570283173307489479163)
    ·
      refine ⟨105644355424759961234218745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70429570283173307489479163 105644355424759961234218745)
      ·
        refine ⟨79233266568569970925664059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105644355424759961234218745 79233266568569970925664059)
        ·
          refine ⟨118849899852854956388496089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79233266568569970925664059 118849899852854956388496089)
          ·
            refine ⟨89137424889641217291372067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118849899852854956388496089 89137424889641217291372067)
            ·
              refine ⟨133706137334461825937058101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89137424889641217291372067 133706137334461825937058101)
              ·
                refine ⟨12534950375105796181599197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133706137334461825937058101 12534950375105796181599197)
                ·
                  refine ⟨4700606390664673568099699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12534950375105796181599197 4700606390664673568099699)
                  ·
                    refine ⟨7050909585997010352149549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700606390664673568099699 7050909585997010352149549)
                    ·
                      refine ⟨2644091094748878882056081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050909585997010352149549 2644091094748878882056081)
                      ·
                        rfl

theorem cell23_5149349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_5149349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149349 prefixEnd_5149349 := by exact prefixLift 5149349
  have htrace : WordTrace (prefixWord ++ tailWord_5149349) baseStart_5149349 baseEnd_5149349 := by
    simpa [prefixWord, tailWord_5149349, baseEnd_5149349] using wordTrace_append hprefix tailTrace_5149349
  have hstable : (prefixWord ++ tailWord_5149349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149349).length < 2 ^ (prefixWord ++ tailWord_5149349).sum := by decide
  have hdescent : baseEnd_5149349 < baseStart_5149349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149376 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2]
def baseStart_5149376 : Nat := 118140960795 + 5149376 * 2 ^ 59
def prefixEnd_5149376 : Nat := 4983230072969 + 3 ^ 40 * 5149376 * 2
def baseEnd_5149376 : Nat := 2644104958726550276418457

theorem tailTrace_5149376 : CollatzResearch.WordTrace tailWord_5149376 prefixEnd_5149376 2644104958726550276418457 := by
  unfold tailWord_5149376
  simp only [CollatzResearch.WordTrace]
  refine ⟨93906586096348835124921991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125208781461798446833229321 93906586096348835124921991)
  ·
    refine ⟨140859879144523252687382987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93906586096348835124921991 140859879144523252687382987)
    ·
      refine ⟨211289818716784879031074481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140859879144523252687382987 211289818716784879031074481)
      ·
        refine ⟨158467364037588659273305861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211289818716784879031074481 158467364037588659273305861)
        ·
          refine ⟨29712630757047873613744849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158467364037588659273305861 29712630757047873613744849)
          ·
            refine ⟨22284473067785905210308637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29712630757047873613744849 22284473067785905210308637)
            ·
              refine ⟨8356677400419714453865739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22284473067785905210308637 8356677400419714453865739)
              ·
                refine ⟨12535016100629571680798609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356677400419714453865739 12535016100629571680798609)
                ·
                  refine ⟨9401262075472178760598957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12535016100629571680798609 9401262075472178760598957)
                  ·
                    refine ⟨3525473278302067035224609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9401262075472178760598957 3525473278302067035224609)
                    ·
                      refine ⟨2644104958726550276418457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525473278302067035224609 2644104958726550276418457)
                      ·
                        rfl

theorem cell23_5149376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_5149376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149376 prefixEnd_5149376 := by exact prefixLift 5149376
  have htrace : WordTrace (prefixWord ++ tailWord_5149376) baseStart_5149376 baseEnd_5149376 := by
    simpa [prefixWord, tailWord_5149376, baseEnd_5149376] using wordTrace_append hprefix tailTrace_5149376
  have hstable : (prefixWord ++ tailWord_5149376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149376).length < 2 ^ (prefixWord ++ tailWord_5149376).sum := by decide
  have hdescent : baseEnd_5149376 < baseStart_5149376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149386 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_5149386 : Nat := 118140960795 + 5149386 * 2 ^ 59
def prefixEnd_5149386 : Nat := 4983230072969 + 3 ^ 40 * 5149386 * 2
def baseEnd_5149386 : Nat := 881370031177698412431137

theorem tailTrace_5149386 : CollatzResearch.WordTrace tailWord_5149386 prefixEnd_5149386 881370031177698412431137 := by
  unfold tailWord_5149386
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953384230665360489427003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125209024615107627971805341 46953384230665360489427003)
  ·
    refine ⟨70430076345998040734140505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46953384230665360489427003 70430076345998040734140505)
    ·
      refine ⟨52822557259498530550605379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70430076345998040734140505 52822557259498530550605379)
      ·
        refine ⟨79233835889247795825908069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52822557259498530550605379 79233835889247795825908069)
        ·
          refine ⟨14856344229233961717357763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79233835889247795825908069 14856344229233961717357763)
          ·
            refine ⟨22284516343850942576036645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14856344229233961717357763 22284516343850942576036645)
            ·
              refine ⟨4178346814472051733006871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22284516343850942576036645 4178346814472051733006871)
              ·
                refine ⟨6267520221708077599510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178346814472051733006871 6267520221708077599510307)
                ·
                  refine ⟨9401280332562116399265461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267520221708077599510307 9401280332562116399265461)
                  ·
                    refine ⟨881370031177698412431137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9401280332562116399265461 881370031177698412431137)
                    ·
                      rfl

theorem cell23_5149386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_5149386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149386 prefixEnd_5149386 := by exact prefixLift 5149386
  have htrace : WordTrace (prefixWord ++ tailWord_5149386) baseStart_5149386 baseEnd_5149386 := by
    simpa [prefixWord, tailWord_5149386, baseEnd_5149386] using wordTrace_append hprefix tailTrace_5149386
  have hstable : (prefixWord ++ tailWord_5149386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149386).length < 2 ^ (prefixWord ++ tailWord_5149386).sum := by decide
  have hdescent : baseEnd_5149386 < baseStart_5149386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149399 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 4, 4]
def baseStart_5149399 : Nat := 118140960795 + 5149399 * 2 ^ 59
def prefixEnd_5149399 : Nat := 4983230072969 + 3 ^ 40 * 5149399 * 2
def baseEnd_5149399 : Nat := 881372256260534562143617

theorem tailTrace_5149399 : CollatzResearch.WordTrace tailWord_5149399 prefixEnd_5149399 881372256260534562143617 := by
  unfold tailWord_5149399
  simp only [CollatzResearch.WordTrace]
  refine ⟨187814011071614345177931251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125209340714409563451954167 187814011071614345177931251)
  ·
    refine ⟨281721016607421517766896877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187814011071614345177931251 281721016607421517766896877)
    ·
      refine ⟨105645381227783069162586329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281721016607421517766896877 105645381227783069162586329)
      ·
        refine ⟨79234035920837301871939747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105645381227783069162586329 79234035920837301871939747)
        ·
          refine ⟨118851053881255952807909621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79234035920837301871939747 118851053881255952807909621)
          ·
            refine ⟨11142286301367745575741527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118851053881255952807909621 11142286301367745575741527)
            ·
              refine ⟨16713429452051618363612291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142286301367745575741527 16713429452051618363612291)
              ·
                refine ⟨25070144178077427545418437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16713429452051618363612291 25070144178077427545418437)
                ·
                  refine ⟨4700652033389517664765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25070144178077427545418437 4700652033389517664765957)
                  ·
                    refine ⟨881372256260534562143617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700652033389517664765957 881372256260534562143617)
                    ·
                      rfl

theorem cell23_5149399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_5149399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149399 prefixEnd_5149399 := by exact prefixLift 5149399
  have htrace : WordTrace (prefixWord ++ tailWord_5149399) baseStart_5149399 baseEnd_5149399 := by
    simpa [prefixWord, tailWord_5149399, baseEnd_5149399] using wordTrace_append hprefix tailTrace_5149399
  have hstable : (prefixWord ++ tailWord_5149399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149399).length < 2 ^ (prefixWord ++ tailWord_5149399).sum := by decide
  have hdescent : baseEnd_5149399 < baseStart_5149399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149402 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_5149402 : Nat := 118140960795 + 5149402 * 2 ^ 59
def prefixEnd_5149402 : Nat := 4983230072969 + 3 ^ 40 * 5149402 * 2
def baseEnd_5149402 : Nat := 2644118309223567174693337

theorem tailTrace_5149402 : CollatzResearch.WordTrace tailWord_5149402 prefixEnd_5149402 2644118309223567174693337 := by
  unfold tailWord_5149402
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953530122650869172572615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125209413660402317793526973 46953530122650869172572615)
  ·
    refine ⟨70430295183976303758858923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46953530122650869172572615 70430295183976303758858923)
    ·
      refine ⟨105645442775964455638288385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70430295183976303758858923 105645442775964455638288385)
      ·
        refine ⟨79234082081973341728716289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105645442775964455638288385 79234082081973341728716289)
        ·
          refine ⟨59425561561480006296537217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79234082081973341728716289 59425561561480006296537217)
          ·
            refine ⟨44569171171110004722402913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59425561561480006296537217 44569171171110004722402913)
            ·
              refine ⟨33426878378332503541802185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44569171171110004722402913 33426878378332503541802185)
              ·
                refine ⟨25070158783749377656351639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33426878378332503541802185 25070158783749377656351639)
                ·
                  refine ⟨37605238175624066484527459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25070158783749377656351639 37605238175624066484527459)
                  ·
                    refine ⟨56407857263436099726791189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37605238175624066484527459 56407857263436099726791189)
                    ·
                      refine ⟨2644118309223567174693337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56407857263436099726791189 2644118309223567174693337)
                      ·
                        rfl

theorem cell23_5149402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_5149402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149402 prefixEnd_5149402 := by exact prefixLift 5149402
  have htrace : WordTrace (prefixWord ++ tailWord_5149402) baseStart_5149402 baseEnd_5149402 := by
    simpa [prefixWord, tailWord_5149402, baseEnd_5149402] using wordTrace_append hprefix tailTrace_5149402
  have hstable : (prefixWord ++ tailWord_5149402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149402).length < 2 ^ (prefixWord ++ tailWord_5149402).sum := by decide
  have hdescent : baseEnd_5149402 < baseStart_5149402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149409 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_5149409 : Nat := 118140960795 + 5149409 * 2 ^ 59
def prefixEnd_5149409 : Nat := 4983230072969 + 3 ^ 40 * 5149409 * 2
def baseEnd_5149409 : Nat := 2644121903588148647305805

theorem tailTrace_5149409 : CollatzResearch.WordTrace tailWord_5149409 prefixEnd_5149409 2644121903588148647305805 := by
  unfold tailWord_5149409
  simp only [CollatzResearch.WordTrace]
  refine ⟨187814375801578116885795281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125209583867718744590530187 187814375801578116885795281)
  ·
    refine ⟨140860781851183587664346461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187814375801578116885795281 140860781851183587664346461)
    ·
      refine ⟨52822793194193845374129923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140860781851183587664346461 52822793194193845374129923)
      ·
        refine ⟨79234189791290768061194885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52822793194193845374129923 79234189791290768061194885)
        ·
          refine ⟨14856410585867019011474041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79234189791290768061194885 14856410585867019011474041)
          ·
            refine ⟨11142307939400264258605531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14856410585867019011474041 11142307939400264258605531)
            ·
              refine ⟨16713461909100396387908297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142307939400264258605531 16713461909100396387908297)
              ·
                refine ⟨12535096431825297290931223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16713461909100396387908297 12535096431825297290931223)
                ·
                  refine ⟨18802644647737945936396835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535096431825297290931223 18802644647737945936396835)
                  ·
                    refine ⟨28203966971606918904595253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18802644647737945936396835 28203966971606918904595253)
                    ·
                      refine ⟨2644121903588148647305805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28203966971606918904595253 2644121903588148647305805)
                      ·
                        rfl

theorem cell23_5149409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_5149409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149409 prefixEnd_5149409 := by exact prefixLift 5149409
  have htrace : WordTrace (prefixWord ++ tailWord_5149409) baseStart_5149409 baseEnd_5149409 := by
    simpa [prefixWord, tailWord_5149409, baseEnd_5149409] using wordTrace_append hprefix tailTrace_5149409
  have hstable : (prefixWord ++ tailWord_5149409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149409).length < 2 ^ (prefixWord ++ tailWord_5149409).sum := by decide
  have hdescent : baseEnd_5149409 < baseStart_5149409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149416 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_5149416 : Nat := 118140960795 + 5149416 * 2 ^ 59
def prefixEnd_5149416 : Nat := 4983230072969 + 3 ^ 40 * 5149416 * 2
def baseEnd_5149416 : Nat := 881375165984243373306091

theorem tailTrace_5149416 : CollatzResearch.WordTrace tailWord_5149416 prefixEnd_5149416 881375165984243373306091 := by
  unfold tailWord_5149416
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907315556276378540650051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125209754075035171387533401 93907315556276378540650051)
  ·
    refine ⟨140860973334414567810975077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93907315556276378540650051 140860973334414567810975077)
    ·
      refine ⟨26411432500202731464557827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140860973334414567810975077 26411432500202731464557827)
      ·
        refine ⟨39617148750304097196836741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26411432500202731464557827 39617148750304097196836741)
        ·
          refine ⟨7428215390682018224406889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39617148750304097196836741 7428215390682018224406889)
          ·
            refine ⟨5571161543011513668305167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428215390682018224406889 5571161543011513668305167)
            ·
              refine ⟨8356742314517270502457751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571161543011513668305167 8356742314517270502457751)
              ·
                refine ⟨12535113471775905753686627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356742314517270502457751 12535113471775905753686627)
                ·
                  refine ⟨18802670207663858630529941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535113471775905753686627 18802670207663858630529941)
                  ·
                    refine ⟨881375165984243373306091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18802670207663858630529941 881375165984243373306091)
                    ·
                      rfl

theorem cell23_5149416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_5149416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149416 prefixEnd_5149416 := by exact prefixLift 5149416
  have htrace : WordTrace (prefixWord ++ tailWord_5149416) baseStart_5149416 baseEnd_5149416 := by
    simpa [prefixWord, tailWord_5149416, baseEnd_5149416] using wordTrace_append hprefix tailTrace_5149416
  have hstable : (prefixWord ++ tailWord_5149416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149416).length < 2 ^ (prefixWord ++ tailWord_5149416).sum := by decide
  have hdescent : baseEnd_5149416 < baseStart_5149416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149426 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5149426 : Nat := 118140960795 + 5149426 * 2 ^ 59
def prefixEnd_5149426 : Nat := 4983230072969 + 3 ^ 40 * 5149426 * 2
def baseEnd_5149426 : Nat := 2644130632759275080793227

theorem tailTrace_5149426 : CollatzResearch.WordTrace tailWord_5149426 prefixEnd_5149426 2644130632759275080793227 := by
  unfold tailWord_5149426
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953748960629132197291033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125209997228344352526109421 46953748960629132197291033)
  ·
    refine ⟨35215311720471849147968275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46953748960629132197291033 35215311720471849147968275)
    ·
      refine ⟨52822967580707773721952413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35215311720471849147968275 52822967580707773721952413)
      ·
        refine ⟨19808612842765415145732155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52822967580707773721952413 19808612842765415145732155)
        ·
          refine ⟨29712919264148122718598233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19808612842765415145732155 29712919264148122718598233)
          ·
            refine ⟨22284689448111092038948675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29712919264148122718598233 22284689448111092038948675)
            ·
              refine ⟨33427034172166638058423013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22284689448111092038948675 33427034172166638058423013)
              ·
                refine ⟨6267568907281244635954315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33427034172166638058423013 6267568907281244635954315)
                ·
                  refine ⟨9401353360921866953931473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267568907281244635954315 9401353360921866953931473)
                  ·
                    refine ⟨7051015020691400215448605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9401353360921866953931473 7051015020691400215448605)
                    ·
                      refine ⟨2644130632759275080793227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051015020691400215448605 2644130632759275080793227)
                      ·
                        rfl

theorem cell23_5149426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5149426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149426 prefixEnd_5149426 := by exact prefixLift 5149426
  have htrace : WordTrace (prefixWord ++ tailWord_5149426) baseStart_5149426 baseEnd_5149426 := by
    simpa [prefixWord, tailWord_5149426, baseEnd_5149426] using wordTrace_append hprefix tailTrace_5149426
  have hstable : (prefixWord ++ tailWord_5149426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149426).length < 2 ^ (prefixWord ++ tailWord_5149426).sum := by decide
  have hdescent : baseEnd_5149426 < baseStart_5149426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149452 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5149452 : Nat := 118140960795 + 5149452 * 2 ^ 59
def prefixEnd_5149452 : Nat := 4983230072969 + 3 ^ 40 * 5149452 * 2
def baseEnd_5149452 : Nat := 2644143983256291979068107

theorem tailTrace_5149452 : CollatzResearch.WordTrace tailWord_5149452 prefixEnd_5149452 2644143983256291979068107 := by
  unfold tailWord_5149452
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907972070211167614805305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125210629426948223486407073 93907972070211167614805305)
  ·
    refine ⟨70430979052658375711103979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93907972070211167614805305 70430979052658375711103979)
    ·
      refine ⟨105646468578987563566655969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70430979052658375711103979 105646468578987563566655969)
      ·
        refine ⟨79234851434240672674991977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105646468578987563566655969 79234851434240672674991977)
        ·
          refine ⟨59426138575680504506243983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79234851434240672674991977 59426138575680504506243983)
          ·
            refine ⟨89139207863520756759365975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59426138575680504506243983 89139207863520756759365975)
            ·
              refine ⟨133708811795281135139048963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89139207863520756759365975 133708811795281135139048963)
              ·
                refine ⟨200563217692921702708573445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133708811795281135139048963 200563217692921702708573445)
                ·
                  refine ⟨37605603317422819257857521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200563217692921702708573445 37605603317422819257857521)
                  ·
                    refine ⟨28204202488067114443393141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37605603317422819257857521 28204202488067114443393141)
                    ·
                      refine ⟨2644143983256291979068107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28204202488067114443393141 2644143983256291979068107)
                      ·
                        rfl

theorem cell23_5149452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5149452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149452 prefixEnd_5149452 := by exact prefixLift 5149452
  have htrace : WordTrace (prefixWord ++ tailWord_5149452) baseStart_5149452 baseEnd_5149452 := by
    simpa [prefixWord, tailWord_5149452, baseEnd_5149452] using wordTrace_append hprefix tailTrace_5149452
  have hstable : (prefixWord ++ tailWord_5149452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149452).length < 2 ^ (prefixWord ++ tailWord_5149452).sum := by decide
  have hdescent : baseEnd_5149452 < baseStart_5149452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149466 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_5149466 : Nat := 118140960795 + 5149466 * 2 ^ 59
def prefixEnd_5149466 : Nat := 4983230072969 + 3 ^ 40 * 5149466 * 2
def baseEnd_5149466 : Nat := 2644151171985454924293043

theorem tailTrace_5149466 : CollatzResearch.WordTrace tailWord_5149466 prefixEnd_5149466 2644151171985454924293043 := by
  unfold tailWord_5149466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46954113690592903905155063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125210969841581077080413501 46954113690592903905155063)
  ·
    refine ⟨70431170535889355857732595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46954113690592903905155063 70431170535889355857732595)
    ·
      refine ⟨105646755803834033786598893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70431170535889355857732595 105646755803834033786598893)
      ·
        refine ⟨39617533426437762669974585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105646755803834033786598893 39617533426437762669974585)
        ·
          refine ⟨29713150069828322002480939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39617533426437762669974585 29713150069828322002480939)
          ·
            refine ⟨44569725104742483003721409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29713150069828322002480939 44569725104742483003721409)
            ·
              refine ⟨33427293828556862252791057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44569725104742483003721409 33427293828556862252791057)
              ·
                refine ⟨25070470371417646689593293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33427293828556862252791057 25070470371417646689593293)
                ·
                  refine ⟨9401426389281617508597485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25070470371417646689593293 9401426389281617508597485)
                  ·
                    refine ⟨3525534895980606565724057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9401426389281617508597485 3525534895980606565724057)
                    ·
                      refine ⟨2644151171985454924293043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525534895980606565724057 2644151171985454924293043)
                      ·
                        rfl

theorem cell23_5149466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_5149466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149466 prefixEnd_5149466 := by exact prefixLift 5149466
  have htrace : WordTrace (prefixWord ++ tailWord_5149466) baseStart_5149466 baseEnd_5149466 := by
    simpa [prefixWord, tailWord_5149466, baseEnd_5149466] using wordTrace_append hprefix tailTrace_5149466
  have hstable : (prefixWord ++ tailWord_5149466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149466).length < 2 ^ (prefixWord ++ tailWord_5149466).sum := by decide
  have hdescent : baseEnd_5149466 < baseStart_5149466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149496 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_5149496 : Nat := 118140960795 + 5149496 * 2 ^ 59
def prefixEnd_5149496 : Nat := 4983230072969 + 3 ^ 40 * 5149496 * 2
def baseEnd_5149496 : Nat := 2644166576405089806917905

theorem tailTrace_5149496 : CollatzResearch.WordTrace tailWord_5149496 prefixEnd_5149496 2644166576405089806917905 := by
  unfold tailWord_5149496
  simp only [CollatzResearch.WordTrace]
  refine ⟨93908774476131465372106171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125211699301508620496141561 93908774476131465372106171)
  ·
    refine ⟨140863161714197198058159257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93908774476131465372106171 140863161714197198058159257)
    ·
      refine ⟨105647371285647898543619443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140863161714197198058159257 105647371285647898543619443)
      ·
        refine ⟨158471056928471847815429165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105647371285647898543619443 158471056928471847815429165)
        ·
          refine ⟨59426646348176942930785937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158471056928471847815429165 59426646348176942930785937)
          ·
            refine ⟨44569984761132707198089453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59426646348176942930785937 44569984761132707198089453)
            ·
              refine ⟨16713744285424765199283545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44569984761132707198089453 16713744285424765199283545)
              ·
                refine ⟨12535308214068573899462659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16713744285424765199283545 12535308214068573899462659)
                ·
                  refine ⟨18802962321102860849193989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535308214068573899462659 18802962321102860849193989)
                  ·
                    refine ⟨3525555435206786409223873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18802962321102860849193989 3525555435206786409223873)
                    ·
                      refine ⟨2644166576405089806917905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525555435206786409223873 2644166576405089806917905)
                      ·
                        rfl

theorem cell23_5149496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_5149496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149496 prefixEnd_5149496 := by exact prefixLift 5149496
  have htrace : WordTrace (prefixWord ++ tailWord_5149496) baseStart_5149496 baseEnd_5149496 := by
    simpa [prefixWord, tailWord_5149496, baseEnd_5149496] using wordTrace_append hprefix tailTrace_5149496
  have hstable : (prefixWord ++ tailWord_5149496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149496).length < 2 ^ (prefixWord ++ tailWord_5149496).sum := by decide
  have hdescent : baseEnd_5149496 < baseStart_5149496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149508 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5149508 : Nat := 118140960795 + 5149508 * 2 ^ 59
def prefixEnd_5149508 : Nat := 4983230072969 + 3 ^ 40 * 5149508 * 2
def baseEnd_5149508 : Nat := 2644172738172943759967851

theorem tailTrace_5149508 : CollatzResearch.WordTrace tailWord_5149508 prefixEnd_5149508 2644172738172943759967851 := by
  unfold tailWord_5149508
  simp only [CollatzResearch.WordTrace]
  refine ⟨93908993314109728396824589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125211991085479637862432785 93908993314109728396824589)
  ·
    refine ⟨35215872492791148148809221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93908993314109728396824589 35215872492791148148809221)
    ·
      refine ⟨6602976092398340277901729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35215872492791148148809221 6602976092398340277901729)
      ·
        refine ⟨4952232069298755208426297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6602976092398340277901729 4952232069298755208426297)
        ·
          refine ⟨3714174051974066406319723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952232069298755208426297 3714174051974066406319723)
          ·
            refine ⟨5571261077961099609479585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714174051974066406319723 5571261077961099609479585)
            ·
              refine ⟨4178445808470824707109689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571261077961099609479585 4178445808470824707109689)
              ·
                refine ⟨3133834356353118530332267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178445808470824707109689 3133834356353118530332267)
                ·
                  refine ⟨4700751534529677795498401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133834356353118530332267 4700751534529677795498401)
                  ·
                    refine ⟨3525563650897258346623801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700751534529677795498401 3525563650897258346623801)
                    ·
                      refine ⟨2644172738172943759967851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525563650897258346623801 2644172738172943759967851)
                      ·
                        rfl

theorem cell23_5149508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5149508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149508 prefixEnd_5149508 := by exact prefixLift 5149508
  have htrace : WordTrace (prefixWord ++ tailWord_5149508) baseStart_5149508 baseEnd_5149508 := by
    simpa [prefixWord, tailWord_5149508, baseEnd_5149508] using wordTrace_append hprefix tailTrace_5149508
  have hstable : (prefixWord ++ tailWord_5149508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149508).length < 2 ^ (prefixWord ++ tailWord_5149508).sum := by decide
  have hdescent : baseEnd_5149508 < baseStart_5149508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149513 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 2, 2, 2]
def baseStart_5149513 : Nat := 118140960795 + 5149513 * 2 ^ 59
def prefixEnd_5149513 : Nat := 4983230072969 + 3 ^ 40 * 5149513 * 2
def baseEnd_5149513 : Nat := 2644175305576216240405327

theorem tailTrace_5149513 : CollatzResearch.WordTrace tailWord_5149513 prefixEnd_5149513 2644175305576216240405327 := by
  unfold tailWord_5149513
  simp only [CollatzResearch.WordTrace]
  refine ⟨187818168993201342647581193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125212112662134228431720795 187818168993201342647581193)
  ·
    refine ⟨140863626744901006985685895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187818168993201342647581193 140863626744901006985685895)
    ·
      refine ⟨211295440117351510478528843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140863626744901006985685895 211295440117351510478528843)
      ·
        refine ⟨316943160176027265717793265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211295440117351510478528843 316943160176027265717793265)
        ·
          refine ⟨237707370132020449288344949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316943160176027265717793265 237707370132020449288344949)
          ·
            refine ⟨22285065949876917120782339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237707370132020449288344949 22285065949876917120782339)
            ·
              refine ⟨33427598924815375681173509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22285065949876917120782339 33427598924815375681173509)
              ·
                refine ⟨6267674798402882940220033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33427598924815375681173509 6267674798402882940220033)
                ·
                  refine ⟨4700756098802162205165025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6267674798402882940220033 4700756098802162205165025)
                  ·
                    refine ⟨3525567074101621653873769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700756098802162205165025 3525567074101621653873769)
                    ·
                      refine ⟨2644175305576216240405327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525567074101621653873769 2644175305576216240405327)
                      ·
                        rfl

theorem cell23_5149513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2, 2].length) (baseStart_5149513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149513 prefixEnd_5149513 := by exact prefixLift 5149513
  have htrace : WordTrace (prefixWord ++ tailWord_5149513) baseStart_5149513 baseEnd_5149513 := by
    simpa [prefixWord, tailWord_5149513, baseEnd_5149513] using wordTrace_append hprefix tailTrace_5149513
  have hstable : (prefixWord ++ tailWord_5149513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149513).length < 2 ^ (prefixWord ++ tailWord_5149513).sum := by decide
  have hdescent : baseEnd_5149513 < baseStart_5149513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149529 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_5149529 : Nat := 118140960795 + 5149529 * 2 ^ 59
def prefixEnd_5149529 : Nat := 4983230072969 + 3 ^ 40 * 5149529 * 2
def baseEnd_5149529 : Nat := 2644183521266688177805253

theorem tailTrace_5149529 : CollatzResearch.WordTrace tailWord_5149529 prefixEnd_5149529 2644183521266688177805253 := by
  unfold tailWord_5149529
  simp only [CollatzResearch.WordTrace]
  refine ⟨187818752561143377380163641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125212501707428918253442427 187818752561143377380163641)
  ·
    refine ⟨140864064420857533035122731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187818752561143377380163641 140864064420857533035122731)
    ·
      refine ⟨211296096631286299552684097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140864064420857533035122731 211296096631286299552684097)
      ·
        refine ⟨158472072473464724664513073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211296096631286299552684097 158472072473464724664513073)
        ·
          refine ⟨118854054355098543498384805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158472072473464724664513073 118854054355098543498384805)
          ·
            refine ⟨22285135191580976905947151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118854054355098543498384805 22285135191580976905947151)
            ·
              refine ⟨33427702787371465358920727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22285135191580976905947151 33427702787371465358920727)
              ·
                refine ⟨50141554181057198038381091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33427702787371465358920727 50141554181057198038381091)
                ·
                  refine ⟨75212331271585797057571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50141554181057198038381091 75212331271585797057571637)
                  ·
                    refine ⟨7051156056711168474147341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75212331271585797057571637 7051156056711168474147341)
                    ·
                      refine ⟨2644183521266688177805253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051156056711168474147341 2644183521266688177805253)
                      ·
                        rfl

theorem cell23_5149529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_5149529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149529 prefixEnd_5149529 := by exact prefixLift 5149529
  have htrace : WordTrace (prefixWord ++ tailWord_5149529) baseStart_5149529 baseEnd_5149529 := by
    simpa [prefixWord, tailWord_5149529, baseEnd_5149529] using wordTrace_append hprefix tailTrace_5149529
  have hstable : (prefixWord ++ tailWord_5149529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149529).length < 2 ^ (prefixWord ++ tailWord_5149529).sum := by decide
  have hdescent : baseEnd_5149529 < baseStart_5149529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149570 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_5149570 : Nat := 118140960795 + 5149570 * 2 ^ 59
def prefixEnd_5149570 : Nat := 4983230072969 + 3 ^ 40 * 5149570 * 2
def baseEnd_5149570 : Nat := 293800508219280279710285

theorem tailTrace_5149570 : CollatzResearch.WordTrace tailWord_5149570 prefixEnd_5149570 293800508219280279710285 := by
  unfold tailWord_5149570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46955061988498710345601541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125213498635996560921604109 46955061988498710345601541)
  ·
    refine ⟨8804074122843508189800289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46955061988498710345601541 8804074122843508189800289)
    ·
      refine ⟨6603055592132631142350217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8804074122843508189800289 6603055592132631142350217)
      ·
        refine ⟨4952291694099473356762663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6603055592132631142350217 4952291694099473356762663)
        ·
          refine ⟨7428437541149210035143995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952291694099473356762663 7428437541149210035143995)
          ·
            refine ⟨11142656311723815052715993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428437541149210035143995 11142656311723815052715993)
            ·
              refine ⟨8356992233792861289536995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11142656311723815052715993 8356992233792861289536995)
              ·
                refine ⟨12535488350689291934305493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356992233792861289536995 12535488350689291934305493)
                ·
                  refine ⟨293800508219280279710285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12535488350689291934305493 293800508219280279710285)
                  ·
                    rfl

theorem cell23_5149570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_5149570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149570 prefixEnd_5149570 := by exact prefixLift 5149570
  have htrace : WordTrace (prefixWord ++ tailWord_5149570) baseStart_5149570 baseEnd_5149570 := by
    simpa [prefixWord, tailWord_5149570, baseEnd_5149570] using wordTrace_append hprefix tailTrace_5149570
  have hstable : (prefixWord ++ tailWord_5149570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149570).length < 2 ^ (prefixWord ++ tailWord_5149570).sum := by decide
  have hdescent : baseEnd_5149570 < baseStart_5149570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149620 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5149620 : Nat := 118140960795 + 5149620 * 2 ^ 59
def prefixEnd_5149620 : Nat := 4983230072969 + 3 ^ 40 * 5149620 * 2
def baseEnd_5149620 : Nat := 2644230248006247321767335

theorem tailTrace_5149620 : CollatzResearch.WordTrace tailWord_5149620 prefixEnd_5149620 2644230248006247321767335 := by
  unfold tailWord_5149620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93911035801906849960863157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125214714402542466614484209 93911035801906849960863157)
  ·
    refine ⟨8804159606428767183830921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93911035801906849960863157 8804159606428767183830921)
    ·
      refine ⟨6603119704821575387873191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8804159606428767183830921 6603119704821575387873191)
      ·
        refine ⟨9904679557232363081809787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603119704821575387873191 9904679557232363081809787)
        ·
          refine ⟨14857019335848544622714681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904679557232363081809787 14857019335848544622714681)
          ·
            refine ⟨11142764501886408467036011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14857019335848544622714681 11142764501886408467036011)
            ·
              refine ⟨16714146752829612700554017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142764501886408467036011 16714146752829612700554017)
              ·
                refine ⟨12535610064622209525415513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16714146752829612700554017 12535610064622209525415513)
                ·
                  refine ⟨9401707548466657144061635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12535610064622209525415513 9401707548466657144061635)
                  ·
                    refine ⟨14102561322699985716092453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9401707548466657144061635 14102561322699985716092453)
                    ·
                      refine ⟨2644230248006247321767335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14102561322699985716092453 2644230248006247321767335)
                      ·
                        rfl

theorem cell23_5149620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5149620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149620 prefixEnd_5149620 := by exact prefixLift 5149620
  have htrace : WordTrace (prefixWord ++ tailWord_5149620) baseStart_5149620 baseEnd_5149620 := by
    simpa [prefixWord, tailWord_5149620, baseEnd_5149620] using wordTrace_append hprefix tailTrace_5149620
  have hstable : (prefixWord ++ tailWord_5149620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149620).length < 2 ^ (prefixWord ++ tailWord_5149620).sum := by decide
  have hdescent : baseEnd_5149620 < baseStart_5149620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149643 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 6]
def baseStart_5149643 : Nat := 118140960795 + 5149643 * 2 ^ 59
def prefixEnd_5149643 : Nat := 4983230072969 + 3 ^ 40 * 5149643 * 2
def baseEnd_5149643 : Nat := 293804673117922303531081

theorem tailTrace_5149643 : CollatzResearch.WordTrace tailWord_5149643 prefixEnd_5149643 293804673117922303531081 := by
  unfold tailWord_5149643
  simp only [CollatzResearch.WordTrace]
  refine ⟨187822910482730374849813583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125215273655153583233209055 187822910482730374849813583)
  ·
    refine ⟨281734365724095562274720375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187822910482730374849813583 281734365724095562274720375)
    ·
      refine ⟨422601548586143343412080563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281734365724095562274720375 422601548586143343412080563)
      ·
        refine ⟨633902322879215015118120845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422601548586143343412080563 633902322879215015118120845)
        ·
          refine ⟨237713371079705630669295317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 633902322879215015118120845 237713371079705630669295317)
          ·
            refine ⟨5571407134680600718811609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 237713371079705630669295317 5571407134680600718811609)
            ·
              refine ⟨4178555351010450539108707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571407134680600718811609 4178555351010450539108707)
              ·
                refine ⟨6267833026515675808663061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178555351010450539108707 6267833026515675808663061)
                ·
                  refine ⟨293804673117922303531081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6267833026515675808663061 293804673117922303531081)
                  ·
                    rfl

theorem cell23_5149643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 6].length) (baseStart_5149643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149643 prefixEnd_5149643 := by exact prefixLift 5149643
  have htrace : WordTrace (prefixWord ++ tailWord_5149643) baseStart_5149643 baseEnd_5149643 := by
    simpa [prefixWord, tailWord_5149643, baseEnd_5149643] using wordTrace_append hprefix tailTrace_5149643
  have hstable : (prefixWord ++ tailWord_5149643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149643).length < 2 ^ (prefixWord ++ tailWord_5149643).sum := by decide
  have hdescent : baseEnd_5149643 < baseStart_5149643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149656 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_5149656 : Nat := 118140960795 + 5149656 * 2 ^ 59
def prefixEnd_5149656 : Nat := 4983230072969 + 3 ^ 40 * 5149656 * 2
def baseEnd_5149656 : Nat := 881416244436603060305723

theorem tailTrace_5149656 : CollatzResearch.WordTrace tailWord_5149656 prefixEnd_5149656 881416244436603060305723 := by
  unfold tailWord_5149656
  simp only [CollatzResearch.WordTrace]
  refine ⟨93911692315841639035018411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125215589754455518713357881 93911692315841639035018411)
  ·
    refine ⟨140867538473762458552527617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93911692315841639035018411 140867538473762458552527617)
    ·
      refine ⟨105650653855321843914395713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140867538473762458552527617 105650653855321843914395713)
      ·
        refine ⟨79237990391491382935796785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105650653855321843914395713 79237990391491382935796785)
        ·
          refine ⟨59428492793618537201847589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79237990391491382935796785 59428492793618537201847589)
          ·
            refine ⟨11142842398803475725346423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59428492793618537201847589 11142842398803475725346423)
            ·
              refine ⟨16714263598205213588019635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142842398803475725346423 16714263598205213588019635)
              ·
                refine ⟨25071395397307820382029453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16714263598205213588019635 25071395397307820382029453)
                ·
                  refine ⟨9401773273990432643261045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25071395397307820382029453 9401773273990432643261045)
                  ·
                    refine ⟨881416244436603060305723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9401773273990432643261045 881416244436603060305723)
                    ·
                      rfl

theorem cell23_5149656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_5149656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149656 prefixEnd_5149656 := by exact prefixLift 5149656
  have htrace : WordTrace (prefixWord ++ tailWord_5149656) baseStart_5149656 baseEnd_5149656 := by
    simpa [prefixWord, tailWord_5149656, baseEnd_5149656] using wordTrace_append hprefix tailTrace_5149656
  have hstable : (prefixWord ++ tailWord_5149656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149656).length < 2 ^ (prefixWord ++ tailWord_5149656).sum := by decide
  have hdescent : baseEnd_5149656 < baseStart_5149656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149703 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 2, 4]
def baseStart_5149703 : Nat := 118140960795 + 5149703 * 2 ^ 59
def prefixEnd_5149703 : Nat := 4983230072969 + 3 ^ 40 * 5149703 * 2
def baseEnd_5149703 : Nat := 881424288966856832343151

theorem tailTrace_5149703 : CollatzResearch.WordTrace tailWord_5149703 prefixEnd_5149703 881424288966856832343151 := by
  unfold tailWord_5149703
  simp only [CollatzResearch.WordTrace]
  refine ⟨187825098862513005096997763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125216732575008670064665175 187825098862513005096997763)
  ·
    refine ⟨281737648293769507645496645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187825098862513005096997763 281737648293769507645496645)
    ·
      refine ⟨52825809055081782683530621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281737648293769507645496645 52825809055081782683530621)
      ·
        refine ⟨19809678395655668506323983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52825809055081782683530621 19809678395655668506323983)
        ·
          refine ⟨29714517593483502759485975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809678395655668506323983 29714517593483502759485975)
          ·
            refine ⟨44571776390225254139228963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29714517593483502759485975 44571776390225254139228963)
            ·
              refine ⟨66857664585337881208843445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44571776390225254139228963 66857664585337881208843445)
              ·
                refine ⟨6267906054875426363329073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66857664585337881208843445 6267906054875426363329073)
                ·
                  refine ⟨4700929541156569772496805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6267906054875426363329073 4700929541156569772496805)
                  ·
                    refine ⟨881424288966856832343151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700929541156569772496805 881424288966856832343151)
                    ·
                      rfl

theorem cell23_5149703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_5149703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149703 prefixEnd_5149703 := by exact prefixLift 5149703
  have htrace : WordTrace (prefixWord ++ tailWord_5149703) baseStart_5149703 baseEnd_5149703 := by
    simpa [prefixWord, tailWord_5149703, baseEnd_5149703] using wordTrace_append hprefix tailTrace_5149703
  have hstable : (prefixWord ++ tailWord_5149703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149703).length < 2 ^ (prefixWord ++ tailWord_5149703).sum := by decide
  have hdescent : baseEnd_5149703 < baseStart_5149703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149710 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5149710 : Nat := 118140960795 + 5149710 * 2 ^ 59
def prefixEnd_5149710 : Nat := 4983230072969 + 3 ^ 40 * 5149710 * 2
def baseEnd_5149710 : Nat := 2644276461265151969641921

theorem tailTrace_5149710 : CollatzResearch.WordTrace tailWord_5149710 prefixEnd_5149710 2644276461265151969641921 := by
  unfold tailWord_5149710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478169271685955661562823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125216902782325096861668389 23478169271685955661562823)
  ·
    refine ⟨35217253907528933492344235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478169271685955661562823 35217253907528933492344235)
    ·
      refine ⟨52825880861293400238516353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35217253907528933492344235 52825880861293400238516353)
      ·
        refine ⟨39619410645970050178887265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52825880861293400238516353 39619410645970050178887265)
        ·
          refine ⟨29714557984477537634165449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39619410645970050178887265 29714557984477537634165449)
          ·
            refine ⟨22285918488358153225624087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29714557984477537634165449 22285918488358153225624087)
            ·
              refine ⟨33428877732537229838436131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22285918488358153225624087 33428877732537229838436131)
              ·
                refine ⟨50143316598805844757654197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33428877732537229838436131 50143316598805844757654197)
                ·
                  refine ⟨4700935931138047946030081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50143316598805844757654197 4700935931138047946030081)
                  ·
                    refine ⟨3525701948353535959522561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700935931138047946030081 3525701948353535959522561)
                    ·
                      refine ⟨2644276461265151969641921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525701948353535959522561 2644276461265151969641921)
                      ·
                        rfl

theorem cell23_5149710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5149710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149710 prefixEnd_5149710 := by exact prefixLift 5149710
  have htrace : WordTrace (prefixWord ++ tailWord_5149710) baseStart_5149710 baseEnd_5149710 := by
    simpa [prefixWord, tailWord_5149710, baseEnd_5149710] using wordTrace_append hprefix tailTrace_5149710
  have hstable : (prefixWord ++ tailWord_5149710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149710).length < 2 ^ (prefixWord ++ tailWord_5149710).sum := by decide
  have hdescent : baseEnd_5149710 < baseStart_5149710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149714 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5149714 : Nat := 118140960795 + 5149714 * 2 ^ 59
def prefixEnd_5149714 : Nat := 4983230072969 + 3 ^ 40 * 5149714 * 2
def baseEnd_5149714 : Nat := 2644278515187769953991903

theorem tailTrace_5149714 : CollatzResearch.WordTrace tailWord_5149714 prefixEnd_5149714 2644278515187769953991903 := by
  unfold tailWord_5149714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956375016368288493912049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125217000043648769317098797 46956375016368288493912049)
  ·
    refine ⟨35217281262276216370434037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46956375016368288493912049 35217281262276216370434037)
    ·
      refine ⟨3301620118338395284728191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35217281262276216370434037 3301620118338395284728191)
      ·
        refine ⟨4952430177507592927092287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301620118338395284728191 4952430177507592927092287)
        ·
          refine ⟨7428645266261389390638431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952430177507592927092287 7428645266261389390638431)
          ·
            refine ⟨11142967899392084085957647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428645266261389390638431 11142967899392084085957647)
            ·
              refine ⟨16714451849088126128936471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142967899392084085957647 16714451849088126128936471)
              ·
                refine ⟨25071677773632189193404707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16714451849088126128936471 25071677773632189193404707)
                ·
                  refine ⟨37607516660448283790107061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25071677773632189193404707 37607516660448283790107061)
                  ·
                    refine ⟨3525704686917026605322537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37607516660448283790107061 3525704686917026605322537)
                    ·
                      refine ⟨2644278515187769953991903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525704686917026605322537 2644278515187769953991903)
                      ·
                        rfl

theorem cell23_5149714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5149714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149714 prefixEnd_5149714 := by exact prefixLift 5149714
  have htrace : WordTrace (prefixWord ++ tailWord_5149714) baseStart_5149714 baseEnd_5149714 := by
    simpa [prefixWord, tailWord_5149714, baseEnd_5149714] using wordTrace_append hprefix tailTrace_5149714
  have hstable : (prefixWord ++ tailWord_5149714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149714).length < 2 ^ (prefixWord ++ tailWord_5149714).sum := by decide
  have hdescent : baseEnd_5149714 < baseStart_5149714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149727 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 1, 2, 2]
def baseStart_5149727 : Nat := 118140960795 + 5149727 * 2 ^ 59
def prefixEnd_5149727 : Nat := 4983230072969 + 3 ^ 40 * 5149727 * 2
def baseEnd_5149727 : Nat := 2644285190436278403129343

theorem tailTrace_5149727 : CollatzResearch.WordTrace tailWord_5149727 prefixEnd_5149727 2644285190436278403129343 := by
  unfold tailWord_5149727
  simp only [CollatzResearch.WordTrace]
  refine ⟨187825974214426057195871435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125217316142950704797247623 187825974214426057195871435)
  ·
    refine ⟨281738961321639085793807153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187825974214426057195871435 281738961321639085793807153)
    ·
      refine ⟨211304220991229314345355365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281738961321639085793807153 211304220991229314345355365)
      ·
        refine ⟨39619541435855496439754131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211304220991229314345355365 39619541435855496439754131)
        ·
          refine ⟨59429312153783244659631197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39619541435855496439754131 59429312153783244659631197)
          ·
            refine ⟨22285992057668716747361699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59429312153783244659631197 22285992057668716747361699)
            ·
              refine ⟨33428988086503075121042549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22285992057668716747361699 33428988086503075121042549)
              ·
                refine ⟨3133967633109663292597739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33428988086503075121042549 3133967633109663292597739)
                ·
                  refine ⟨4700951449664494938896609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133967633109663292597739 4700951449664494938896609)
                  ·
                    refine ⟨3525713587248371204172457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4700951449664494938896609 3525713587248371204172457)
                    ·
                      refine ⟨2644285190436278403129343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525713587248371204172457 2644285190436278403129343)
                      ·
                        rfl

theorem cell23_5149727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_5149727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149727 prefixEnd_5149727 := by exact prefixLift 5149727
  have htrace : WordTrace (prefixWord ++ tailWord_5149727) baseStart_5149727 baseEnd_5149727 := by
    simpa [prefixWord, tailWord_5149727, baseEnd_5149727] using wordTrace_append hprefix tailTrace_5149727
  have hstable : (prefixWord ++ tailWord_5149727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149727).length < 2 ^ (prefixWord ++ tailWord_5149727).sum := by decide
  have hdescent : baseEnd_5149727 < baseStart_5149727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149730 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_5149730 : Nat := 118140960795 + 5149730 * 2 ^ 59
def prefixEnd_5149730 : Nat := 4983230072969 + 3 ^ 40 * 5149730 * 2
def baseEnd_5149730 : Nat := 2644286730878241891391829

theorem tailTrace_5149730 : CollatzResearch.WordTrace tailWord_5149730 prefixEnd_5149730 2644286730878241891391829 := by
  unfold tailWord_5149730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956520908353797177057661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125217389088943459138820429 46956520908353797177057661)
  ·
    refine ⟨17608695340632673941396623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46956520908353797177057661 17608695340632673941396623)
    ·
      refine ⟨26413043010949010912094935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17608695340632673941396623 26413043010949010912094935)
      ·
        refine ⟨39619564516423516368142403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26413043010949010912094935 39619564516423516368142403)
        ·
          refine ⟨59429346774635274552213605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39619564516423516368142403 59429346774635274552213605)
          ·
            refine ⟨11143002520244113978540051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59429346774635274552213605 11143002520244113978540051)
            ·
              refine ⟨16714503780366170967810077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11143002520244113978540051 16714503780366170967810077)
              ·
                refine ⟨6267938917637314112928779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16714503780366170967810077 6267938917637314112928779)
                ·
                  refine ⟨9401908376455971169393169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267938917637314112928779 9401908376455971169393169)
                  ·
                    refine ⟨7051431282341978377044877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9401908376455971169393169 7051431282341978377044877)
                    ·
                      refine ⟨2644286730878241891391829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051431282341978377044877 2644286730878241891391829)
                      ·
                        rfl

theorem cell23_5149730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_5149730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149730 prefixEnd_5149730 := by exact prefixLift 5149730
  have htrace : WordTrace (prefixWord ++ tailWord_5149730) baseStart_5149730 baseEnd_5149730 := by
    simpa [prefixWord, tailWord_5149730, baseEnd_5149730] using wordTrace_append hprefix tailTrace_5149730
  have hstable : (prefixWord ++ tailWord_5149730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149730).length < 2 ^ (prefixWord ++ tailWord_5149730).sum := by decide
  have hdescent : baseEnd_5149730 < baseStart_5149730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149770 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_5149770 : Nat := 118140960795 + 5149770 * 2 ^ 59
def prefixEnd_5149770 : Nat := 4983230072969 + 3 ^ 40 * 5149770 * 2
def baseEnd_5149770 : Nat := 2644307270104421734891645

theorem tailTrace_5149770 : CollatzResearch.WordTrace tailWord_5149770 prefixEnd_5149770 2644307270104421734891645 := by
  unfold tailWord_5149770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956885638317568884921691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125218361702180183693124509 46956885638317568884921691)
  ·
    refine ⟨70435328457476353327382537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46956885638317568884921691 70435328457476353327382537)
    ·
      refine ⟨52826496343107264995536903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70435328457476353327382537 52826496343107264995536903)
      ·
        refine ⟨79239744514660897493305355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52826496343107264995536903 79239744514660897493305355)
        ·
          refine ⟨118859616771991346239958033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79239744514660897493305355 118859616771991346239958033)
          ·
            refine ⟨89144712578993509679968525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118859616771991346239958033 89144712578993509679968525)
            ·
              refine ⟨33429267217122566129988197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89144712578993509679968525 33429267217122566129988197)
              ·
                refine ⟨6267987603210481149372787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33429267217122566129988197 6267987603210481149372787)
                ·
                  refine ⟨9401981404815721724059181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267987603210481149372787 9401981404815721724059181)
                  ·
                    refine ⟨3525743026805895646522193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9401981404815721724059181 3525743026805895646522193)
                    ·
                      refine ⟨2644307270104421734891645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525743026805895646522193 2644307270104421734891645)
                      ·
                        rfl

theorem cell23_5149770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_5149770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149770 prefixEnd_5149770 := by exact prefixLift 5149770
  have htrace : WordTrace (prefixWord ++ tailWord_5149770) baseStart_5149770 baseEnd_5149770 := by
    simpa [prefixWord, tailWord_5149770, baseEnd_5149770] using wordTrace_append hprefix tailTrace_5149770
  have hstable : (prefixWord ++ tailWord_5149770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149770).length < 2 ^ (prefixWord ++ tailWord_5149770).sum := by decide
  have hdescent : baseEnd_5149770 < baseStart_5149770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149773 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5149773 : Nat := 118140960795 + 5149773 * 2 ^ 59
def prefixEnd_5149773 : Nat := 4983230072969 + 3 ^ 40 * 5149773 * 2
def baseEnd_5149773 : Nat := 2644308810546385223154131

theorem tailTrace_5149773 : CollatzResearch.WordTrace tailWord_5149773 prefixEnd_5149773 2644308810546385223154131 := by
  unfold tailWord_5149773
  simp only [CollatzResearch.WordTrace]
  refine ⟨187827651972259407052045973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125218434648172938034697315 187827651972259407052045973)
  ·
    refine ⟨8804421186199659705564655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187827651972259407052045973 8804421186199659705564655)
    ·
      refine ⟨13206631779299489558346983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804421186199659705564655 13206631779299489558346983)
      ·
        refine ⟨19809947668949234337520475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206631779299489558346983 19809947668949234337520475)
        ·
          refine ⟨29714921503423851506280713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809947668949234337520475 29714921503423851506280713)
          ·
            refine ⟨22286191127567888629710535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29714921503423851506280713 22286191127567888629710535)
            ·
              refine ⟨33429286691351832944565803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22286191127567888629710535 33429286691351832944565803)
              ·
                refine ⟨50143930037027749416848705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33429286691351832944565803 50143930037027749416848705)
                ·
                  refine ⟨37607947527770812062636529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50143930037027749416848705 37607947527770812062636529)
                  ·
                    refine ⟨28205960645828109046977397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37607947527770812062636529 28205960645828109046977397)
                    ·
                      refine ⟨2644308810546385223154131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28205960645828109046977397 2644308810546385223154131)
                      ·
                        rfl

theorem cell23_5149773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5149773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149773 prefixEnd_5149773 := by exact prefixLift 5149773
  have htrace : WordTrace (prefixWord ++ tailWord_5149773) baseStart_5149773 baseEnd_5149773 := by
    simpa [prefixWord, tailWord_5149773, baseEnd_5149773] using wordTrace_append hprefix tailTrace_5149773
  have hstable : (prefixWord ++ tailWord_5149773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149773).length < 2 ^ (prefixWord ++ tailWord_5149773).sum := by decide
  have hdescent : baseEnd_5149773 < baseStart_5149773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149783 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_5149783 : Nat := 118140960795 + 5149783 * 2 ^ 59
def prefixEnd_5149783 : Nat := 4983230072969 + 3 ^ 40 * 5149783 * 2
def baseEnd_5149783 : Nat := 2644313945352930184029085

theorem tailTrace_5149783 : CollatzResearch.WordTrace tailWord_5149783 prefixEnd_5149783 2644313945352930184029085 := by
  unfold tailWord_5149783
  simp only [CollatzResearch.WordTrace]
  refine ⟨187828016702223178759910003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125218677801482119173273335 187828016702223178759910003)
  ·
    refine ⟨281742025053334768139865005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187828016702223178759910003 281742025053334768139865005)
    ·
      refine ⟨105653259395000538052449377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281742025053334768139865005 105653259395000538052449377)
      ·
        refine ⟨79239944546250403539337033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105653259395000538052449377 79239944546250403539337033)
        ·
          refine ⟨59429958409687802654502775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79239944546250403539337033 59429958409687802654502775)
          ·
            refine ⟨89144937614531703981754163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59429958409687802654502775 89144937614531703981754163)
            ·
              refine ⟨133717406421797555972631245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89144937614531703981754163 133717406421797555972631245)
              ·
                refine ⟨50144027408174083489736717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133717406421797555972631245 50144027408174083489736717)
                ·
                  refine ⟨18804010278065281308651269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50144027408174083489736717 18804010278065281308651269)
                  ·
                    refine ⟨3525751927137240245372113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18804010278065281308651269 3525751927137240245372113)
                    ·
                      refine ⟨2644313945352930184029085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525751927137240245372113 2644313945352930184029085)
                      ·
                        rfl

theorem cell23_5149783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_5149783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149783 prefixEnd_5149783 := by exact prefixLift 5149783
  have htrace : WordTrace (prefixWord ++ tailWord_5149783) baseStart_5149783 baseEnd_5149783 := by
    simpa [prefixWord, tailWord_5149783, baseEnd_5149783] using wordTrace_append hprefix tailTrace_5149783
  have hstable : (prefixWord ++ tailWord_5149783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149783).length < 2 ^ (prefixWord ++ tailWord_5149783).sum := by decide
  have hdescent : baseEnd_5149783 < baseStart_5149783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149836 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_5149836 : Nat := 118140960795 + 5149836 * 2 ^ 59
def prefixEnd_5149836 : Nat := 4983230072969 + 3 ^ 40 * 5149836 * 2
def baseEnd_5149836 : Nat := 881447053275872825555447

theorem tailTrace_5149836 : CollatzResearch.WordTrace tailWord_5149836 prefixEnd_5149836 881447053275872825555447 := by
  unfold tailWord_5149836
  simp only [CollatzResearch.WordTrace]
  refine ⟨93914974885515584405794681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125219966514020779207726241 93914974885515584405794681)
  ·
    refine ⟨70436231164136688304346011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93914974885515584405794681 70436231164136688304346011)
    ·
      refine ⟨105654346746205032456519017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70436231164136688304346011 105654346746205032456519017)
      ·
        refine ⟨79240760059653774342389263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105654346746205032456519017 79240760059653774342389263)
        ·
          refine ⟨118861140089480661513583895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79240760059653774342389263 118861140089480661513583895)
          ·
            refine ⟨178291710134220992270375843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118861140089480661513583895 178291710134220992270375843)
            ·
              refine ⟨267437565201331488405563765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178291710134220992270375843 267437565201331488405563765)
              ·
                refine ⟨25072271737624827038021603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267437565201331488405563765 25072271737624827038021603)
                ·
                  refine ⟨37608407606437240557032405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25072271737624827038021603 37608407606437240557032405)
                  ·
                    refine ⟨881447053275872825555447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37608407606437240557032405 881447053275872825555447)
                    ·
                      rfl

theorem cell23_5149836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_5149836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149836 prefixEnd_5149836 := by exact prefixLift 5149836
  have htrace : WordTrace (prefixWord ++ tailWord_5149836) baseStart_5149836 baseEnd_5149836 := by
    simpa [prefixWord, tailWord_5149836, baseEnd_5149836] using wordTrace_append hprefix tailTrace_5149836
  have hstable : (prefixWord ++ tailWord_5149836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149836).length < 2 ^ (prefixWord ++ tailWord_5149836).sum := by decide
  have hdescent : baseEnd_5149836 < baseStart_5149836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149853 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_5149853 : Nat := 118140960795 + 5149853 * 2 ^ 59
def prefixEnd_5149853 : Nat := 4983230072969 + 3 ^ 40 * 5149853 * 2
def baseEnd_5149853 : Nat := 881449962999581636717921

theorem tailTrace_5149853 : CollatzResearch.WordTrace tailWord_5149853 prefixEnd_5149853 881449962999581636717921 := by
  unfold tailWord_5149853
  simp only [CollatzResearch.WordTrace]
  refine ⟨187830569811969580714958213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125220379874646387143305475 187830569811969580714958213)
  ·
    refine ⟨35218231839744296384054665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187830569811969580714958213 35218231839744296384054665)
    ·
      refine ⟨26413673879808222288040999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35218231839744296384054665 26413673879808222288040999)
      ·
        refine ⟨39620510819712333432061499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26413673879808222288040999 39620510819712333432061499)
        ·
          refine ⟨59430766229568500148092249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39620510819712333432061499 59430766229568500148092249)
          ·
            refine ⟨44573074672176375111069187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59430766229568500148092249 44573074672176375111069187)
            ·
              refine ⟨66859612008264562666603781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44573074672176375111069187 66859612008264562666603781)
              ·
                refine ⟨12536177251549605499988209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66859612008264562666603781 12536177251549605499988209)
                ·
                  refine ⟨9402132938662204124991157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12536177251549605499988209 9402132938662204124991157)
                  ·
                    refine ⟨881449962999581636717921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9402132938662204124991157 881449962999581636717921)
                    ·
                      rfl

theorem cell23_5149853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_5149853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149853 prefixEnd_5149853 := by exact prefixLift 5149853
  have htrace : WordTrace (prefixWord ++ tailWord_5149853) baseStart_5149853 baseEnd_5149853 := by
    simpa [prefixWord, tailWord_5149853, baseEnd_5149853] using wordTrace_append hprefix tailTrace_5149853
  have hstable : (prefixWord ++ tailWord_5149853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149853).length < 2 ^ (prefixWord ++ tailWord_5149853).sum := by decide
  have hdescent : baseEnd_5149853 < baseStart_5149853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149860 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_5149860 : Nat := 118140960795 + 5149860 * 2 ^ 59
def prefixEnd_5149860 : Nat := 4983230072969 + 3 ^ 40 * 5149860 * 2
def baseEnd_5149860 : Nat := 2644353483363326382766231

theorem tailTrace_5149860 : CollatzResearch.WordTrace tailWord_5149860 prefixEnd_5149860 2644353483363326382766231 := by
  unfold tailWord_5149860
  simp only [CollatzResearch.WordTrace]
  refine ⟨93915412561472110455231517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125220550081962813940308689 93915412561472110455231517)
  ·
    refine ⟨35218279710552041420711819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93915412561472110455231517 35218279710552041420711819)
    ·
      refine ⟨52827419565828062131067729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35218279710552041420711819 52827419565828062131067729)
      ·
        refine ⟨39620564674371046598300797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52827419565828062131067729 39620564674371046598300797)
        ·
          refine ⟨14857711752889142474362799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39620564674371046598300797 14857711752889142474362799)
          ·
            refine ⟨22286567629333713711544199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14857711752889142474362799 22286567629333713711544199)
            ·
              refine ⟨33429851444000570567316299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22286567629333713711544199 33429851444000570567316299)
              ·
                refine ⟨50144777166000855850974449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33429851444000570567316299 50144777166000855850974449)
                ·
                  refine ⟨37608582874500641888230837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50144777166000855850974449 37608582874500641888230837)
                  ·
                    refine ⟨3525804644484435177021641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37608582874500641888230837 3525804644484435177021641)
                    ·
                      refine ⟨2644353483363326382766231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525804644484435177021641 2644353483363326382766231)
                      ·
                        rfl

theorem cell23_5149860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_5149860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149860 prefixEnd_5149860 := by exact prefixLift 5149860
  have htrace : WordTrace (prefixWord ++ tailWord_5149860) baseStart_5149860 baseEnd_5149860 := by
    simpa [prefixWord, tailWord_5149860, baseEnd_5149860] using wordTrace_append hprefix tailTrace_5149860
  have hstable : (prefixWord ++ tailWord_5149860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149860).length < 2 ^ (prefixWord ++ tailWord_5149860).sum := by decide
  have hdescent : baseEnd_5149860 < baseStart_5149860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149994 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5149994 : Nat := 118140960795 + 5149994 * 2 ^ 59
def prefixEnd_5149994 : Nat := 4983230072969 + 3 ^ 40 * 5149994 * 2
def baseEnd_5149994 : Nat := 881474096590342952830205

theorem tailTrace_5149994 : CollatzResearch.WordTrace tailWord_5149994 prefixEnd_5149994 881474096590342952830205 := by
  unfold tailWord_5149994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46958928126114690448960259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125223808336305841197227357 46958928126114690448960259)
  ·
    refine ⟨70438392189172035673440389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46958928126114690448960259 70438392189172035673440389)
    ·
      refine ⟨13207198535469756688770073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70438392189172035673440389 13207198535469756688770073)
      ·
        refine ⟨9905398901602317516577555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13207198535469756688770073 9905398901602317516577555)
        ·
          refine ⟨14858098352403476274866333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905398901602317516577555 14858098352403476274866333)
          ·
            refine ⟨5571786882151303603074875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14858098352403476274866333 5571786882151303603074875)
            ·
              refine ⟨8357680323226955404612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571786882151303603074875 8357680323226955404612313)
              ·
                refine ⟨6268260242420216553459235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8357680323226955404612313 6268260242420216553459235)
                ·
                  refine ⟨9402390363630324830188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268260242420216553459235 9402390363630324830188853)
                  ·
                    refine ⟨881474096590342952830205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9402390363630324830188853 881474096590342952830205)
                    ·
                      rfl

theorem cell23_5149994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5149994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5149994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5149994 prefixEnd_5149994 := by exact prefixLift 5149994
  have htrace : WordTrace (prefixWord ++ tailWord_5149994) baseStart_5149994 baseEnd_5149994 := by
    simpa [prefixWord, tailWord_5149994, baseEnd_5149994] using wordTrace_append hprefix tailTrace_5149994
  have hstable : (prefixWord ++ tailWord_5149994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149994).length < 2 ^ (prefixWord ++ tailWord_5149994).sum := by decide
  have hdescent : baseEnd_5149994 < baseStart_5149994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150000 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_5150000 : Nat := 118140960795 + 5150000 * 2 ^ 59
def prefixEnd_5150000 : Nat := 4983230072969 + 3 ^ 40 * 5150000 * 2
def baseEnd_5150000 : Nat := 2644425370654955835015587

theorem tailTrace_5150000 : CollatzResearch.WordTrace tailWord_5150000 prefixEnd_5150000 2644425370654955835015587 := by
  unfold tailWord_5150000
  simp only [CollatzResearch.WordTrace]
  refine ⟨93917965671218512410279727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125223954228291349880372969 93917965671218512410279727)
  ·
    refine ⟨140876948506827768615419591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93917965671218512410279727 140876948506827768615419591)
    ·
      refine ⟨211315422760241652923129387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140876948506827768615419591 211315422760241652923129387)
      ·
        refine ⟨316973134140362479384694081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211315422760241652923129387 316973134140362479384694081)
        ·
          refine ⟨237729850605271859538520561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316973134140362479384694081 237729850605271859538520561)
          ·
            refine ⟨178297387953953894653890421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237729850605271859538520561 178297387953953894653890421)
            ·
              refine ⟨16715380120683177623802227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178297387953953894653890421 16715380120683177623802227)
              ·
                refine ⟨25073070181024766435703341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16715380120683177623802227 25073070181024766435703341)
                ·
                  refine ⟨9402401317884287413388753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25073070181024766435703341 9402401317884287413388753)
                  ·
                    refine ⟨7051800988413215560041565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9402401317884287413388753 7051800988413215560041565)
                    ·
                      refine ⟨2644425370654955835015587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051800988413215560041565 2644425370654955835015587)
                      ·
                        rfl

theorem cell23_5150000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_5150000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150000 prefixEnd_5150000 := by exact prefixLift 5150000
  have htrace : WordTrace (prefixWord ++ tailWord_5150000) baseStart_5150000 baseEnd_5150000 := by
    simpa [prefixWord, tailWord_5150000, baseEnd_5150000] using wordTrace_append hprefix tailTrace_5150000
  have hstable : (prefixWord ++ tailWord_5150000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150000).length < 2 ^ (prefixWord ++ tailWord_5150000).sum := by decide
  have hdescent : baseEnd_5150000 < baseStart_5150000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150003 : List Nat := [1, 1, 1, 2, 5, 2, 2, 9]
def baseStart_5150003 : Nat := 118140960795 + 5150003 * 2 ^ 59
def prefixEnd_5150003 : Nat := 4983230072969 + 3 ^ 40 * 5150003 * 2
def baseEnd_5150003 : Nat := 97941737448034049010299

theorem tailTrace_5150003 : CollatzResearch.WordTrace tailWord_5150003 prefixEnd_5150003 97941737448034049010299 := by
  unfold tailWord_5150003
  simp only [CollatzResearch.WordTrace]
  refine ⟨187836040761426156332918663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125224027174284104221945775 187836040761426156332918663)
  ·
    refine ⟨281754061142139234499377995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187836040761426156332918663 281754061142139234499377995)
    ·
      refine ⟨422631091713208851749066993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281754061142139234499377995 422631091713208851749066993)
      ·
        refine ⟨316973318784906638811800245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422631091713208851749066993 316973318784906638811800245)
        ·
          refine ⟨29716248636084997388606273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 316973318784906638811800245 29716248636084997388606273)
          ·
            refine ⟨22287186477063748041454705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29716248636084997388606273 22287186477063748041454705)
            ·
              refine ⟨16715389857797811031091029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22287186477063748041454705 16715389857797811031091029)
              ·
                refine ⟨97941737448034049010299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16715389857797811031091029 97941737448034049010299)
                ·
                  rfl

theorem cell23_5150003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 9].length) (baseStart_5150003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150003 prefixEnd_5150003 := by exact prefixLift 5150003
  have htrace : WordTrace (prefixWord ++ tailWord_5150003) baseStart_5150003 baseEnd_5150003 := by
    simpa [prefixWord, tailWord_5150003, baseEnd_5150003] using wordTrace_append hprefix tailTrace_5150003
  have hstable : (prefixWord ++ tailWord_5150003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150003).length < 2 ^ (prefixWord ++ tailWord_5150003).sum := by decide
  have hdescent : baseEnd_5150003 < baseStart_5150003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150010 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_5150010 : Nat := 118140960795 + 5150010 * 2 ^ 59
def prefixEnd_5150010 : Nat := 4983230072969 + 3 ^ 40 * 5150010 * 2
def baseEnd_5150010 : Nat := 2644430505461500795890541

theorem tailTrace_5150010 : CollatzResearch.WordTrace tailWord_5150010 prefixEnd_5150010 2644430505461500795890541 := by
  unfold tailWord_5150010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959074018100199132105871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125224197381600531018948989 46959074018100199132105871)
  ·
    refine ⟨70438611027150298698158807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46959074018100199132105871 70438611027150298698158807)
    ·
      refine ⟨105657916540725448047238211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70438611027150298698158807 105657916540725448047238211)
      ·
        refine ⟨158486874811088172070857317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105657916540725448047238211 158486874811088172070857317)
        ·
          refine ⟨29716289027079032263285747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158486874811088172070857317 29716289027079032263285747)
          ·
            refine ⟨44574433540618548394928621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29716289027079032263285747 44574433540618548394928621)
            ·
              refine ⟨16715412577731955648098233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44574433540618548394928621 16715412577731955648098233)
              ·
                refine ⟨12536559433298966736073675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16715412577731955648098233 12536559433298966736073675)
                ·
                  refine ⟨18804839149948450104110513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12536559433298966736073675 18804839149948450104110513)
                  ·
                    refine ⟨14103629362461337578082885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18804839149948450104110513 14103629362461337578082885)
                    ·
                      refine ⟨2644430505461500795890541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14103629362461337578082885 2644430505461500795890541)
                      ·
                        rfl

theorem cell23_5150010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_5150010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150010 prefixEnd_5150010 := by exact prefixLift 5150010
  have htrace : WordTrace (prefixWord ++ tailWord_5150010) baseStart_5150010 baseEnd_5150010 := by
    simpa [prefixWord, tailWord_5150010, baseEnd_5150010] using wordTrace_append hprefix tailTrace_5150010
  have hstable : (prefixWord ++ tailWord_5150010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150010).length < 2 ^ (prefixWord ++ tailWord_5150010).sum := by decide
  have hdescent : baseEnd_5150010 < baseStart_5150010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150014 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5150014 : Nat := 118140960795 + 5150014 * 2 ^ 59
def prefixEnd_5150014 : Nat := 4983230072969 + 3 ^ 40 * 5150014 * 2
def baseEnd_5150014 : Nat := 2644432559384118780240523

theorem tailTrace_5150014 : CollatzResearch.WordTrace tailWord_5150014 prefixEnd_5150014 2644432559384118780240523 := by
  unfold tailWord_5150014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23479555245548288151446137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125224294642924203474379397 23479555245548288151446137)
  ·
    refine ⟨17609666434161216113584603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23479555245548288151446137 17609666434161216113584603)
    ·
      refine ⟨26414499651241824170376905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17609666434161216113584603 26414499651241824170376905)
      ·
        refine ⟨19810874738431368127782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26414499651241824170376905 19810874738431368127782679)
        ·
          refine ⟨29716312107647052191674019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19810874738431368127782679 29716312107647052191674019)
          ·
            refine ⟨44574468161470578287511029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29716312107647052191674019 44574468161470578287511029)
            ·
              refine ⟨4178856390137866714454159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44574468161470578287511029 4178856390137866714454159)
              ·
                refine ⟨6268284585206800071681239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178856390137866714454159 6268284585206800071681239)
                ·
                  refine ⟨9402426877810200107521859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268284585206800071681239 9402426877810200107521859)
                  ·
                    refine ⟨14103640316715300161282789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402426877810200107521859 14103640316715300161282789)
                    ·
                      refine ⟨2644432559384118780240523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14103640316715300161282789 2644432559384118780240523)
                      ·
                        rfl

theorem cell23_5150014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5150014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150014 prefixEnd_5150014 := by exact prefixLift 5150014
  have htrace : WordTrace (prefixWord ++ tailWord_5150014) baseStart_5150014 baseEnd_5150014 := by
    simpa [prefixWord, tailWord_5150014, baseEnd_5150014] using wordTrace_append hprefix tailTrace_5150014
  have hstable : (prefixWord ++ tailWord_5150014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150014).length < 2 ^ (prefixWord ++ tailWord_5150014).sum := by decide
  have hdescent : baseEnd_5150014 < baseStart_5150014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150017 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5150017 : Nat := 118140960795 + 5150017 * 2 ^ 59
def prefixEnd_5150017 : Nat := 4983230072969 + 3 ^ 40 * 5150017 * 2
def baseEnd_5150017 : Nat := 2644434099826082268503009

theorem tailTrace_5150017 : CollatzResearch.WordTrace tailWord_5150017 prefixEnd_5150017 2644434099826082268503009 := by
  unfold tailWord_5150017
  simp only [CollatzResearch.WordTrace]
  refine ⟨187836551383375436723928305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125224367588916957815952203 187836551383375436723928305)
  ·
    refine ⟨140877413537531577542946229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187836551383375436723928305 140877413537531577542946229)
    ·
      refine ⟨13207257519143585394651209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140877413537531577542946229 13207257519143585394651209)
      ·
        refine ⟨9905443139357689045988407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13207257519143585394651209 9905443139357689045988407)
        ·
          refine ⟨14858164709036533568982611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905443139357689045988407 14858164709036533568982611)
          ·
            refine ⟨22287247063554800353473917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14858164709036533568982611 22287247063554800353473917)
            ·
              refine ⟨8357717648833050132552719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22287247063554800353473917 8357717648833050132552719)
              ·
                refine ⟨12536576473249575198829079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8357717648833050132552719 12536576473249575198829079)
                ·
                  refine ⟨18804864709874362798243619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12536576473249575198829079 18804864709874362798243619)
                  ·
                    refine ⟨28207297064811544197365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18804864709874362798243619 28207297064811544197365429)
                    ·
                      refine ⟨2644434099826082268503009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28207297064811544197365429 2644434099826082268503009)
                      ·
                        rfl

theorem cell23_5150017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5150017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150017 prefixEnd_5150017 := by exact prefixLift 5150017
  have htrace : WordTrace (prefixWord ++ tailWord_5150017) baseStart_5150017 baseEnd_5150017 := by
    simpa [prefixWord, tailWord_5150017, baseEnd_5150017] using wordTrace_append hprefix tailTrace_5150017
  have hstable : (prefixWord ++ tailWord_5150017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150017).length < 2 ^ (prefixWord ++ tailWord_5150017).sum := by decide
  have hdescent : baseEnd_5150017 < baseStart_5150017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150020 : List Nat := [2, 3, 4, 1, 1, 12]
def baseStart_5150020 : Nat := 118140960795 + 5150020 * 2 ^ 59
def prefixEnd_5150020 : Nat := 4983230072969 + 3 ^ 40 * 5150020 * 2
def baseEnd_5150020 : Nat := 10882451194518706817965

theorem tailTrace_5150020 : CollatzResearch.WordTrace tailWord_5150020 prefixEnd_5150020 10882451194518706817965 := by
  unfold tailWord_5150020
  simp only [CollatzResearch.WordTrace]
  refine ⟨93918330401182284118143757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125224440534909712157525009 93918330401182284118143757)
  ·
    refine ⟨35219373900443356544303909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93918330401182284118143757 35219373900443356544303909)
    ·
      refine ⟨6603632606333129352056983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35219373900443356544303909 6603632606333129352056983)
      ·
        refine ⟨9905448909499694028085475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603632606333129352056983 9905448909499694028085475)
        ·
          refine ⟨14858173364249541042128213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905448909499694028085475 14858173364249541042128213)
          ·
            refine ⟨10882451194518706817965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14858173364249541042128213 10882451194518706817965)
            ·
              rfl

theorem cell23_5150020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 12].length) (baseStart_5150020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150020 prefixEnd_5150020 := by exact prefixLift 5150020
  have htrace : WordTrace (prefixWord ++ tailWord_5150020) baseStart_5150020 baseEnd_5150020 := by
    simpa [prefixWord, tailWord_5150020, baseEnd_5150020] using wordTrace_append hprefix tailTrace_5150020
  have hstable : (prefixWord ++ tailWord_5150020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150020).length < 2 ^ (prefixWord ++ tailWord_5150020).sum := by decide
  have hdescent : baseEnd_5150020 < baseStart_5150020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150030 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_5150030 : Nat := 118140960795 + 5150030 * 2 ^ 59
def prefixEnd_5150030 : Nat := 4983230072969 + 3 ^ 40 * 5150030 * 2
def baseEnd_5150030 : Nat := 2644440775074590717640449

theorem tailTrace_5150030 : CollatzResearch.WordTrace tailWord_5150030 prefixEnd_5150030 2644440775074590717640449 := by
  unfold tailWord_5150030
  simp only [CollatzResearch.WordTrace]
  refine ⟨23479628191541042493018943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125224683688218893296101029 23479628191541042493018943)
  ·
    refine ⟨35219442287311563739528415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23479628191541042493018943 35219442287311563739528415)
    ·
      refine ⟨52829163430967345609292623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35219442287311563739528415 52829163430967345609292623)
      ·
        refine ⟨79243745146451018413938935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52829163430967345609292623 79243745146451018413938935)
        ·
          refine ⟨118865617719676527620908403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79243745146451018413938935 118865617719676527620908403)
          ·
            refine ⟨178298426579514791431362605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118865617719676527620908403 178298426579514791431362605)
            ·
              refine ⟨66861909967318046786760977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178298426579514791431362605 66861909967318046786760977)
              ·
                refine ⟨50146432475488535090070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66861909967318046786760977 50146432475488535090070733)
                ·
                  refine ⟨18804912178308200658776525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50146432475488535090070733 18804912178308200658776525)
                  ·
                    refine ⟨7051842066865575247041197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18804912178308200658776525 7051842066865575247041197)
                    ·
                      refine ⟨2644440775074590717640449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051842066865575247041197 2644440775074590717640449)
                      ·
                        rfl

theorem cell23_5150030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_5150030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150030 prefixEnd_5150030 := by exact prefixLift 5150030
  have htrace : WordTrace (prefixWord ++ tailWord_5150030) baseStart_5150030 baseEnd_5150030 := by
    simpa [prefixWord, tailWord_5150030, baseEnd_5150030] using wordTrace_append hprefix tailTrace_5150030
  have hstable : (prefixWord ++ tailWord_5150030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150030).length < 2 ^ (prefixWord ++ tailWord_5150030).sum := by decide
  have hdescent : baseEnd_5150030 < baseStart_5150030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150033 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_5150033 : Nat := 118140960795 + 5150033 * 2 ^ 59
def prefixEnd_5150033 : Nat := 4983230072969 + 3 ^ 40 * 5150033 * 2
def baseEnd_5150033 : Nat := 881480771838851401967645

theorem tailTrace_5150033 : CollatzResearch.WordTrace tailWord_5150033 prefixEnd_5150033 881480771838851401967645 := by
  unfold tailWord_5150033
  simp only [CollatzResearch.WordTrace]
  refine ⟨187837134951317471456510753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125224756634211647637673835 187837134951317471456510753)
  ·
    refine ⟨140877851213488103592383065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187837134951317471456510753 140877851213488103592383065)
    ·
      refine ⟨105658388410116077694287299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140877851213488103592383065 105658388410116077694287299)
      ·
        refine ⟨158487582615174116541430949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105658388410116077694287299 158487582615174116541430949)
        ·
          refine ⟨29716421740345146851518303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158487582615174116541430949 29716421740345146851518303)
          ·
            refine ⟨44574632610517720277277455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29716421740345146851518303 44574632610517720277277455)
            ·
              refine ⟨66861948915776580415916183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44574632610517720277277455 66861948915776580415916183)
              ·
                refine ⟨100292923373664870623874275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66861948915776580415916183 100292923373664870623874275)
                ·
                  refine ⟨150439385060497305935811413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100292923373664870623874275 150439385060497305935811413)
                  ·
                    refine ⟨881480771838851401967645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150439385060497305935811413 881480771838851401967645)
                    ·
                      rfl

theorem cell23_5150033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_5150033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150033 prefixEnd_5150033 := by exact prefixLift 5150033
  have htrace : WordTrace (prefixWord ++ tailWord_5150033) baseStart_5150033 baseEnd_5150033 := by
    simpa [prefixWord, tailWord_5150033, baseEnd_5150033] using wordTrace_append hprefix tailTrace_5150033
  have hstable : (prefixWord ++ tailWord_5150033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150033).length < 2 ^ (prefixWord ++ tailWord_5150033).sum := by decide
  have hdescent : baseEnd_5150033 < baseStart_5150033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150050 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5150050 : Nat := 118140960795 + 5150050 * 2 ^ 59
def prefixEnd_5150050 : Nat := 4983230072969 + 3 ^ 40 * 5150050 * 2
def baseEnd_5150050 : Nat := 881483681562560213130119

theorem tailTrace_5150050 : CollatzResearch.WordTrace tailWord_5150050 prefixEnd_5150050 881483681562560213130119 := by
  unfold tailWord_5150050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959438748063970839969901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125225169994837255573253069 46959438748063970839969901)
  ·
    refine ⟨17609789530523989064988713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46959438748063970839969901 17609789530523989064988713)
    ·
      refine ⟨13207342147892991798741535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17609789530523989064988713 13207342147892991798741535)
      ·
        refine ⟨19811013221839487698112303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13207342147892991798741535 19811013221839487698112303)
        ·
          refine ⟨29716519832759231547168455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19811013221839487698112303 29716519832759231547168455)
          ·
            refine ⟨44574779749138847320752683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29716519832759231547168455 44574779749138847320752683)
            ·
              refine ⟨66862169623708270981129025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44574779749138847320752683 66862169623708270981129025)
              ·
                refine ⟨50146627217781203235846769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66862169623708270981129025 50146627217781203235846769)
                ·
                  refine ⟨37609970413335902426885077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50146627217781203235846769 37609970413335902426885077)
                  ·
                    refine ⟨881483681562560213130119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37609970413335902426885077 881483681562560213130119)
                    ·
                      rfl

theorem cell23_5150050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5150050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150050 prefixEnd_5150050 := by exact prefixLift 5150050
  have htrace : WordTrace (prefixWord ++ tailWord_5150050) baseStart_5150050 baseEnd_5150050 := by
    simpa [prefixWord, tailWord_5150050, baseEnd_5150050] using wordTrace_append hprefix tailTrace_5150050
  have hstable : (prefixWord ++ tailWord_5150050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150050).length < 2 ^ (prefixWord ++ tailWord_5150050).sum := by decide
  have hdescent : baseEnd_5150050 < baseStart_5150050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150063 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 8]
def baseStart_5150063 : Nat := 118140960795 + 5150063 * 2 ^ 59
def prefixEnd_5150063 : Nat := 4983230072969 + 3 ^ 40 * 5150063 * 2
def baseEnd_5150063 : Nat := 881485906645396362842599

theorem tailTrace_5150063 : CollatzResearch.WordTrace tailWord_5150063 prefixEnd_5150063 881485906645396362842599 := by
  unfold tailWord_5150063
  simp only [CollatzResearch.WordTrace]
  refine ⟨187838229141208786580102843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125225486094139191053401895 187838229141208786580102843)
  ·
    refine ⟨281757343711813179870154265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187838229141208786580102843 281757343711813179870154265)
    ·
      refine ⟨211318007783859884902615699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281757343711813179870154265 211318007783859884902615699)
      ·
        refine ⟨316977011675789827353923549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211318007783859884902615699 316977011675789827353923549)
        ·
          refine ⟨118866379378421185257721331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316977011675789827353923549 118866379378421185257721331)
          ·
            refine ⟨178299569067631777886581997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118866379378421185257721331 178299569067631777886581997)
            ·
              refine ⟨66862338400361916707468249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178299569067631777886581997 66862338400361916707468249)
              ·
                refine ⟨50146753800271437530601187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66862338400361916707468249 50146753800271437530601187)
                ·
                  refine ⟨75220130700407156295901781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50146753800271437530601187 75220130700407156295901781)
                  ·
                    refine ⟨881485906645396362842599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75220130700407156295901781 881485906645396362842599)
                    ·
                      rfl

theorem cell23_5150063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_5150063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150063 prefixEnd_5150063 := by exact prefixLift 5150063
  have htrace : WordTrace (prefixWord ++ tailWord_5150063) baseStart_5150063 baseEnd_5150063 := by
    simpa [prefixWord, tailWord_5150063, baseEnd_5150063] using wordTrace_append hprefix tailTrace_5150063
  have hstable : (prefixWord ++ tailWord_5150063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150063).length < 2 ^ (prefixWord ++ tailWord_5150063).sum := by decide
  have hdescent : baseEnd_5150063 < baseStart_5150063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150098 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5150098 : Nat := 118140960795 + 5150098 * 2 ^ 59
def prefixEnd_5150098 : Nat := 4983230072969 + 3 ^ 40 * 5150098 * 2
def baseEnd_5150098 : Nat := 2644475691759096451590137

theorem tailTrace_5150098 : CollatzResearch.WordTrace tailWord_5150098 prefixEnd_5150098 2644475691759096451590137 := by
  unfold tailWord_5150098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959876424020496889406737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125226337130721325038417965 46959876424020496889406737)
  ·
    refine ⟨35219907318015372667055053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46959876424020496889406737 35219907318015372667055053)
    ·
      refine ⟨13207465244255764750145645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35219907318015372667055053 13207465244255764750145645)
      ·
        refine ⟨4952799466595911781304617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13207465244255764750145645 4952799466595911781304617)
        ·
          refine ⟨3714599599946933835978463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952799466595911781304617 3714599599946933835978463)
          ·
            refine ⟨5571899399920400753967695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714599599946933835978463 5571899399920400753967695)
            ·
              refine ⟨8357849099880601130951543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571899399920400753967695 8357849099880601130951543)
              ·
                refine ⟨12536773649820901696427315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8357849099880601130951543 12536773649820901696427315)
                ·
                  refine ⟨18805160474731352544640973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12536773649820901696427315 18805160474731352544640973)
                  ·
                    refine ⟨7051935178024257204240365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18805160474731352544640973 7051935178024257204240365)
                    ·
                      refine ⟨2644475691759096451590137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7051935178024257204240365 2644475691759096451590137)
                      ·
                        rfl

theorem cell23_5150098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5150098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150098 prefixEnd_5150098 := by exact prefixLift 5150098
  have htrace : WordTrace (prefixWord ++ tailWord_5150098) baseStart_5150098 baseEnd_5150098 := by
    simpa [prefixWord, tailWord_5150098, baseEnd_5150098] using wordTrace_append hprefix tailTrace_5150098
  have hstable : (prefixWord ++ tailWord_5150098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150098).length < 2 ^ (prefixWord ++ tailWord_5150098).sum := by decide
  have hdescent : baseEnd_5150098 < baseStart_5150098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150108 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5150108 : Nat := 118140960795 + 5150108 * 2 ^ 59
def prefixEnd_5150108 : Nat := 4983230072969 + 3 ^ 40 * 5150108 * 2
def baseEnd_5150108 : Nat := 2644480826565641412465091

theorem tailTrace_5150108 : CollatzResearch.WordTrace tailWord_5150108 prefixEnd_5150108 2644480826565641412465091 := by
  unfold tailWord_5150108
  simp only [CollatzResearch.WordTrace]
  refine ⟨93919935213022879632745489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125226580284030506176993985 93919935213022879632745489)
  ·
    refine ⟨70439951409767159724559117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93919935213022879632745489 70439951409767159724559117)
    ·
      refine ⟨26414981778662684896709669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70439951409767159724559117 26414981778662684896709669)
      ·
        refine ⟨4952809083499253418133063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26414981778662684896709669 4952809083499253418133063)
        ·
          refine ⟨7429213625248880127199595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952809083499253418133063 7429213625248880127199595)
          ·
            refine ⟨11143820437873320190799393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429213625248880127199595 11143820437873320190799393)
            ·
              refine ⟨8357865328404990143099545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11143820437873320190799393 8357865328404990143099545)
              ·
                refine ⟨6268398996303742607324659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8357865328404990143099545 6268398996303742607324659)
                ·
                  refine ⟨9402598494455613910986989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268398996303742607324659 9402598494455613910986989)
                  ·
                    refine ⟨3525974435420855216620121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9402598494455613910986989 3525974435420855216620121)
                    ·
                      refine ⟨2644480826565641412465091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525974435420855216620121 2644480826565641412465091)
                      ·
                        rfl

theorem cell23_5150108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5150108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150108 prefixEnd_5150108 := by exact prefixLift 5150108
  have htrace : WordTrace (prefixWord ++ tailWord_5150108) baseStart_5150108 baseEnd_5150108 := by
    simpa [prefixWord, tailWord_5150108, baseEnd_5150108] using wordTrace_append hprefix tailTrace_5150108
  have hstable : (prefixWord ++ tailWord_5150108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150108).length < 2 ^ (prefixWord ++ tailWord_5150108).sum := by decide
  have hdescent : baseEnd_5150108 < baseStart_5150108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150177 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_5150177 : Nat := 118140960795 + 5150177 * 2 ^ 59
def prefixEnd_5150177 : Nat := 4983230072969 + 3 ^ 40 * 5150177 * 2
def baseEnd_5150177 : Nat := 2644516256730801642502273

theorem tailTrace_5150177 : CollatzResearch.WordTrace tailWord_5150177 prefixEnd_5150177 2644516256730801642502273 := by
  unfold tailWord_5150177
  simp only [CollatzResearch.WordTrace]
  refine ⟨187842387062795784049752785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125228258041863856033168523 187842387062795784049752785)
  ·
    refine ⟨140881790297096838037314589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187842387062795784049752785 140881790297096838037314589)
    ·
      refine ⟨52830671361411314263992971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140881790297096838037314589 52830671361411314263992971)
      ·
        refine ⟨79246007042116971395989457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52830671361411314263992971 79246007042116971395989457)
        ·
          refine ⟨59434505281587728546992093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79246007042116971395989457 59434505281587728546992093)
          ·
            refine ⟨22287939480595398205122035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59434505281587728546992093 22287939480595398205122035)
            ·
              refine ⟨33431909220893097307683053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22287939480595398205122035 33431909220893097307683053)
              ·
                refine ⟨12536965957834911490381145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33431909220893097307683053 12536965957834911490381145)
                ·
                  refine ⟨9402724468376183617785859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12536965957834911490381145 9402724468376183617785859)
                  ·
                    refine ⟨14104086702564275426678789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402724468376183617785859 14104086702564275426678789)
                    ·
                      refine ⟨2644516256730801642502273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104086702564275426678789 2644516256730801642502273)
                      ·
                        rfl

theorem cell23_5150177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_5150177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150177 prefixEnd_5150177 := by exact prefixLift 5150177
  have htrace : WordTrace (prefixWord ++ tailWord_5150177) baseStart_5150177 baseEnd_5150177 := by
    simpa [prefixWord, tailWord_5150177, baseEnd_5150177] using wordTrace_append hprefix tailTrace_5150177
  have hstable : (prefixWord ++ tailWord_5150177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150177).length < 2 ^ (prefixWord ++ tailWord_5150177).sum := by decide
  have hdescent : baseEnd_5150177 < baseStart_5150177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150194 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5150194 : Nat := 118140960795 + 5150194 * 2 ^ 59
def prefixEnd_5150194 : Nat := 4983230072969 + 3 ^ 40 * 5150194 * 2
def baseEnd_5150194 : Nat := 2644524985901928075989695

theorem tailTrace_5150194 : CollatzResearch.WordTrace tailWord_5150194 prefixEnd_5150194 2644524985901928075989695 := by
  unfold tailWord_5150194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46960751775933548988280409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125228671402489463968747757 46960751775933548988280409)
  ·
    refine ⟨35220563831950161741210307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46960751775933548988280409 35220563831950161741210307)
    ·
      refine ⟨52830845747925242611815461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35220563831950161741210307 52830845747925242611815461)
      ·
        refine ⟨9905783577735982989715399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52830845747925242611815461 9905783577735982989715399)
        ·
          refine ⟨14858675366603974484573099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905783577735982989715399 14858675366603974484573099)
          ·
            refine ⟨22288013049905961726859649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14858675366603974484573099 22288013049905961726859649)
            ·
              refine ⟨16716009787429471295144737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22288013049905961726859649 16716009787429471295144737)
              ·
                refine ⟨12537007340572103471358553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16716009787429471295144737 12537007340572103471358553)
                ·
                  refine ⟨9402755505429077603518915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12537007340572103471358553 9402755505429077603518915)
                  ·
                    refine ⟨14104133258143616405278373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402755505429077603518915 14104133258143616405278373)
                    ·
                      refine ⟨2644524985901928075989695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104133258143616405278373 2644524985901928075989695)
                      ·
                        rfl

theorem cell23_5150194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5150194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150194 prefixEnd_5150194 := by exact prefixLift 5150194
  have htrace : WordTrace (prefixWord ++ tailWord_5150194) baseStart_5150194 baseEnd_5150194 := by
    simpa [prefixWord, tailWord_5150194, baseEnd_5150194] using wordTrace_append hprefix tailTrace_5150194
  have hstable : (prefixWord ++ tailWord_5150194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150194).length < 2 ^ (prefixWord ++ tailWord_5150194).sum := by decide
  have hdescent : baseEnd_5150194 < baseStart_5150194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150228 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5150228 : Nat := 118140960795 + 5150228 * 2 ^ 59
def prefixEnd_5150228 : Nat := 4983230072969 + 3 ^ 40 * 5150228 * 2
def baseEnd_5150228 : Nat := 2644542444244180942964539

theorem tailTrace_5150228 : CollatzResearch.WordTrace tailWord_5150228 prefixEnd_5150228 2644542444244180942964539 := by
  unfold tailWord_5150228
  simp only [CollatzResearch.WordTrace]
  refine ⟨93922123592805509879929669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125229498123740679839906225 93922123592805509879929669)
  ·
    refine ⟨17610398173651033102486813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93922123592805509879929669 17610398173651033102486813)
    ·
      refine ⟨6603899315119137413432555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17610398173651033102486813 6603899315119137413432555)
      ·
        refine ⟨9905848972678706120148833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603899315119137413432555 9905848972678706120148833)
        ·
          refine ⟨7429386729509029590111625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9905848972678706120148833 7429386729509029590111625)
          ·
            refine ⟨5572040047131772192583719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7429386729509029590111625 5572040047131772192583719)
            ·
              refine ⟨8358060070697658288875579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572040047131772192583719 8358060070697658288875579)
              ·
                refine ⟨12537090106046487433313369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358060070697658288875579 12537090106046487433313369)
                ·
                  refine ⟨9402817579534865574985027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12537090106046487433313369 9402817579534865574985027)
                  ·
                    refine ⟨14104226369302298362477541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402817579534865574985027 14104226369302298362477541)
                    ·
                      refine ⟨2644542444244180942964539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104226369302298362477541 2644542444244180942964539)
                      ·
                        rfl

theorem cell23_5150228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5150228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150228 prefixEnd_5150228 := by exact prefixLift 5150228
  have htrace : WordTrace (prefixWord ++ tailWord_5150228) baseStart_5150228 baseEnd_5150228 := by
    simpa [prefixWord, tailWord_5150228, baseEnd_5150228] using wordTrace_append hprefix tailTrace_5150228
  have hstable : (prefixWord ++ tailWord_5150228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150228).length < 2 ^ (prefixWord ++ tailWord_5150228).sum := by decide
  have hdescent : baseEnd_5150228 < baseStart_5150228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150261 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_5150261 : Nat := 118140960795 + 5150261 * 2 ^ 59
def prefixEnd_5150261 : Nat := 4983230072969 + 3 ^ 40 * 5150261 * 2
def baseEnd_5150261 : Nat := 2644559389105779313851887

theorem tailTrace_5150261 : CollatzResearch.WordTrace tailWord_5150261 prefixEnd_5150261 2644559389105779313851887 := by
  unfold tailWord_5150261
  simp only [CollatzResearch.WordTrace]
  refine ⟨187845450794491466395810637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125230300529660977597207091 187845450794491466395810637)
  ·
    refine ⟨70442044047934299898428989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187845450794491466395810637 70442044047934299898428989)
    ·
      refine ⟨26415766517975362461910871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70442044047934299898428989 26415766517975362461910871)
      ·
        refine ⟨39623649776963043692866307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26415766517975362461910871 39623649776963043692866307)
        ·
          refine ⟨59435474665444565539299461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39623649776963043692866307 59435474665444565539299461)
          ·
            refine ⟨11144151499770856038618649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59435474665444565539299461 11144151499770856038618649)
            ·
              refine ⟨8358113624828142028963987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11144151499770856038618649 8358113624828142028963987)
              ·
                refine ⟨12537170437242213043445981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358113624828142028963987 12537170437242213043445981)
                ·
                  refine ⟨4701438913965829891292243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12537170437242213043445981 4701438913965829891292243)
                  ·
                    refine ⟨7052158370948744836938365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4701438913965829891292243 7052158370948744836938365)
                    ·
                      refine ⟨2644559389105779313851887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7052158370948744836938365 2644559389105779313851887)
                      ·
                        rfl

theorem cell23_5150261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_5150261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150261 prefixEnd_5150261 := by exact prefixLift 5150261
  have htrace : WordTrace (prefixWord ++ tailWord_5150261) baseStart_5150261 baseEnd_5150261 := by
    simpa [prefixWord, tailWord_5150261, baseEnd_5150261] using wordTrace_append hprefix tailTrace_5150261
  have hstable : (prefixWord ++ tailWord_5150261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150261).length < 2 ^ (prefixWord ++ tailWord_5150261).sum := by decide
  have hdescent : baseEnd_5150261 < baseStart_5150261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150284 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5150284 : Nat := 118140960795 + 5150284 * 2 ^ 59
def prefixEnd_5150284 : Nat := 4983230072969 + 3 ^ 40 * 5150284 * 2
def baseEnd_5150284 : Nat := 2644571199160832723864281

theorem tailTrace_5150284 : CollatzResearch.WordTrace tailWord_5150284 prefixEnd_5150284 2644571199160832723864281 := by
  unfold tailWord_5150284
  simp only [CollatzResearch.WordTrace]
  refine ⟨93923144836704070661948953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125230859782272094215931937 93923144836704070661948953)
  ·
    refine ⟨70442358627528052996461715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93923144836704070661948953 70442358627528052996461715)
    ·
      refine ⟨105663537941292079494692573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70442358627528052996461715 105663537941292079494692573)
      ·
        refine ⟨39623826727984529810509715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105663537941292079494692573 39623826727984529810509715)
        ·
          refine ⟨59435740091976794715764573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39623826727984529810509715 59435740091976794715764573)
          ·
            refine ⟨22288402534491298018411715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59435740091976794715764573 22288402534491298018411715)
            ·
              refine ⟨33432603801736947027617573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22288402534491298018411715 33432603801736947027617573)
              ·
                refine ⟨6268613212825677567678295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33432603801736947027617573 6268613212825677567678295)
                ·
                  refine ⟨9402919819238516351517443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268613212825677567678295 9402919819238516351517443)
                  ·
                    refine ⟨14104379728857774527276165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9402919819238516351517443 14104379728857774527276165)
                    ·
                      refine ⟨2644571199160832723864281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104379728857774527276165 2644571199160832723864281)
                      ·
                        rfl

theorem cell23_5150284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5150284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150284 prefixEnd_5150284 := by exact prefixLift 5150284
  have htrace : WordTrace (prefixWord ++ tailWord_5150284) baseStart_5150284 baseEnd_5150284 := by
    simpa [prefixWord, tailWord_5150284, baseEnd_5150284] using wordTrace_append hprefix tailTrace_5150284
  have hstable : (prefixWord ++ tailWord_5150284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150284).length < 2 ^ (prefixWord ++ tailWord_5150284).sum := by decide
  have hdescent : baseEnd_5150284 < baseStart_5150284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150297 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_5150297 : Nat := 118140960795 + 5150297 * 2 ^ 59
def prefixEnd_5150297 : Nat := 4983230072969 + 3 ^ 40 * 5150297 * 2
def baseEnd_5150297 : Nat := 2644577874409341173001721

theorem tailTrace_5150297 : CollatzResearch.WordTrace tailWord_5150297 prefixEnd_5150297 2644577874409341173001721 := by
  unfold tailWord_5150297
  simp only [CollatzResearch.WordTrace]
  refine ⟨187846763822361044544121145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125231175881574029696080763 187846763822361044544121145)
  ·
    refine ⟨140885072866770783408090859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187846763822361044544121145 140885072866770783408090859)
    ·
      refine ⟨211327609300156175112136289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140885072866770783408090859 211327609300156175112136289)
      ·
        refine ⟨158495706975117131334102217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211327609300156175112136289 158495706975117131334102217)
        ·
          refine ⟨118871780231337848500576663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158495706975117131334102217 118871780231337848500576663)
          ·
            refine ⟨178307670347006772750864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118871780231337848500576663 178307670347006772750864995)
            ·
              refine ⟨267461505520510159126297493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178307670347006772750864995 267461505520510159126297493)
              ·
                refine ⟨12537258071273913709045195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267461505520510159126297493 12537258071273913709045195)
                ·
                  refine ⟨18805887106910870563567793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12537258071273913709045195 18805887106910870563567793)
                  ·
                    refine ⟨14104415330183152922675845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18805887106910870563567793 14104415330183152922675845)
                    ·
                      refine ⟨2644577874409341173001721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104415330183152922675845 2644577874409341173001721)
                      ·
                        rfl

theorem cell23_5150297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_5150297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150297 prefixEnd_5150297 := by exact prefixLift 5150297
  have htrace : WordTrace (prefixWord ++ tailWord_5150297) baseStart_5150297 baseEnd_5150297 := by
    simpa [prefixWord, tailWord_5150297, baseEnd_5150297] using wordTrace_append hprefix tailTrace_5150297
  have hstable : (prefixWord ++ tailWord_5150297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150297).length < 2 ^ (prefixWord ++ tailWord_5150297).sum := by decide
  have hdescent : baseEnd_5150297 < baseStart_5150297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150307 : List Nat := [1, 1, 1, 5, 1, 5, 9]
def baseStart_5150307 : Nat := 118140960795 + 5150307 * 2 ^ 59
def prefixEnd_5150307 : Nat := 4983230072969 + 3 ^ 40 * 5150307 * 2
def baseEnd_5150307 : Nat := 32649172953282544862675

theorem tailTrace_5150307 : CollatzResearch.WordTrace tailWord_5150307 prefixEnd_5150307 32649172953282544862675 := by
  unfold tailWord_5150307
  simp only [CollatzResearch.WordTrace]
  refine ⟨187847128552324816251985175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125231419034883210834656783 187847128552324816251985175)
  ·
    refine ⟨281770692828487224377977763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187847128552324816251985175 281770692828487224377977763)
    ·
      refine ⟨422656039242730836566966645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281770692828487224377977763 422656039242730836566966645)
      ·
        refine ⟨39624003679006015928153123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422656039242730836566966645 39624003679006015928153123)
        ·
          refine ⟨59436005518509023892229685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39624003679006015928153123 59436005518509023892229685)
          ·
            refine ⟨5572125517360220989896533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59436005518509023892229685 5572125517360220989896533)
            ·
              refine ⟨32649172953282544862675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5572125517360220989896533 32649172953282544862675)
              ·
                rfl

theorem cell23_5150307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 9].length) (baseStart_5150307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150307 prefixEnd_5150307 := by exact prefixLift 5150307
  have htrace : WordTrace (prefixWord ++ tailWord_5150307) baseStart_5150307 baseEnd_5150307 := by
    simpa [prefixWord, tailWord_5150307, baseEnd_5150307] using wordTrace_append hprefix tailTrace_5150307
  have hstable : (prefixWord ++ tailWord_5150307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150307).length < 2 ^ (prefixWord ++ tailWord_5150307).sum := by decide
  have hdescent : baseEnd_5150307 < baseStart_5150307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150357 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_5150357 : Nat := 118140960795 + 5150357 * 2 ^ 59
def prefixEnd_5150357 : Nat := 4983230072969 + 3 ^ 40 * 5150357 * 2
def baseEnd_5150357 : Nat := 2644608683248610938251445

theorem tailTrace_5150357 : CollatzResearch.WordTrace tailWord_5150357 prefixEnd_5150357 2644608683248610938251445 := by
  unfold tailWord_5150357
  simp only [CollatzResearch.WordTrace]
  refine ⟨187848952202143674791305325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125232634801429116527536883 187848952202143674791305325)
  ·
    refine ⟨70443357075803878046739497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187848952202143674791305325 70443357075803878046739497)
    ·
      refine ⟨52832517806852908535054623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70443357075803878046739497 52832517806852908535054623)
      ·
        refine ⟨79248776710279362802581935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52832517806852908535054623 79248776710279362802581935)
        ·
          refine ⟨118873165065419044203872903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79248776710279362802581935 118873165065419044203872903)
          ·
            refine ⟨178309747598128566305809355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118873165065419044203872903 178309747598128566305809355)
            ·
              refine ⟨267464621397192849458714033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178309747598128566305809355 267464621397192849458714033)
              ·
                refine ⟨200598466047894637094035525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267464621397192849458714033 200598466047894637094035525)
                ·
                  refine ⟨37612212383980244455131661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200598466047894637094035525 37612212383980244455131661)
                  ·
                    refine ⟨14104579643992591670674373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37612212383980244455131661 14104579643992591670674373)
                    ·
                      refine ⟨2644608683248610938251445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104579643992591670674373 2644608683248610938251445)
                      ·
                        rfl

theorem cell23_5150357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_5150357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150357 prefixEnd_5150357 := by exact prefixLift 5150357
  have htrace : WordTrace (prefixWord ++ tailWord_5150357) baseStart_5150357 baseEnd_5150357 := by
    simpa [prefixWord, tailWord_5150357, baseEnd_5150357] using wordTrace_append hprefix tailTrace_5150357
  have hstable : (prefixWord ++ tailWord_5150357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150357).length < 2 ^ (prefixWord ++ tailWord_5150357).sum := by decide
  have hdescent : baseEnd_5150357 < baseStart_5150357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150368 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_5150368 : Nat := 118140960795 + 5150368 * 2 ^ 59
def prefixEnd_5150368 : Nat := 4983230072969 + 3 ^ 40 * 5150368 * 2
def baseEnd_5150368 : Nat := 2644614331535810395213895

theorem tailTrace_5150368 : CollatzResearch.WordTrace tailWord_5150368 prefixEnd_5150368 2644614331535810395213895 := by
  unfold tailWord_5150368
  simp only [CollatzResearch.WordTrace]
  refine ⟨93924676702551911834977879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125232902270069215779970505 93924676702551911834977879)
  ·
    refine ⟨140887015053827867752466819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93924676702551911834977879 140887015053827867752466819)
    ·
      refine ⟨211330522580741801628700229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140887015053827867752466819 211330522580741801628700229)
      ·
        refine ⟨39624472983889087805381293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211330522580741801628700229 39624472983889087805381293)
        ·
          refine ⟨14859177368958407927017985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39624472983889087805381293 14859177368958407927017985)
          ·
            refine ⟨11144383026718805945263489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14859177368958407927017985 11144383026718805945263489)
            ·
              refine ⟨8358287270039104458947617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11144383026718805945263489 8358287270039104458947617)
              ·
                refine ⟨6268715452529328344210713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8358287270039104458947617 6268715452529328344210713)
                ·
                  refine ⟨4701536589396996258158035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6268715452529328344210713 4701536589396996258158035)
                  ·
                    refine ⟨7052304884095494387237053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4701536589396996258158035 7052304884095494387237053)
                    ·
                      refine ⟨2644614331535810395213895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7052304884095494387237053 2644614331535810395213895)
                      ·
                        rfl

theorem cell23_5150368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_5150368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150368 prefixEnd_5150368 := by exact prefixLift 5150368
  have htrace : WordTrace (prefixWord ++ tailWord_5150368) baseStart_5150368 baseEnd_5150368 := by
    simpa [prefixWord, tailWord_5150368, baseEnd_5150368] using wordTrace_append hprefix tailTrace_5150368
  have hstable : (prefixWord ++ tailWord_5150368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150368).length < 2 ^ (prefixWord ++ tailWord_5150368).sum := by decide
  have hdescent : baseEnd_5150368 < baseStart_5150368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150391 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_5150391 : Nat := 118140960795 + 5150391 * 2 ^ 59
def prefixEnd_5150391 : Nat := 4983230072969 + 3 ^ 40 * 5150391 * 2
def baseEnd_5150391 : Nat := 2644626141590863805226289

theorem tailTrace_5150391 : CollatzResearch.WordTrace tailWord_5150391 prefixEnd_5150391 2644626141590863805226289 := by
  unfold tailWord_5150391
  simp only [CollatzResearch.WordTrace]
  refine ⟨187850192284020498598043027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125233461522680332398695351 187850192284020498598043027)
  ·
    refine ⟨281775288426030747897064541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187850192284020498598043027 281775288426030747897064541)
    ·
      refine ⟨105665733159761530461399203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281775288426030747897064541 105665733159761530461399203)
      ·
        refine ⟨158498599739642295692098805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105665733159761530461399203 158498599739642295692098805)
        ·
          refine ⟨14859243725591465221134263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158498599739642295692098805 14859243725591465221134263)
          ·
            refine ⟨22288865588387197831701395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14859243725591465221134263 22288865588387197831701395)
            ·
              refine ⟨33433298382580796747552093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22288865588387197831701395 33433298382580796747552093)
              ·
                refine ⟨12537486893467798780332035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33433298382580796747552093 12537486893467798780332035)
                ·
                  refine ⟨18806230340201698170498053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12537486893467798780332035 18806230340201698170498053)
                  ·
                    refine ⟨3526168188787818406968385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18806230340201698170498053 3526168188787818406968385)
                    ·
                      refine ⟨2644626141590863805226289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526168188787818406968385 2644626141590863805226289)
                      ·
                        rfl

theorem cell23_5150391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_5150391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150391 prefixEnd_5150391 := by exact prefixLift 5150391
  have htrace : WordTrace (prefixWord ++ tailWord_5150391) baseStart_5150391 baseEnd_5150391 := by
    simpa [prefixWord, tailWord_5150391, baseEnd_5150391] using wordTrace_append hprefix tailTrace_5150391
  have hstable : (prefixWord ++ tailWord_5150391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150391).length < 2 ^ (prefixWord ++ tailWord_5150391).sum := by decide
  have hdescent : baseEnd_5150391 < baseStart_5150391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150404 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5150404 : Nat := 118140960795 + 5150404 * 2 ^ 59
def prefixEnd_5150404 : Nat := 4983230072969 + 3 ^ 40 * 5150404 * 2
def baseEnd_5150404 : Nat := 2644632816839372254363729

theorem tailTrace_5150404 : CollatzResearch.WordTrace tailWord_5150404 prefixEnd_5150404 2644632816839372254363729 := by
  unfold tailWord_5150404
  simp only [CollatzResearch.WordTrace]
  refine ⟨93925333216486700909133133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125233777621982267878844177 93925333216486700909133133)
  ·
    refine ⟨35221999956182512840924925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93925333216486700909133133 35221999956182512840924925)
    ·
      refine ⟨13208249983568442315346847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35221999956182512840924925 13208249983568442315346847)
      ·
        refine ⟨19812374975352663473020271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13208249983568442315346847 19812374975352663473020271)
        ·
          refine ⟨29718562463028995209530407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19812374975352663473020271 29718562463028995209530407)
          ·
            refine ⟨44577843694543492814295611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29718562463028995209530407 44577843694543492814295611)
            ·
              refine ⟨66866765541815239221443417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44577843694543492814295611 66866765541815239221443417)
              ·
                refine ⟨50150074156361429416082563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66866765541815239221443417 50150074156361429416082563)
                ·
                  refine ⟨75225111234542144124123845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50150074156361429416082563 75225111234542144124123845)
                  ·
                    refine ⟨14104708356476652023273221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75225111234542144124123845 14104708356476652023273221)
                    ·
                      refine ⟨2644632816839372254363729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14104708356476652023273221 2644632816839372254363729)
                      ·
                        rfl

theorem cell23_5150404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5150404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150404 prefixEnd_5150404 := by exact prefixLift 5150404
  have htrace : WordTrace (prefixWord ++ tailWord_5150404) baseStart_5150404 baseEnd_5150404 := by
    simpa [prefixWord, tailWord_5150404, baseEnd_5150404] using wordTrace_append hprefix tailTrace_5150404
  have hstable : (prefixWord ++ tailWord_5150404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150404).length < 2 ^ (prefixWord ++ tailWord_5150404).sum := by decide
  have hdescent : baseEnd_5150404 < baseStart_5150404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150412 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5150412 : Nat := 118140960795 + 5150412 * 2 ^ 59
def prefixEnd_5150412 : Nat := 4983230072969 + 3 ^ 40 * 5150412 * 2
def baseEnd_5150412 : Nat := 2644636924684608223063693

theorem tailTrace_5150412 : CollatzResearch.WordTrace tailWord_5150412 prefixEnd_5150412 2644636924684608223063693 := by
  unfold tailWord_5150412
  simp only [CollatzResearch.WordTrace]
  refine ⟨93925479108472209592278745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125233972144629612789704993 93925479108472209592278745)
  ·
    refine ⟨70444109331354157194209059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93925479108472209592278745 70444109331354157194209059)
    ·
      refine ⟨105666163997031235791313589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70444109331354157194209059 105666163997031235791313589)
      ·
        refine ⟨9906202874721678355435649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105666163997031235791313589 9906202874721678355435649)
        ·
          refine ⟨7429652156041258766576737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9906202874721678355435649 7429652156041258766576737)
          ·
            refine ⟨5572239117030944074932553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7429652156041258766576737 5572239117030944074932553)
            ·
              refine ⟨4179179337773208056199415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572239117030944074932553 4179179337773208056199415)
              ·
                refine ⟨6268769006659812084299123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179179337773208056199415 6268769006659812084299123)
                ·
                  refine ⟨9403153509989718126448685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268769006659812084299123 9403153509989718126448685)
                  ·
                    refine ⟨3526182566246144297418257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9403153509989718126448685 3526182566246144297418257)
                    ·
                      refine ⟨2644636924684608223063693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526182566246144297418257 2644636924684608223063693)
                      ·
                        rfl

theorem cell23_5150412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5150412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150412 prefixEnd_5150412 := by exact prefixLift 5150412
  have htrace : WordTrace (prefixWord ++ tailWord_5150412) baseStart_5150412 baseEnd_5150412 := by
    simpa [prefixWord, tailWord_5150412, baseEnd_5150412] using wordTrace_append hprefix tailTrace_5150412
  have hstable : (prefixWord ++ tailWord_5150412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150412).length < 2 ^ (prefixWord ++ tailWord_5150412).sum := by decide
  have hdescent : baseEnd_5150412 < baseStart_5150412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150424 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5150424 : Nat := 118140960795 + 5150424 * 2 ^ 59
def prefixEnd_5150424 : Nat := 4983230072969 + 3 ^ 40 * 5150424 * 2
def baseEnd_5150424 : Nat := 2644643086452462176113637

theorem tailTrace_5150424 : CollatzResearch.WordTrace tailWord_5150424 prefixEnd_5150424 2644643086452462176113637 := by
  unfold tailWord_5150424
  simp only [CollatzResearch.WordTrace]
  refine ⟨93925697946450472616997163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125234263928600630155996217 93925697946450472616997163)
  ·
    refine ⟨140888546919675708925495745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93925697946450472616997163 140888546919675708925495745)
    ·
      refine ⟨105666410189756781694121809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140888546919675708925495745 105666410189756781694121809)
      ·
        refine ⟨79249807642317586270591357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105666410189756781694121809 79249807642317586270591357)
        ·
          refine ⟨29718677865869094851471759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79249807642317586270591357 29718677865869094851471759)
          ·
            refine ⟨44578016798803642277207639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29718677865869094851471759 44578016798803642277207639)
            ·
              refine ⟨66867025198205463415811459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44578016798803642277207639 66867025198205463415811459)
              ·
                refine ⟨100300537797308195123717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66867025198205463415811459 100300537797308195123717189)
                ·
                  refine ⟨18806350836995286585696973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100300537797308195123717189 18806350836995286585696973)
                  ·
                    refine ⟨7052381563873232469636365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18806350836995286585696973 7052381563873232469636365)
                    ·
                      refine ⟨2644643086452462176113637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7052381563873232469636365 2644643086452462176113637)
                      ·
                        rfl

theorem cell23_5150424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5150424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150424 prefixEnd_5150424 := by exact prefixLift 5150424
  have htrace : WordTrace (prefixWord ++ tailWord_5150424) baseStart_5150424 baseEnd_5150424 := by
    simpa [prefixWord, tailWord_5150424, baseEnd_5150424] using wordTrace_append hprefix tailTrace_5150424
  have hstable : (prefixWord ++ tailWord_5150424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150424).length < 2 ^ (prefixWord ++ tailWord_5150424).sum := by decide
  have hdescent : baseEnd_5150424 < baseStart_5150424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150425 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 2, 2, 2]
def baseStart_5150425 : Nat := 118140960795 + 5150425 * 2 ^ 59
def prefixEnd_5150425 : Nat := 4983230072969 + 3 ^ 40 * 5150425 * 2
def baseEnd_5150425 : Nat := 2644643599933116672201133

theorem tailTrace_5150425 : CollatzResearch.WordTrace tailWord_5150425 prefixEnd_5150425 2644643599933116672201133 := by
  unfold tailWord_5150425
  simp only [CollatzResearch.WordTrace]
  refine ⟨187851432365897322404780729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125234288243931548269853819 187851432365897322404780729)
  ·
    refine ⟨140888574274422991803585547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187851432365897322404780729 140888574274422991803585547)
    ·
      refine ⟨211332861411634487705378321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140888574274422991803585547 211332861411634487705378321)
      ·
        refine ⟨158499646058725865779033741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211332861411634487705378321 158499646058725865779033741)
        ·
          refine ⟨59437367272022199667137653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158499646058725865779033741 59437367272022199667137653)
          ·
            refine ⟨5572253181752081218794155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59437367272022199667137653 5572253181752081218794155)
            ·
              refine ⟨8358379772628121828191233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572253181752081218794155 8358379772628121828191233)
              ·
                refine ⟨6268784829471091371143425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8358379772628121828191233 6268784829471091371143425)
                ·
                  refine ⟨4701588622103318528357569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6268784829471091371143425 4701588622103318528357569)
                  ·
                    refine ⟨3526191466577488896268177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4701588622103318528357569 3526191466577488896268177)
                    ·
                      refine ⟨2644643599933116672201133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526191466577488896268177 2644643599933116672201133)
                      ·
                        rfl

theorem cell23_5150425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_5150425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150425 prefixEnd_5150425 := by exact prefixLift 5150425
  have htrace : WordTrace (prefixWord ++ tailWord_5150425) baseStart_5150425 baseEnd_5150425 := by
    simpa [prefixWord, tailWord_5150425, baseEnd_5150425] using wordTrace_append hprefix tailTrace_5150425
  have hstable : (prefixWord ++ tailWord_5150425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150425).length < 2 ^ (prefixWord ++ tailWord_5150425).sum := by decide
  have hdescent : baseEnd_5150425 < baseStart_5150425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 4]
def baseStart_5150571 : Nat := 118140960795 + 5150571 * 2 ^ 59
def prefixEnd_5150571 : Nat := 4983230072969 + 3 ^ 40 * 5150571 * 2
def baseEnd_5150571 : Nat := 2644718568108673100975461

theorem tailTrace_5150571 : CollatzResearch.WordTrace tailWord_5150571 prefixEnd_5150571 2644718568108673100975461 := by
  unfold tailWord_5150571
  simp only [CollatzResearch.WordTrace]
  refine ⟨187856757423368389339595567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125237838282245592893063711 187856757423368389339595567)
  ·
    refine ⟨281785136135052584009393351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187856757423368389339595567 281785136135052584009393351)
    ·
      refine ⟨422677704202578876014090027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281785136135052584009393351 422677704202578876014090027)
      ·
        refine ⟨634016556303868314021135041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422677704202578876014090027 634016556303868314021135041)
        ·
          refine ⟨475512417227901235515851281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634016556303868314021135041 475512417227901235515851281)
          ·
            refine ⟨356634312920925926636888461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475512417227901235515851281 356634312920925926636888461)
            ·
              refine ⟨133737867345347222488833173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356634312920925926636888461 133737867345347222488833173)
              ·
                refine ⟨6268962531813151054164055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 133737867345347222488833173 6268962531813151054164055)
                ·
                  refine ⟨9403443797719726581246083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268962531813151054164055 9403443797719726581246083)
                  ·
                    refine ⟨14105165696579589871869125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9403443797719726581246083 14105165696579589871869125)
                    ·
                      refine ⟨2644718568108673100975461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14105165696579589871869125 2644718568108673100975461)
                      ·
                        rfl

theorem cell23_5150571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 4].length) (baseStart_5150571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150571 prefixEnd_5150571 := by exact prefixLift 5150571
  have htrace : WordTrace (prefixWord ++ tailWord_5150571) baseStart_5150571 baseEnd_5150571 := by
    simpa [prefixWord, tailWord_5150571, baseEnd_5150571] using wordTrace_append hprefix tailTrace_5150571
  have hstable : (prefixWord ++ tailWord_5150571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150571).length < 2 ^ (prefixWord ++ tailWord_5150571).sum := by decide
  have hdescent : baseEnd_5150571 < baseStart_5150571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150581 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5150581 : Nat := 118140960795 + 5150581 * 2 ^ 59
def prefixEnd_5150581 : Nat := 4983230072969 + 3 ^ 40 * 5150581 * 2
def baseEnd_5150581 : Nat := 881574567638406020616805

theorem tailTrace_5150581 : CollatzResearch.WordTrace tailWord_5150581 prefixEnd_5150581 881574567638406020616805 := by
  unfold tailWord_5150581
  simp only [CollatzResearch.WordTrace]
  refine ⟨187857122153332161047459597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125238081435554774031639731 187857122153332161047459597)
  ·
    refine ⟨70446420807499560392797349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187857122153332161047459597 70446420807499560392797349)
    ·
      refine ⟨13208703901406167573649503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70446420807499560392797349 13208703901406167573649503)
      ·
        refine ⟨19813055852109251360474255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13208703901406167573649503 19813055852109251360474255)
        ·
          refine ⟨29719583778163877040711383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19813055852109251360474255 29719583778163877040711383)
          ·
            refine ⟨44579375667245815561067075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29719583778163877040711383 44579375667245815561067075)
            ·
              refine ⟨66869063500868723341600613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44579375667245815561067075 66869063500868723341600613)
              ·
                refine ⟨12537949406412885626550115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66869063500868723341600613 12537949406412885626550115)
                ·
                  refine ⟨18806924109619328439825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12537949406412885626550115 18806924109619328439825173)
                  ·
                    refine ⟨881574567638406020616805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18806924109619328439825173 881574567638406020616805)
                    ·
                      rfl

theorem cell23_5150581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5150581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150581 prefixEnd_5150581 := by exact prefixLift 5150581
  have htrace : WordTrace (prefixWord ++ tailWord_5150581) baseStart_5150581 baseEnd_5150581 := by
    simpa [prefixWord, tailWord_5150581, baseEnd_5150581] using wordTrace_append hprefix tailTrace_5150581
  have hstable : (prefixWord ++ tailWord_5150581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150581).length < 2 ^ (prefixWord ++ tailWord_5150581).sum := by decide
  have hdescent : baseEnd_5150581 < baseStart_5150581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_5150584 : Nat := 118140960795 + 5150584 * 2 ^ 59
def prefixEnd_5150584 : Nat := 4983230072969 + 3 ^ 40 * 5150584 * 2
def baseEnd_5150584 : Nat := 2644725243357181550112901

theorem tailTrace_5150584 : CollatzResearch.WordTrace tailWord_5150584 prefixEnd_5150584 2644725243357181550112901 := by
  unfold tailWord_5150584
  simp only [CollatzResearch.WordTrace]
  refine ⟨93928615786160646279909403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125238154381547528373212537 93928615786160646279909403)
  ·
    refine ⟨140892923679240969419864105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93928615786160646279909403 140892923679240969419864105)
    ·
      refine ⟨105669692759430727064898079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140892923679240969419864105 105669692759430727064898079)
      ·
        refine ⟨158504539139146090597347119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105669692759430727064898079 158504539139146090597347119)
        ·
          refine ⟨237756808708719135896020679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158504539139146090597347119 237756808708719135896020679)
          ·
            refine ⟨356635213063078703844031019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237756808708719135896020679 356635213063078703844031019)
            ·
              refine ⟨534952819594618055766046529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356635213063078703844031019 534952819594618055766046529)
              ·
                refine ⟨401214614695963541824534897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534952819594618055766046529 401214614695963541824534897)
                ·
                  refine ⟨300910961021972656368401173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401214614695963541824534897 300910961021972656368401173)
                  ·
                    refine ⟨14105201297904968267268805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 300910961021972656368401173 14105201297904968267268805)
                    ·
                      refine ⟨2644725243357181550112901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14105201297904968267268805 2644725243357181550112901)
                      ·
                        rfl

theorem cell23_5150584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_5150584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150584 prefixEnd_5150584 := by exact prefixLift 5150584
  have htrace : WordTrace (prefixWord ++ tailWord_5150584) baseStart_5150584 baseEnd_5150584 := by
    simpa [prefixWord, tailWord_5150584, baseEnd_5150584] using wordTrace_append hprefix tailTrace_5150584
  have hstable : (prefixWord ++ tailWord_5150584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150584).length < 2 ^ (prefixWord ++ tailWord_5150584).sum := by decide
  have hdescent : baseEnd_5150584 < baseStart_5150584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5150604 : Nat := 118140960795 + 5150604 * 2 ^ 59
def prefixEnd_5150604 : Nat := 4983230072969 + 3 ^ 40 * 5150604 * 2
def baseEnd_5150604 : Nat := 2644735512970271471862809

theorem tailTrace_5150604 : CollatzResearch.WordTrace tailWord_5150604 prefixEnd_5150604 2644735512970271471862809 := by
  unfold tailWord_5150604
  simp only [CollatzResearch.WordTrace]
  refine ⟨93928980516124417987773433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125238640688165890650364577 93928980516124417987773433)
  ·
    refine ⟨70446735387093313490830075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93928980516124417987773433 70446735387093313490830075)
    ·
      refine ⟨105670103080639970236245113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70446735387093313490830075 105670103080639970236245113)
      ·
        refine ⟨79252577310479977677183835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105670103080639970236245113 79252577310479977677183835)
        ·
          refine ⟨118878865965719966515775753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79252577310479977677183835 118878865965719966515775753)
          ·
            refine ⟨89159149474289974886831815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118878865965719966515775753 89159149474289974886831815)
            ·
              refine ⟨133738724211434962330247723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89159149474289974886831815 133738724211434962330247723)
              ·
                refine ⟨200608086317152443495371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133738724211434962330247723 200608086317152443495371585)
                ·
                  refine ⟨150456064737864332621528689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200608086317152443495371585 150456064737864332621528689)
                  ·
                    refine ⟨112842048553398249466146517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150456064737864332621528689 112842048553398249466146517)
                    ·
                      refine ⟨2644735512970271471862809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112842048553398249466146517 2644735512970271471862809)
                      ·
                        rfl

theorem cell23_5150604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5150604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150604 prefixEnd_5150604 := by exact prefixLift 5150604
  have htrace : WordTrace (prefixWord ++ tailWord_5150604) baseStart_5150604 baseEnd_5150604 := by
    simpa [prefixWord, tailWord_5150604, baseEnd_5150604] using wordTrace_append hprefix tailTrace_5150604
  have hstable : (prefixWord ++ tailWord_5150604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150604).length < 2 ^ (prefixWord ++ tailWord_5150604).sum := by decide
  have hdescent : baseEnd_5150604 < baseStart_5150604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150615 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 2, 4]
def baseStart_5150615 : Nat := 118140960795 + 5150615 * 2 ^ 59
def prefixEnd_5150615 : Nat := 4983230072969 + 3 ^ 40 * 5150615 * 2
def baseEnd_5150615 : Nat := 881580387085823642941753

theorem tailTrace_5150615 : CollatzResearch.WordTrace tailWord_5150615 prefixEnd_5150615 881580387085823642941753 := by
  unfold tailWord_5150615
  simp only [CollatzResearch.WordTrace]
  refine ⟨187858362235208984854197299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125238908156805989902798199 187858362235208984854197299)
  ·
    refine ⟨281787543352813477281295949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187858362235208984854197299 281787543352813477281295949)
    ·
      refine ⟨105670328757305053980485981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281787543352813477281295949 105670328757305053980485981)
      ·
        refine ⟨39626373283989395242682243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105670328757305053980485981 39626373283989395242682243)
        ·
          refine ⟨59439559925984092864023365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39626373283989395242682243 59439559925984092864023365)
          ·
            refine ⟨11144917486122017412004381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59439559925984092864023365 11144917486122017412004381)
            ·
              refine ⟨4179344057295756529501643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11144917486122017412004381 4179344057295756529501643)
              ·
                refine ⟨6269016085943634794252465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179344057295756529501643 6269016085943634794252465)
                ·
                  refine ⟨4701762064457726095689349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6269016085943634794252465 4701762064457726095689349)
                  ·
                    refine ⟨881580387085823642941753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701762064457726095689349 881580387085823642941753)
                    ·
                      rfl

theorem cell23_5150615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_5150615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150615 prefixEnd_5150615 := by exact prefixLift 5150615
  have htrace : WordTrace (prefixWord ++ tailWord_5150615) baseStart_5150615 baseEnd_5150615 := by
    simpa [prefixWord, tailWord_5150615, baseEnd_5150615] using wordTrace_append hprefix tailTrace_5150615
  have hstable : (prefixWord ++ tailWord_5150615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150615).length < 2 ^ (prefixWord ++ tailWord_5150615).sum := by decide
  have hdescent : baseEnd_5150615 < baseStart_5150615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150618 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5150618 : Nat := 118140960795 + 5150618 * 2 ^ 59
def prefixEnd_5150618 : Nat := 4983230072969 + 3 ^ 40 * 5150618 * 2
def baseEnd_5150618 : Nat := 2644742701699434417087745

theorem tailTrace_5150618 : CollatzResearch.WordTrace tailWord_5150618 prefixEnd_5150618 2644742701699434417087745 := by
  unfold tailWord_5150618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46964617913549529091639127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125238981102798744244371005 46964617913549529091639127)
  ·
    refine ⟨70446926870324293637458691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46964617913549529091639127 70446926870324293637458691)
    ·
      refine ⟨105670390305486440456188037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70446926870324293637458691 105670390305486440456188037)
      ·
        refine ⟨19813198182278707585535257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105670390305486440456188037 19813198182278707585535257)
        ·
          refine ⟨14859898636709030689151443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19813198182278707585535257 14859898636709030689151443)
          ·
            refine ⟨22289847955063546033727165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14859898636709030689151443 22289847955063546033727165)
            ·
              refine ⟨8358692983148829762647687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22289847955063546033727165 8358692983148829762647687)
              ·
                refine ⟨12538039474723244643971531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358692983148829762647687 12538039474723244643971531)
                ·
                  refine ⟨18807059212084866965957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12538039474723244643971531 18807059212084866965957297)
                  ·
                    refine ⟨14105294409063650224467973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18807059212084866965957297 14105294409063650224467973)
                    ·
                      refine ⟨2644742701699434417087745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14105294409063650224467973 2644742701699434417087745)
                      ·
                        rfl

theorem cell23_5150618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5150618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150618 prefixEnd_5150618 := by exact prefixLift 5150618
  have htrace : WordTrace (prefixWord ++ tailWord_5150618) baseStart_5150618 baseEnd_5150618 := by
    simpa [prefixWord, tailWord_5150618, baseEnd_5150618] using wordTrace_append hprefix tailTrace_5150618
  have hstable : (prefixWord ++ tailWord_5150618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150618).length < 2 ^ (prefixWord ++ tailWord_5150618).sum := by decide
  have hdescent : baseEnd_5150618 < baseStart_5150618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150628 : List Nat := [2, 3, 1, 2, 1, 5, 2, 7]
def baseStart_5150628 : Nat := 118140960795 + 5150628 * 2 ^ 59
def prefixEnd_5150628 : Nat := 4983230072969 + 3 ^ 40 * 5150628 * 2
def baseEnd_5150628 : Nat := 97953623574295532517137

theorem tailTrace_5150628 : CollatzResearch.WordTrace tailWord_5150628 prefixEnd_5150628 97953623574295532517137 := by
  unfold tailWord_5150628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93929418192080944037210269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125239224256107925382947025 93929418192080944037210269)
  ·
    refine ⟨35223531822030354013953851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93929418192080944037210269 35223531822030354013953851)
    ·
      refine ⟨52835297733045531020930777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35223531822030354013953851 52835297733045531020930777)
      ·
        refine ⟨39626473299784148265698083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52835297733045531020930777 39626473299784148265698083)
        ·
          refine ⟨59439709949676222398547125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39626473299784148265698083 59439709949676222398547125)
          ·
            refine ⟨5572472807782145849863793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59439709949676222398547125 5572472807782145849863793)
            ·
              refine ⟨4179354605836609387397845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572472807782145849863793 4179354605836609387397845)
              ·
                refine ⟨97953623574295532517137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4179354605836609387397845 97953623574295532517137)
                ·
                  rfl

theorem cell23_5150628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 7].length) (baseStart_5150628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150628 prefixEnd_5150628 := by exact prefixLift 5150628
  have htrace : WordTrace (prefixWord ++ tailWord_5150628) baseStart_5150628 baseEnd_5150628 := by
    simpa [prefixWord, tailWord_5150628, baseEnd_5150628] using wordTrace_append hprefix tailTrace_5150628
  have hstable : (prefixWord ++ tailWord_5150628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150628).length < 2 ^ (prefixWord ++ tailWord_5150628).sum := by decide
  have hdescent : baseEnd_5150628 < baseStart_5150628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150711 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_5150711 : Nat := 118140960795 + 5150711 * 2 ^ 59
def prefixEnd_5150711 : Nat := 4983230072969 + 3 ^ 40 * 5150711 * 2
def baseEnd_5150711 : Nat := 2644790455400302553224817

theorem tailTrace_5150711 : CollatzResearch.WordTrace tailWord_5150711 prefixEnd_5150711 2644790455400302553224817 := by
  unfold tailWord_5150711
  simp only [CollatzResearch.WordTrace]
  refine ⟨187861863642861193249691987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125241242428574128833127991 187861863642861193249691987)
  ·
    refine ⟨281792795464291789874537981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187861863642861193249691987 281792795464291789874537981)
    ·
      refine ⟨105672298299109421202951743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281792795464291789874537981 105672298299109421202951743)
      ·
        refine ⟨158508447448664131804427615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105672298299109421202951743 158508447448664131804427615)
        ·
          refine ⟨237762671172996197706641423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158508447448664131804427615 237762671172996197706641423)
          ·
            refine ⟨356644006759494296559962135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237762671172996197706641423 356644006759494296559962135)
            ·
              refine ⟨534966010139241444839943203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356644006759494296559962135 534966010139241444839943203)
              ·
                refine ⟨802449015208862167259914805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534966010139241444839943203 802449015208862167259914805)
                ·
                  refine ⟨75229595175830828180617013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802449015208862167259914805 75229595175830828180617013)
                  ·
                    refine ⟨7052774547734140141932845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75229595175830828180617013 7052774547734140141932845)
                    ·
                      refine ⟨2644790455400302553224817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7052774547734140141932845 2644790455400302553224817)
                      ·
                        rfl

theorem cell23_5150711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_5150711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150711 prefixEnd_5150711 := by exact prefixLift 5150711
  have htrace : WordTrace (prefixWord ++ tailWord_5150711) baseStart_5150711 baseEnd_5150711 := by
    simpa [prefixWord, tailWord_5150711, baseEnd_5150711] using wordTrace_append hprefix tailTrace_5150711
  have hstable : (prefixWord ++ tailWord_5150711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150711).length < 2 ^ (prefixWord ++ tailWord_5150711).sum := by decide
  have hdescent : baseEnd_5150711 < baseStart_5150711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150728 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_5150728 : Nat := 118140960795 + 5150728 * 2 ^ 59
def prefixEnd_5150728 : Nat := 4983230072969 + 3 ^ 40 * 5150728 * 2
def baseEnd_5150728 : Nat := 2644799184571428986712239

theorem tailTrace_5150728 : CollatzResearch.WordTrace tailWord_5150728 prefixEnd_5150728 2644799184571428986712239 := by
  unfold tailWord_5150728
  simp only [CollatzResearch.WordTrace]
  refine ⟨93931241841899802576530419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125241655789199736768707225 93931241841899802576530419)
  ·
    refine ⟨140896862762849703864795629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93931241841899802576530419 140896862762849703864795629)
    ·
      refine ⟨52836323536068638949298361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140896862762849703864795629 52836323536068638949298361)
      ·
        refine ⟨39627242652051479211973771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52836323536068638949298361 39627242652051479211973771)
        ·
          refine ⟨59440863978077218817960657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39627242652051479211973771 59440863978077218817960657)
          ·
            refine ⟨44580647983557914113470493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59440863978077218817960657 44580647983557914113470493)
            ·
              refine ⟨16717742993834217792551435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44580647983557914113470493 16717742993834217792551435)
              ·
                refine ⟨25076614490751326688827153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16717742993834217792551435 25076614490751326688827153)
                ·
                  refine ⟨18807460868063495016620365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25076614490751326688827153 18807460868063495016620365)
                  ·
                    refine ⟨7052797825523810631232637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18807460868063495016620365 7052797825523810631232637)
                    ·
                      refine ⟨2644799184571428986712239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7052797825523810631232637 2644799184571428986712239)
                      ·
                        rfl

theorem cell23_5150728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_5150728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150728 prefixEnd_5150728 := by exact prefixLift 5150728
  have htrace : WordTrace (prefixWord ++ tailWord_5150728) baseStart_5150728 baseEnd_5150728 := by
    simpa [prefixWord, tailWord_5150728, baseEnd_5150728] using wordTrace_append hprefix tailTrace_5150728
  have hstable : (prefixWord ++ tailWord_5150728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150728).length < 2 ^ (prefixWord ++ tailWord_5150728).sum := by decide
  have hdescent : baseEnd_5150728 < baseStart_5150728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150731 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 7]
def baseStart_5150731 : Nat := 118140960795 + 5150731 * 2 ^ 59
def prefixEnd_5150731 : Nat := 4983230072969 + 3 ^ 40 * 5150731 * 2
def baseEnd_5150731 : Nat := 881600241671130824991575

theorem tailTrace_5150731 : CollatzResearch.WordTrace tailWord_5150731 prefixEnd_5150731 881600241671130824991575 := by
  unfold tailWord_5150731
  simp only [CollatzResearch.WordTrace]
  refine ⟨187862593102788736665420047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125241728735192491110280031 187862593102788736665420047)
  ·
    refine ⟨281793889654183104998130071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187862593102788736665420047 281793889654183104998130071)
    ·
      refine ⟨422690834481274657497195107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281793889654183104998130071 422690834481274657497195107)
      ·
        refine ⟨634036251721911986245792661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422690834481274657497195107 634036251721911986245792661)
        ·
          refine ⟨29720449299464624355271531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 634036251721911986245792661 29720449299464624355271531)
          ·
            refine ⟨44580673949196936532907297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29720449299464624355271531 44580673949196936532907297)
            ·
              refine ⟨33435505461897702399680473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44580673949196936532907297 33435505461897702399680473)
              ·
                refine ⟨25076629096423276799760355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33435505461897702399680473 25076629096423276799760355)
                ·
                  refine ⟨37614943644634915199640533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25076629096423276799760355 37614943644634915199640533)
                  ·
                    refine ⟨881600241671130824991575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37614943644634915199640533 881600241671130824991575)
                    ·
                      rfl

theorem cell23_5150731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_5150731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150731 prefixEnd_5150731 := by exact prefixLift 5150731
  have htrace : WordTrace (prefixWord ++ tailWord_5150731) baseStart_5150731 baseEnd_5150731 := by
    simpa [prefixWord, tailWord_5150731, baseEnd_5150731] using wordTrace_append hprefix tailTrace_5150731
  have hstable : (prefixWord ++ tailWord_5150731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150731).length < 2 ^ (prefixWord ++ tailWord_5150731).sum := by decide
  have hdescent : baseEnd_5150731 < baseStart_5150731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150748 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5150748 : Nat := 118140960795 + 5150748 * 2 ^ 59
def prefixEnd_5150748 : Nat := 4983230072969 + 3 ^ 40 * 5150748 * 2
def baseEnd_5150748 : Nat := 881603151394839636154049

theorem tailTrace_5150748 : CollatzResearch.WordTrace tailWord_5150748 prefixEnd_5150748 881603151394839636154049 := by
  unfold tailWord_5150748
  simp only [CollatzResearch.WordTrace]
  refine ⟨93931606571863574284394449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125242142095818099045859265 93931606571863574284394449)
  ·
    refine ⟨70448704928897680713295837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93931606571863574284394449 70448704928897680713295837)
    ·
      refine ⟨26418264348336630267485939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70448704928897680713295837 26418264348336630267485939)
      ·
        refine ⟨39627396522504945401228909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26418264348336630267485939 39627396522504945401228909)
        ·
          refine ⟨14860273695939354525460841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39627396522504945401228909 14860273695939354525460841)
          ·
            refine ⟨11145205271954515894095631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14860273695939354525460841 11145205271954515894095631)
            ·
              refine ⟨16717807907931773841143447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145205271954515894095631 16717807907931773841143447)
              ·
                refine ⟨25076711861897660761715171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16717807907931773841143447 25076711861897660761715171)
                ·
                  refine ⟨37615067792846491142572757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25076711861897660761715171 37615067792846491142572757)
                  ·
                    refine ⟨881603151394839636154049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37615067792846491142572757 881603151394839636154049)
                    ·
                      rfl

theorem cell23_5150748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5150748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150748 prefixEnd_5150748 := by exact prefixLift 5150748
  have htrace : WordTrace (prefixWord ++ tailWord_5150748) baseStart_5150748 baseEnd_5150748 := by
    simpa [prefixWord, tailWord_5150748, baseEnd_5150748] using wordTrace_append hprefix tailTrace_5150748
  have hstable : (prefixWord ++ tailWord_5150748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150748).length < 2 ^ (prefixWord ++ tailWord_5150748).sum := by decide
  have hdescent : baseEnd_5150748 < baseStart_5150748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150771 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_5150771 : Nat := 118140960795 + 5150771 * 2 ^ 59
def prefixEnd_5150771 : Nat := 4983230072969 + 3 ^ 40 * 5150771 * 2
def baseEnd_5150771 : Nat := 2644821264239572318474541

theorem tailTrace_5150771 : CollatzResearch.WordTrace tailWord_5150771 prefixEnd_5150771 2644821264239572318474541 := by
  unfold tailWord_5150771
  simp only [CollatzResearch.WordTrace]
  refine ⟨187864052022643823496876167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125242701348429215664584111 187864052022643823496876167)
  ·
    refine ⟨281796078033965735245314251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187864052022643823496876167 281796078033965735245314251)
    ·
      refine ⟨422694117050948602867971377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281796078033965735245314251 422694117050948602867971377)
      ·
        refine ⟨317020587788211452150978533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422694117050948602867971377 317020587788211452150978533)
        ·
          refine ⟨59441360210289647278308475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317020587788211452150978533 59441360210289647278308475)
          ·
            refine ⟨89162040315434470917462713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59441360210289647278308475 89162040315434470917462713)
            ·
              refine ⟨66871530236575853188097035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89162040315434470917462713 66871530236575853188097035)
              ·
                refine ⟨100307295354863779782145553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66871530236575853188097035 100307295354863779782145553)
                ·
                  refine ⟨75230471516147834836609165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100307295354863779782145553 75230471516147834836609165)
                  ·
                    refine ⟨28211426818555438063728437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75230471516147834836609165 28211426818555438063728437)
                    ·
                      refine ⟨2644821264239572318474541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28211426818555438063728437 2644821264239572318474541)
                      ·
                        rfl

theorem cell23_5150771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_5150771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150771 prefixEnd_5150771 := by exact prefixLift 5150771
  have htrace : WordTrace (prefixWord ++ tailWord_5150771) baseStart_5150771 baseEnd_5150771 := by
    simpa [prefixWord, tailWord_5150771, baseEnd_5150771] using wordTrace_append hprefix tailTrace_5150771
  have hstable : (prefixWord ++ tailWord_5150771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150771).length < 2 ^ (prefixWord ++ tailWord_5150771).sum := by decide
  have hdescent : baseEnd_5150771 < baseStart_5150771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150829 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_5150829 : Nat := 118140960795 + 5150829 * 2 ^ 59
def prefixEnd_5150829 : Nat := 4983230072969 + 3 ^ 40 * 5150829 * 2
def baseEnd_5150829 : Nat := 881617015372511030516425

theorem tailTrace_5150829 : CollatzResearch.WordTrace tailWord_5150829 prefixEnd_5150829 881617015372511030516425 := by
  unfold tailWord_5150829
  simp only [CollatzResearch.WordTrace]
  refine ⟨187866167456433699402487541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125244111637622466268325027 187866167456433699402487541)
  ·
    refine ⟨17612453199040659318983207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187866167456433699402487541 17612453199040659318983207)
    ·
      refine ⟨26418679798560988978474811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17612453199040659318983207 26418679798560988978474811)
      ·
        refine ⟨39628019697841483467712217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26418679798560988978474811 39628019697841483467712217)
        ·
          refine ⟨29721014773381112600784163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39628019697841483467712217 29721014773381112600784163)
          ·
            refine ⟨44581522160071668901176245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29721014773381112600784163 44581522160071668901176245)
            ·
              refine ⟨4179517702506718959485273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44581522160071668901176245 4179517702506718959485273)
              ·
                refine ⟨3134638276880039219613955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179517702506718959485273 3134638276880039219613955)
                ·
                  refine ⟨4701957415320058829420933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134638276880039219613955 4701957415320058829420933)
                  ·
                    refine ⟨881617015372511030516425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701957415320058829420933 881617015372511030516425)
                    ·
                      rfl

theorem cell23_5150829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_5150829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150829 prefixEnd_5150829 := by exact prefixLift 5150829
  have htrace : WordTrace (prefixWord ++ tailWord_5150829) baseStart_5150829 baseEnd_5150829 := by
    simpa [prefixWord, tailWord_5150829, baseEnd_5150829] using wordTrace_append hprefix tailTrace_5150829
  have hstable : (prefixWord ++ tailWord_5150829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150829).length < 2 ^ (prefixWord ++ tailWord_5150829).sum := by decide
  have hdescent : baseEnd_5150829 < baseStart_5150829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150855 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 1, 5]
def baseStart_5150855 : Nat := 118140960795 + 5150855 * 2 ^ 59
def prefixEnd_5150855 : Nat := 4983230072969 + 3 ^ 40 * 5150855 * 2
def baseEnd_5150855 : Nat := 881621465538183329941385

theorem tailTrace_5150855 : CollatzResearch.WordTrace tailWord_5150855 prefixEnd_5150855 881621465538183329941385 := by
  unfold tailWord_5150855
  simp only [CollatzResearch.WordTrace]
  refine ⟨187867115754339505842934019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125244743836226337228622679 187867115754339505842934019)
  ·
    refine ⟨281800673631509258764401029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187867115754339505842934019 281800673631509258764401029)
    ·
      refine ⟨52837626305907986018325193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281800673631509258764401029 52837626305907986018325193)
      ·
        refine ⟨39628219729430989513743895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52837626305907986018325193 39628219729430989513743895)
        ·
          refine ⟨59442329594146484270615843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39628219729430989513743895 59442329594146484270615843)
          ·
            refine ⟨89163494391219726405923765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59442329594146484270615843 89163494391219726405923765)
            ·
              refine ⟨8359077599176849350555353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89163494391219726405923765 8359077599176849350555353)
              ·
                refine ⟨6269308199382637012916515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8359077599176849350555353 6269308199382637012916515)
                ·
                  refine ⟨9403962299073955519374773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269308199382637012916515 9403962299073955519374773)
                  ·
                    refine ⟨881621465538183329941385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9403962299073955519374773 881621465538183329941385)
                    ·
                      rfl

theorem cell23_5150855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_5150855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150855 prefixEnd_5150855 := by exact prefixLift 5150855
  have htrace : WordTrace (prefixWord ++ tailWord_5150855) baseStart_5150855 baseEnd_5150855 := by
    simpa [prefixWord, tailWord_5150855, baseEnd_5150855] using wordTrace_append hprefix tailTrace_5150855
  have hstable : (prefixWord ++ tailWord_5150855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150855).length < 2 ^ (prefixWord ++ tailWord_5150855).sum := by decide
  have hdescent : baseEnd_5150855 < baseStart_5150855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150905 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5150905 : Nat := 118140960795 + 5150905 * 2 ^ 59
def prefixEnd_5150905 : Nat := 4983230072969 + 3 ^ 40 * 5150905 * 2
def baseEnd_5150905 : Nat := 2644890070647274794198925

theorem tailTrace_5150905 : CollatzResearch.WordTrace tailWord_5150905 prefixEnd_5150905 2644890070647274794198925 := by
  unfold tailWord_5150905
  simp only [CollatzResearch.WordTrace]
  refine ⟨187868939404158364382254169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125245959602772242921502779 187868939404158364382254169)
  ·
    refine ⟨140901704553118773286690627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187868939404158364382254169 140901704553118773286690627)
    ·
      refine ⟨211352556829678159930035941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140901704553118773286690627 211352556829678159930035941)
      ·
        refine ⟨39628604405564654986881739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211352556829678159930035941 39628604405564654986881739)
        ·
          refine ⟨59442906608346982480322609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39628604405564654986881739 59442906608346982480322609)
          ·
            refine ⟨44582179956260236860241957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59442906608346982480322609 44582179956260236860241957)
            ·
              refine ⟨8359158741798794411295367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44582179956260236860241957 8359158741798794411295367)
              ·
                refine ⟨12538738112698191616943051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359158741798794411295367 12538738112698191616943051)
                ·
                  refine ⟨18808107169047287425414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12538738112698191616943051 18808107169047287425414577)
                  ·
                    refine ⟨14106080376785465569060933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18808107169047287425414577 14106080376785465569060933)
                    ·
                      refine ⟨2644890070647274794198925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14106080376785465569060933 2644890070647274794198925)
                      ·
                        rfl

theorem cell23_5150905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5150905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150905 prefixEnd_5150905 := by exact prefixLift 5150905
  have htrace : WordTrace (prefixWord ++ tailWord_5150905) baseStart_5150905 baseEnd_5150905 := by
    simpa [prefixWord, tailWord_5150905, baseEnd_5150905] using wordTrace_append hprefix tailTrace_5150905
  have hstable : (prefixWord ++ tailWord_5150905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150905).length < 2 ^ (prefixWord ++ tailWord_5150905).sum := by decide
  have hdescent : baseEnd_5150905 < baseStart_5150905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150913 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5150913 : Nat := 118140960795 + 5150913 * 2 ^ 59
def prefixEnd_5150913 : Nat := 4983230072969 + 3 ^ 40 * 5150913 * 2
def baseEnd_5150913 : Nat := 2644894178492510762898889

theorem tailTrace_5150913 : CollatzResearch.WordTrace tailWord_5150913 prefixEnd_5150913 2644894178492510762898889 := by
  unfold tailWord_5150913
  simp only [CollatzResearch.WordTrace]
  refine ⟨187869231188129381748545393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125246154125419587832363595 187869231188129381748545393)
  ·
    refine ⟨140901923391097036311409045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187869231188129381748545393 140901923391097036311409045)
    ·
      refine ⟨6604777658957673577097299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140901923391097036311409045 6604777658957673577097299)
      ·
        refine ⟨9907166488436510365645949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604777658957673577097299 9907166488436510365645949)
        ·
          refine ⟨3715187433163691387117231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9907166488436510365645949 3715187433163691387117231)
          ·
            refine ⟨5572781149745537080675847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715187433163691387117231 5572781149745537080675847)
            ·
              refine ⟨8359171724618305621013771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572781149745537080675847 8359171724618305621013771)
              ·
                refine ⟨12538757586927458431520657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359171724618305621013771 12538757586927458431520657)
                ·
                  refine ⟨9404068190195593823640493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12538757586927458431520657 9404068190195593823640493)
                  ·
                    refine ⟨3526525571323347683865185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9404068190195593823640493 3526525571323347683865185)
                    ·
                      refine ⟨2644894178492510762898889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526525571323347683865185 2644894178492510762898889)
                      ·
                        rfl

theorem cell23_5150913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5150913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150913 prefixEnd_5150913 := by exact prefixLift 5150913
  have htrace : WordTrace (prefixWord ++ tailWord_5150913) baseStart_5150913 baseEnd_5150913 := by
    simpa [prefixWord, tailWord_5150913, baseEnd_5150913] using wordTrace_append hprefix tailTrace_5150913
  have hstable : (prefixWord ++ tailWord_5150913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150913).length < 2 ^ (prefixWord ++ tailWord_5150913).sum := by decide
  have hdescent : baseEnd_5150913 < baseStart_5150913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150926 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_5150926 : Nat := 118140960795 + 5150926 * 2 ^ 59
def prefixEnd_5150926 : Nat := 4983230072969 + 3 ^ 40 * 5150926 * 2
def baseEnd_5150926 : Nat := 2644900853741019212036329

theorem tailTrace_5150926 : CollatzResearch.WordTrace tailWord_5150926 prefixEnd_5150926 2644900853741019212036329 := by
  unfold tailWord_5150926
  simp only [CollatzResearch.WordTrace]
  refine ⟨23483713167135285621096079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125246470224721523312512421 23483713167135285621096079)
  ·
    refine ⟨35225569750702928431644119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23483713167135285621096079 35225569750702928431644119)
    ·
      refine ⟨52838354626054392647466179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35225569750702928431644119 52838354626054392647466179)
      ·
        refine ⟨79257531939081588971199269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52838354626054392647466179 79257531939081588971199269)
        ·
          refine ⟨14860787238577797932099863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79257531939081588971199269 14860787238577797932099863)
          ·
            refine ⟨22291180857866696898149795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14860787238577797932099863 22291180857866696898149795)
            ·
              refine ⟨33436771286800045347224693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22291180857866696898149795 33436771286800045347224693)
              ·
                refine ⟨3134697308137504251302315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33436771286800045347224693 3134697308137504251302315)
                ·
                  refine ⟨4702045962206256376953473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134697308137504251302315 4702045962206256376953473)
                  ·
                    refine ⟨3526534471654692282715105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4702045962206256376953473 3526534471654692282715105)
                    ·
                      refine ⟨2644900853741019212036329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526534471654692282715105 2644900853741019212036329)
                      ·
                        rfl

theorem cell23_5150926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_5150926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150926 prefixEnd_5150926 := by exact prefixLift 5150926
  have htrace : WordTrace (prefixWord ++ tailWord_5150926) baseStart_5150926 baseEnd_5150926 := by
    simpa [prefixWord, tailWord_5150926, baseEnd_5150926] using wordTrace_append hprefix tailTrace_5150926
  have hstable : (prefixWord ++ tailWord_5150926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150926).length < 2 ^ (prefixWord ++ tailWord_5150926).sum := by decide
  have hdescent : baseEnd_5150926 < baseStart_5150926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150946 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5150946 : Nat := 118140960795 + 5150946 * 2 ^ 59
def prefixEnd_5150946 : Nat := 4983230072969 + 3 ^ 40 * 5150946 * 2
def baseEnd_5150946 : Nat := 2644911123354109133786237

theorem tailTrace_5150946 : CollatzResearch.WordTrace tailWord_5150946 prefixEnd_5150946 2644911123354109133786237 := by
  unfold tailWord_5150946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46967608699252457096124173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125246956531339885589664461 46967608699252457096124173)
  ·
    refine ⟨17612853262219671411046565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46967608699252457096124173 17612853262219671411046565)
    ·
      refine ⟨3302409986666188389571231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17612853262219671411046565 3302409986666188389571231)
      ·
        refine ⟨4953614979999282584356847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302409986666188389571231 4953614979999282584356847)
        ·
          refine ⟨7430422469998923876535271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953614979999282584356847 7430422469998923876535271)
          ·
            refine ⟨11145633704998385814802907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7430422469998923876535271 11145633704998385814802907)
            ·
              refine ⟨16718450557497578722204361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145633704998385814802907 16718450557497578722204361)
              ·
                refine ⟨12538837918123184041653271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16718450557497578722204361 12538837918123184041653271)
                ·
                  refine ⟨18808256877184776062479907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12538837918123184041653271 18808256877184776062479907)
                  ·
                    refine ⟨28212385315777164093719861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18808256877184776062479907 28212385315777164093719861)
                    ·
                      refine ⟨2644911123354109133786237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28212385315777164093719861 2644911123354109133786237)
                      ·
                        rfl

theorem cell23_5150946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5150946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150946 prefixEnd_5150946 := by exact prefixLift 5150946
  have htrace : WordTrace (prefixWord ++ tailWord_5150946) baseStart_5150946 baseEnd_5150946 := by
    simpa [prefixWord, tailWord_5150946, baseEnd_5150946] using wordTrace_append hprefix tailTrace_5150946
  have hstable : (prefixWord ++ tailWord_5150946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150946).length < 2 ^ (prefixWord ++ tailWord_5150946).sum := by decide
  have hdescent : baseEnd_5150946 < baseStart_5150946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150968 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_5150968 : Nat := 118140960795 + 5150968 * 2 ^ 59
def prefixEnd_5150968 : Nat := 4983230072969 + 3 ^ 40 * 5150968 * 2
def baseEnd_5150968 : Nat := 2644922419928508047711135

theorem tailTrace_5150968 : CollatzResearch.WordTrace tailWord_5150968 prefixEnd_5150968 2644922419928508047711135 := by
  unfold tailWord_5150968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93935618601465063070898779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125247491468620084094531705 93935618601465063070898779)
  ·
    refine ⟨140903427902197594606348169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93935618601465063070898779 140903427902197594606348169)
    ·
      refine ⟨105677570926648195954761127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140903427902197594606348169 105677570926648195954761127)
      ·
        refine ⟨158516356389972293932141691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105677570926648195954761127 158516356389972293932141691)
        ·
          refine ⟨237774534584958440898212537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158516356389972293932141691 237774534584958440898212537)
          ·
            refine ⟨178330900938718830673659403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237774534584958440898212537 178330900938718830673659403)
            ·
              refine ⟨267496351408078246010489105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178330900938718830673659403 267496351408078246010489105)
              ·
                refine ⟨200622263556058684507866829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267496351408078246010489105 200622263556058684507866829)
                ·
                  refine ⟨75233348833522006690450061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200622263556058684507866829 75233348833522006690450061)
                  ·
                    refine ⟨28212505812570752508918773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75233348833522006690450061 28212505812570752508918773)
                    ·
                      refine ⟨2644922419928508047711135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28212505812570752508918773 2644922419928508047711135)
                      ·
                        rfl

theorem cell23_5150968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_5150968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150968 prefixEnd_5150968 := by exact prefixLift 5150968
  have htrace : WordTrace (prefixWord ++ tailWord_5150968) baseStart_5150968 baseEnd_5150968 := by
    simpa [prefixWord, tailWord_5150968, baseEnd_5150968] using wordTrace_append hprefix tailTrace_5150968
  have hstable : (prefixWord ++ tailWord_5150968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150968).length < 2 ^ (prefixWord ++ tailWord_5150968).sum := by decide
  have hdescent : baseEnd_5150968 < baseStart_5150968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150985 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_5150985 : Nat := 118140960795 + 5150985 * 2 ^ 59
def prefixEnd_5150985 : Nat := 4983230072969 + 3 ^ 40 * 5150985 * 2
def baseEnd_5150985 : Nat := 2644931149099634481198557

theorem tailTrace_5150985 : CollatzResearch.WordTrace tailWord_5150985 prefixEnd_5150985 2644931149099634481198557 := by
  unfold tailWord_5150985
  simp only [CollatzResearch.WordTrace]
  refine ⟨187871857243868538045166409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125247904829245692030110939 187871857243868538045166409)
  ·
    refine ⟨140903892932901403533874807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187871857243868538045166409 140903892932901403533874807)
    ·
      refine ⟨211355839399352105300812211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140903892932901403533874807 211355839399352105300812211)
      ·
        refine ⟨317033759099028157951218317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211355839399352105300812211 317033759099028157951218317)
        ·
          refine ⟨118887659662135559231706869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317033759099028157951218317 118887659662135559231706869)
          ·
            refine ⟨11145718093325208677972519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118887659662135559231706869 11145718093325208677972519)
            ·
              refine ⟨16718577139987813016958779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145718093325208677972519 16718577139987813016958779)
              ·
                refine ⟨25077865709981719525438169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16718577139987813016958779 25077865709981719525438169)
                ·
                  refine ⟨18808399282486289644078627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25077865709981719525438169 18808399282486289644078627)
                  ·
                    refine ⟨28212598923729434466117941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18808399282486289644078627 28212598923729434466117941)
                    ·
                      refine ⟨2644931149099634481198557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28212598923729434466117941 2644931149099634481198557)
                      ·
                        rfl

theorem cell23_5150985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_5150985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150985 prefixEnd_5150985 := by exact prefixLift 5150985
  have htrace : WordTrace (prefixWord ++ tailWord_5150985) baseStart_5150985 baseEnd_5150985 := by
    simpa [prefixWord, tailWord_5150985, baseEnd_5150985] using wordTrace_append hprefix tailTrace_5150985
  have hstable : (prefixWord ++ tailWord_5150985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150985).length < 2 ^ (prefixWord ++ tailWord_5150985).sum := by decide
  have hdescent : baseEnd_5150985 < baseStart_5150985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5150999 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5150999 : Nat := 118140960795 + 5150999 * 2 ^ 59
def prefixEnd_5150999 : Nat := 4983230072969 + 3 ^ 40 * 5150999 * 2
def baseEnd_5150999 : Nat := 2644938337828797426423493

theorem tailTrace_5150999 : CollatzResearch.WordTrace tailWord_5150999 prefixEnd_5150999 2644938337828797426423493 := by
  unfold tailWord_5150999
  simp only [CollatzResearch.WordTrace]
  refine ⟨187872367865817818436176051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125248245243878545624117367 187872367865817818436176051)
  ·
    refine ⟨281808551798726727654264077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187872367865817818436176051 281808551798726727654264077)
    ·
      refine ⟨105678206924522522870349029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281808551798726727654264077 105678206924522522870349029)
      ·
        refine ⟨19814663798347973038190443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105678206924522522870349029 19814663798347973038190443)
        ·
          refine ⟨29721995697521959557285665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19814663798347973038190443 29721995697521959557285665)
          ·
            refine ⟨22291496773141469667964249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29721995697521959557285665 22291496773141469667964249)
            ·
              refine ⟨16718622579856102250973187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22291496773141469667964249 16718622579856102250973187)
              ·
                refine ⟨25077933869784153376459781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16718622579856102250973187 25077933869784153376459781)
                ·
                  refine ⟨4702112600584528758086209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25077933869784153376459781 4702112600584528758086209)
                  ·
                    refine ⟨3526584450438396568564657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4702112600584528758086209 3526584450438396568564657)
                    ·
                      refine ⟨2644938337828797426423493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526584450438396568564657 2644938337828797426423493)
                      ·
                        rfl

theorem cell23_5150999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5150999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5150999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5150999 prefixEnd_5150999 := by exact prefixLift 5150999
  have htrace : WordTrace (prefixWord ++ tailWord_5150999) baseStart_5150999 baseEnd_5150999 := by
    simpa [prefixWord, tailWord_5150999, baseEnd_5150999] using wordTrace_append hprefix tailTrace_5150999
  have hstable : (prefixWord ++ tailWord_5150999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5150999).length < 2 ^ (prefixWord ++ tailWord_5150999).sum := by decide
  have hdescent : baseEnd_5150999 < baseStart_5150999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5150999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151055 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_5151055 : Nat := 118140960795 + 5151055 * 2 ^ 59
def prefixEnd_5151055 : Nat := 4983230072969 + 3 ^ 40 * 5151055 * 2
def baseEnd_5151055 : Nat := 2644967092745449207323235

theorem tailTrace_5151055 : CollatzResearch.WordTrace tailWord_5151055 prefixEnd_5151055 2644967092745449207323235 := by
  unfold tailWord_5151055
  simp only [CollatzResearch.WordTrace]
  refine ⟨187874410353614940000214619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125249606902409960000143079 187874410353614940000214619)
  ·
    refine ⟨281811615530422410000321929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187874410353614940000214619 281811615530422410000321929)
    ·
      refine ⟨211358711647816807500241447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281811615530422410000321929 211358711647816807500241447)
      ·
        refine ⟨317038067471725211250362171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211358711647816807500241447 317038067471725211250362171)
        ·
          refine ⟨475557101207587816875543257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317038067471725211250362171 475557101207587816875543257)
          ·
            refine ⟨356667825905690862656657443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475557101207587816875543257 356667825905690862656657443)
            ·
              refine ⟨535001738858536293984986165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356667825905690862656657443 535001738858536293984986165)
              ·
                refine ⟨50156413017987777561092453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535001738858536293984986165 50156413017987777561092453)
                ·
                  refine ⟨9404327440872708292704835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50156413017987777561092453 9404327440872708292704835)
                  ·
                    refine ⟨14106491161309062439057253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9404327440872708292704835 14106491161309062439057253)
                    ·
                      refine ⟨2644967092745449207323235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14106491161309062439057253 2644967092745449207323235)
                      ·
                        rfl

theorem cell23_5151055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_5151055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151055 prefixEnd_5151055 := by exact prefixLift 5151055
  have htrace : WordTrace (prefixWord ++ tailWord_5151055) baseStart_5151055 baseEnd_5151055 := by
    simpa [prefixWord, tailWord_5151055, baseEnd_5151055] using wordTrace_append hprefix tailTrace_5151055
  have hstable : (prefixWord ++ tailWord_5151055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151055).length < 2 ^ (prefixWord ++ tailWord_5151055).sum := by decide
  have hdescent : baseEnd_5151055 < baseStart_5151055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151099 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 1, 4]
def baseStart_5151099 : Nat := 118140960795 + 5151099 * 2 ^ 59
def prefixEnd_5151099 : Nat := 4983230072969 + 3 ^ 40 * 5151099 * 2
def baseEnd_5151099 : Nat := 881663228631415678391011

theorem tailTrace_5151099 : CollatzResearch.WordTrace tailWord_5151099 prefixEnd_5151099 881663228631415678391011 := by
  unfold tailWord_5151099
  simp only [CollatzResearch.WordTrace]
  refine ⟨187876015165455535514816351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125250676776970357009877567 187876015165455535514816351)
  ·
    refine ⟨281814022748183303272224527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187876015165455535514816351 281814022748183303272224527)
    ·
      refine ⟨422721034122274954908336791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281814022748183303272224527 422721034122274954908336791)
      ·
        refine ⟨634081551183412432362505187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422721034122274954908336791 634081551183412432362505187)
        ·
          refine ⟨951122326775118648543757781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634081551183412432362505187 951122326775118648543757781)
          ·
            refine ⟨22291929533791843325244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 951122326775118648543757781 22291929533791843325244323)
            ·
              refine ⟨33437894300687764987866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22291929533791843325244323 33437894300687764987866485)
              ·
                refine ⟨3134802590689477967612483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33437894300687764987866485 3134802590689477967612483)
                ·
                  refine ⟨4702203886034216951418725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134802590689477967612483 4702203886034216951418725)
                  ·
                    refine ⟨881663228631415678391011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702203886034216951418725 881663228631415678391011)
                    ·
                      rfl

theorem cell23_5151099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 4].length) (baseStart_5151099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151099 prefixEnd_5151099 := by exact prefixLift 5151099
  have htrace : WordTrace (prefixWord ++ tailWord_5151099) baseStart_5151099 baseEnd_5151099 := by
    simpa [prefixWord, tailWord_5151099, baseEnd_5151099] using wordTrace_append hprefix tailTrace_5151099
  have hstable : (prefixWord ++ tailWord_5151099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151099).length < 2 ^ (prefixWord ++ tailWord_5151099).sum := by decide
  have hdescent : baseEnd_5151099 < baseStart_5151099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151115 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_5151115 : Nat := 118140960795 + 5151115 * 2 ^ 59
def prefixEnd_5151115 : Nat := 4983230072969 + 3 ^ 40 * 5151115 * 2
def baseEnd_5151115 : Nat := 2644997901584718972572959

theorem tailTrace_5151115 : CollatzResearch.WordTrace tailWord_5151115 prefixEnd_5151115 2644997901584718972572959 := by
  unfold tailWord_5151115
  simp only [CollatzResearch.WordTrace]
  refine ⟨187876598733397570247398799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125251065822265046831599199 187876598733397570247398799)
  ·
    refine ⟨281814898100096355371098199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187876598733397570247398799 281814898100096355371098199)
    ·
      refine ⟨422722347150144533056647299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281814898100096355371098199 422722347150144533056647299)
      ·
        refine ⟨634083520725216799584970949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422722347150144533056647299 634083520725216799584970949)
        ·
          refine ⟨118890660135978149922182053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 634083520725216799584970949 118890660135978149922182053)
          ·
            refine ⟨22291998775495903110409135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118890660135978149922182053 22291998775495903110409135)
            ·
              refine ⟨33437998163243854665613703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22291998775495903110409135 33437998163243854665613703)
              ·
                refine ⟨50156997244865781998420555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33437998163243854665613703 50156997244865781998420555)
                ·
                  refine ⟨75235495867298672997630833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50156997244865781998420555 75235495867298672997630833)
                  ·
                    refine ⟨56426621900474004748223125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75235495867298672997630833 56426621900474004748223125)
                    ·
                      refine ⟨2644997901584718972572959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56426621900474004748223125 2644997901584718972572959)
                      ·
                        rfl

theorem cell23_5151115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_5151115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151115 prefixEnd_5151115 := by exact prefixLift 5151115
  have htrace : WordTrace (prefixWord ++ tailWord_5151115) baseStart_5151115 baseEnd_5151115 := by
    simpa [prefixWord, tailWord_5151115, baseEnd_5151115] using wordTrace_append hprefix tailTrace_5151115
  have hstable : (prefixWord ++ tailWord_5151115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151115).length < 2 ^ (prefixWord ++ tailWord_5151115).sum := by decide
  have hdescent : baseEnd_5151115 < baseStart_5151115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151139 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 3]
def baseStart_5151139 : Nat := 118140960795 + 5151139 * 2 ^ 59
def prefixEnd_5151139 : Nat := 4983230072969 + 3 ^ 40 * 5151139 * 2
def baseEnd_5151139 : Nat := 2645010225120426878672849

theorem tailTrace_5151139 : CollatzResearch.WordTrace tailWord_5151139 prefixEnd_5151139 2645010225120426878672849 := by
  unfold tailWord_5151139
  simp only [CollatzResearch.WordTrace]
  refine ⟨187877474085310622346272471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125251649390207081564181647 187877474085310622346272471)
  ·
    refine ⟨281816211127965933519408707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187877474085310622346272471 281816211127965933519408707)
    ·
      refine ⟨422724316691948900279113061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281816211127965933519408707 422724316691948900279113061)
      ·
        refine ⟨79260809379740418802333699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422724316691948900279113061 79260809379740418802333699)
        ·
          refine ⟨118891214069610628203500549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79260809379740418802333699 118891214069610628203500549)
          ·
            refine ⟨22292102638051992788156353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118891214069610628203500549 22292102638051992788156353)
            ·
              refine ⟨16719076978538994591117265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22292102638051992788156353 16719076978538994591117265)
              ·
                refine ⟨12539307733904245943337949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16719076978538994591117265 12539307733904245943337949)
                ·
                  refine ⟨4702240400214092228751731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12539307733904245943337949 4702240400214092228751731)
                  ·
                    refine ⟨7053360600321138343127597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4702240400214092228751731 7053360600321138343127597)
                    ·
                      refine ⟨2645010225120426878672849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053360600321138343127597 2645010225120426878672849)
                      ·
                        rfl

theorem cell23_5151139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_5151139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151139 prefixEnd_5151139 := by exact prefixLift 5151139
  have htrace : WordTrace (prefixWord ++ tailWord_5151139) baseStart_5151139 baseEnd_5151139 := by
    simpa [prefixWord, tailWord_5151139, baseEnd_5151139] using wordTrace_append hprefix tailTrace_5151139
  have hstable : (prefixWord ++ tailWord_5151139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151139).length < 2 ^ (prefixWord ++ tailWord_5151139).sum := by decide
  have hdescent : baseEnd_5151139 < baseStart_5151139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151145 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_5151145 : Nat := 118140960795 + 5151145 * 2 ^ 59
def prefixEnd_5151145 : Nat := 4983230072969 + 3 ^ 40 * 5151145 * 2
def baseEnd_5151145 : Nat := 2645013306004353855197821

theorem tailTrace_5151145 : CollatzResearch.WordTrace tailWord_5151145 prefixEnd_5151145 2645013306004353855197821 := by
  unfold tailWord_5151145
  simp only [CollatzResearch.WordTrace]
  refine ⟨187877692923288885370990889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125251795282192590247327259 187877692923288885370990889)
  ·
    refine ⟨140908269692466664028243167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187877692923288885370990889 140908269692466664028243167)
    ·
      refine ⟨211362404538699996042364751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140908269692466664028243167 211362404538699996042364751)
      ·
        refine ⟨317043606808049994063547127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211362404538699996042364751 317043606808049994063547127)
        ·
          refine ⟨475565410212074991095320691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317043606808049994063547127 475565410212074991095320691)
          ·
            refine ⟨713348115318112486642981037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475565410212074991095320691 713348115318112486642981037)
            ·
              refine ⟨267505543244292182491117889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713348115318112486642981037 267505543244292182491117889)
              ·
                refine ⟨200629157433219136868338417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267505543244292182491117889 200629157433219136868338417)
                ·
                  refine ⟨150471868074914352651253813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200629157433219136868338417 150471868074914352651253813)
                  ·
                    refine ⟨14106737632023220561055045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150471868074914352651253813 14106737632023220561055045)
                    ·
                      refine ⟨2645013306004353855197821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14106737632023220561055045 2645013306004353855197821)
                      ·
                        rfl

theorem cell23_5151145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_5151145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151145 prefixEnd_5151145 := by exact prefixLift 5151145
  have htrace : WordTrace (prefixWord ++ tailWord_5151145) baseStart_5151145 baseEnd_5151145 := by
    simpa [prefixWord, tailWord_5151145, baseEnd_5151145] using wordTrace_append hprefix tailTrace_5151145
  have hstable : (prefixWord ++ tailWord_5151145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151145).length < 2 ^ (prefixWord ++ tailWord_5151145).sum := by decide
  have hdescent : baseEnd_5151145 < baseStart_5151145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151182 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_5151182 : Nat := 118140960795 + 5151182 * 2 ^ 59
def prefixEnd_5151182 : Nat := 4983230072969 + 3 ^ 40 * 5151182 * 2
def baseEnd_5151182 : Nat := 2645032304788570210435151

theorem tailTrace_5151182 : CollatzResearch.WordTrace tailWord_5151182 prefixEnd_5151182 2645032304788570210435151 := by
  unfold tailWord_5151182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23484880303019355086260975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125252694949436560460058533 23484880303019355086260975)
  ·
    refine ⟨35227320454529032629391463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23484880303019355086260975 35227320454529032629391463)
    ·
      refine ⟨52840980681793548944087195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35227320454529032629391463 52840980681793548944087195)
      ·
        refine ⟨79261471022690323416130793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52840980681793548944087195 79261471022690323416130793)
        ·
          refine ⟨59446103267017742562098095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79261471022690323416130793 59446103267017742562098095)
          ·
            refine ⟨89169154900526613843147143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59446103267017742562098095 89169154900526613843147143)
            ·
              refine ⟨133753732350789920764720715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89169154900526613843147143 133753732350789920764720715)
              ·
                refine ⟨200630598526184881147081073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133753732350789920764720715 200630598526184881147081073)
                ·
                  refine ⟨150472948894638660860310805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200630598526184881147081073 150472948894638660860310805)
                  ·
                    refine ⟨7053419479436187227827069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 150472948894638660860310805 7053419479436187227827069)
                    ·
                      refine ⟨2645032304788570210435151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053419479436187227827069 2645032304788570210435151)
                      ·
                        rfl

theorem cell23_5151182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_5151182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151182 prefixEnd_5151182 := by exact prefixLift 5151182
  have htrace : WordTrace (prefixWord ++ tailWord_5151182) baseStart_5151182 baseEnd_5151182 := by
    simpa [prefixWord, tailWord_5151182, baseEnd_5151182] using wordTrace_append hprefix tailTrace_5151182
  have hstable : (prefixWord ++ tailWord_5151182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151182).length < 2 ^ (prefixWord ++ tailWord_5151182).sum := by decide
  have hdescent : baseEnd_5151182 < baseStart_5151182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151192 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5151192 : Nat := 118140960795 + 5151192 * 2 ^ 59
def prefixEnd_5151192 : Nat := 4983230072969 + 3 ^ 40 * 5151192 * 2
def baseEnd_5151192 : Nat := 2645037439595115171310105

theorem tailTrace_5151192 : CollatzResearch.WordTrace tailWord_5151192 prefixEnd_5151192 2645037439595115171310105 := by
  unfold tailWord_5151192
  simp only [CollatzResearch.WordTrace]
  refine ⟨93939703577059306198975915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125252938102745741598634553 93939703577059306198975915)
  ·
    refine ⟨140909555365588959298463873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93939703577059306198975915 140909555365588959298463873)
    ·
      refine ⟨105682166524191719473847905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140909555365588959298463873 105682166524191719473847905)
      ·
        refine ⟨79261624893143789605385929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105682166524191719473847905 79261624893143789605385929)
        ·
          refine ⟨59446218669857842204039447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79261624893143789605385929 59446218669857842204039447)
          ·
            refine ⟨89169328004786763306059171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59446218669857842204039447 89169328004786763306059171)
            ·
              refine ⟨133753992007180144959088757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89169328004786763306059171 133753992007180144959088757)
              ·
                refine ⟨12539436750673138589914571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133753992007180144959088757 12539436750673138589914571)
                ·
                  refine ⟨18809155126009707884871857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12539436750673138589914571 18809155126009707884871857)
                  ·
                    refine ⟨14106866344507280913653893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18809155126009707884871857 14106866344507280913653893)
                    ·
                      refine ⟨2645037439595115171310105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14106866344507280913653893 2645037439595115171310105)
                      ·
                        rfl

theorem cell23_5151192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5151192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151192 prefixEnd_5151192 := by exact prefixLift 5151192
  have htrace : WordTrace (prefixWord ++ tailWord_5151192) baseStart_5151192 baseEnd_5151192 := by
    simpa [prefixWord, tailWord_5151192, baseEnd_5151192] using wordTrace_append hprefix tailTrace_5151192
  have hstable : (prefixWord ++ tailWord_5151192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151192).length < 2 ^ (prefixWord ++ tailWord_5151192).sum := by decide
  have hdescent : baseEnd_5151192 < baseStart_5151192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151199 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_5151199 : Nat := 118140960795 + 5151199 * 2 ^ 59
def prefixEnd_5151199 : Nat := 4983230072969 + 3 ^ 40 * 5151199 * 2
def baseEnd_5151199 : Nat := 2645041033959696643922573

theorem tailTrace_5151199 : CollatzResearch.WordTrace tailWord_5151199 prefixEnd_5151199 2645041033959696643922573 := by
  unfold tailWord_5151199
  simp only [CollatzResearch.WordTrace]
  refine ⟨187879662465093252593456651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125253108310062168395637767 187879662465093252593456651)
  ·
    refine ⟨281819493697639878890184977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187879662465093252593456651 281819493697639878890184977)
    ·
      refine ⟨211364620273229909167638733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281819493697639878890184977 211364620273229909167638733)
      ·
        refine ⟨79261732602461215937864525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211364620273229909167638733 79261732602461215937864525)
        ·
          refine ⟨29723149725922955976699197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79261732602461215937864525 29723149725922955976699197)
          ·
            refine ⟨11146181147221108491262199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29723149725922955976699197 11146181147221108491262199)
            ·
              refine ⟨16719271720831662736893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11146181147221108491262199 16719271720831662736893299)
              ·
                refine ⟨25078907581247494105339949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16719271720831662736893299 25078907581247494105339949)
                ·
                  refine ⟨9404590342967810289502481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25078907581247494105339949 9404590342967810289502481)
                  ·
                    refine ⟨7053442757225857717126861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9404590342967810289502481 7053442757225857717126861)
                    ·
                      refine ⟨2645041033959696643922573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053442757225857717126861 2645041033959696643922573)
                      ·
                        rfl

theorem cell23_5151199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_5151199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151199 prefixEnd_5151199 := by exact prefixLift 5151199
  have htrace : WordTrace (prefixWord ++ tailWord_5151199) baseStart_5151199 baseEnd_5151199 := by
    simpa [prefixWord, tailWord_5151199, baseEnd_5151199] using wordTrace_append hprefix tailTrace_5151199
  have hstable : (prefixWord ++ tailWord_5151199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151199).length < 2 ^ (prefixWord ++ tailWord_5151199).sum := by decide
  have hdescent : baseEnd_5151199 < baseStart_5151199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151213 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5151213 : Nat := 118140960795 + 5151213 * 2 ^ 59
def prefixEnd_5151213 : Nat := 4983230072969 + 3 ^ 40 * 5151213 * 2
def baseEnd_5151213 : Nat := 2645048222688859589147509

theorem tailTrace_5151213 : CollatzResearch.WordTrace tailWord_5151213 prefixEnd_5151213 2645048222688859589147509 := by
  unfold tailWord_5151213
  simp only [CollatzResearch.WordTrace]
  refine ⟨187880173087042532984466293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125253448724695021989644195 187880173087042532984466293)
  ·
    refine ⟨17613766226910237467293715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187880173087042532984466293 17613766226910237467293715)
    ·
      refine ⟨26420649340365356200940573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17613766226910237467293715 26420649340365356200940573)
      ·
        refine ⟨9907743502637008575352715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26420649340365356200940573 9907743502637008575352715)
        ·
          refine ⟨14861615253955512863029073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907743502637008575352715 14861615253955512863029073)
          ·
            refine ⟨11146211440466634647271805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14861615253955512863029073 11146211440466634647271805)
            ·
              refine ⟨4179829290174987992726927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11146211440466634647271805 4179829290174987992726927)
              ·
                refine ⟨6269743935262481989090391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179829290174987992726927 6269743935262481989090391)
                ·
                  refine ⟨9404615902893722983635587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269743935262481989090391 9404615902893722983635587)
                  ·
                    refine ⟨14106923854340584475453381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9404615902893722983635587 14106923854340584475453381)
                    ·
                      refine ⟨2645048222688859589147509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14106923854340584475453381 2645048222688859589147509)
                      ·
                        rfl

theorem cell23_5151213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5151213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151213 prefixEnd_5151213 := by exact prefixLift 5151213
  have htrace : WordTrace (prefixWord ++ tailWord_5151213) baseStart_5151213 baseEnd_5151213 := by
    simpa [prefixWord, tailWord_5151213, baseEnd_5151213] using wordTrace_append hprefix tailTrace_5151213
  have hstable : (prefixWord ++ tailWord_5151213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151213).length < 2 ^ (prefixWord ++ tailWord_5151213).sum := by decide
  have hdescent : baseEnd_5151213 < baseStart_5151213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151216 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3]
def baseStart_5151216 : Nat := 118140960795 + 5151216 * 2 ^ 59
def prefixEnd_5151216 : Nat := 4983230072969 + 3 ^ 40 * 5151216 * 2
def baseEnd_5151216 : Nat := 2645049763130823077409995

theorem tailTrace_5151216 : CollatzResearch.WordTrace tailWord_5151216 prefixEnd_5151216 2645049763130823077409995 := by
  unfold tailWord_5151216
  simp only [CollatzResearch.WordTrace]
  refine ⟨93940141253015832248412751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125253521670687776331217001 93940141253015832248412751)
  ·
    refine ⟨140910211879523748372619127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93940141253015832248412751 140910211879523748372619127)
    ·
      refine ⟨211365317819285622558928691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140910211879523748372619127 211365317819285622558928691)
      ·
        refine ⟨317047976728928433838393037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211365317819285622558928691 317047976728928433838393037)
        ·
          refine ⟨118892991273348162689397389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317047976728928433838393037 118892991273348162689397389)
          ·
            refine ⟨44584871727505561008524021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118892991273348162689397389 44584871727505561008524021)
            ·
              refine ⟨4179831724453646344549127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44584871727505561008524021 4179831724453646344549127)
              ·
                refine ⟨6269747586680469516823691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179831724453646344549127 6269747586680469516823691)
                ·
                  refine ⟨9404621380020704275235537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269747586680469516823691 9404621380020704275235537)
                  ·
                    refine ⟨7053466035015528206426653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9404621380020704275235537 7053466035015528206426653)
                    ·
                      refine ⟨2645049763130823077409995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053466035015528206426653 2645049763130823077409995)
                      ·
                        rfl

theorem cell23_5151216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3].length) (baseStart_5151216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151216 prefixEnd_5151216 := by exact prefixLift 5151216
  have htrace : WordTrace (prefixWord ++ tailWord_5151216) baseStart_5151216 baseEnd_5151216 := by
    simpa [prefixWord, tailWord_5151216, baseEnd_5151216] using wordTrace_append hprefix tailTrace_5151216
  have hstable : (prefixWord ++ tailWord_5151216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151216).length < 2 ^ (prefixWord ++ tailWord_5151216).sum := by decide
  have hdescent : baseEnd_5151216 < baseStart_5151216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151246 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5151246 : Nat := 118140960795 + 5151246 * 2 ^ 59
def prefixEnd_5151246 : Nat := 4983230072969 + 3 ^ 40 * 5151246 * 2
def baseEnd_5151246 : Nat := 2645065167550457960034857

theorem tailTrace_5151246 : CollatzResearch.WordTrace tailWord_5151246 prefixEnd_5151246 2645065167550457960034857 := by
  unfold tailWord_5151246
  simp only [CollatzResearch.WordTrace]
  refine ⟨23485172086990372452552199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125254251130615319746945061 23485172086990372452552199)
  ·
    refine ⟨35227758130485558678828299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23485172086990372452552199 35227758130485558678828299)
    ·
      refine ⟨52841637195728338018242449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35227758130485558678828299 52841637195728338018242449)
      ·
        refine ⟨39631227896796253513681837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52841637195728338018242449 39631227896796253513681837)
        ·
          refine ⟨14861710461298595067630689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39631227896796253513681837 14861710461298595067630689)
          ·
            refine ⟨11146282845973946300723017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14861710461298595067630689 11146282845973946300723017)
            ·
              refine ⟨8359712134480459725542263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11146282845973946300723017 8359712134480459725542263)
              ·
                refine ⟨12539568201720689588313395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359712134480459725542263 12539568201720689588313395)
                ·
                  refine ⟨18809352302581034382470093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12539568201720689588313395 18809352302581034382470093)
                  ·
                    refine ⟨7053507113467887893426285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18809352302581034382470093 7053507113467887893426285)
                    ·
                      refine ⟨2645065167550457960034857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053507113467887893426285 2645065167550457960034857)
                      ·
                        rfl

theorem cell23_5151246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5151246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151246 prefixEnd_5151246 := by exact prefixLift 5151246
  have htrace : WordTrace (prefixWord ++ tailWord_5151246) baseStart_5151246 baseEnd_5151246 := by
    simpa [prefixWord, tailWord_5151246, baseEnd_5151246] using wordTrace_append hprefix tailTrace_5151246
  have hstable : (prefixWord ++ tailWord_5151246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151246).length < 2 ^ (prefixWord ++ tailWord_5151246).sum := by decide
  have hdescent : baseEnd_5151246 < baseStart_5151246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151256 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5151256 : Nat := 118140960795 + 5151256 * 2 ^ 59
def prefixEnd_5151256 : Nat := 4983230072969 + 3 ^ 40 * 5151256 * 2
def baseEnd_5151256 : Nat := 2645070302357002920909811

theorem tailTrace_5151256 : CollatzResearch.WordTrace tailWord_5151256 prefixEnd_5151256 2645070302357002920909811 := by
  unfold tailWord_5151256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93940870712943375664140811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125254494283924500885521081 93940870712943375664140811)
  ·
    refine ⟨140911306069415063496211217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93940870712943375664140811 140911306069415063496211217)
    ·
      refine ⟨105683479552061297622158413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140911306069415063496211217 105683479552061297622158413)
      ·
        refine ⟨39631304832022986608309405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105683479552061297622158413 39631304832022986608309405)
        ·
          refine ⟨14861739312008619978116027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39631304832022986608309405 14861739312008619978116027)
          ·
            refine ⟨22292608968012929967174041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14861739312008619978116027 22292608968012929967174041)
            ·
              refine ⟨16719456726009697475380531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22292608968012929967174041 16719456726009697475380531)
              ·
                refine ⟨25079185089014546213070797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16719456726009697475380531 25079185089014546213070797)
                ·
                  refine ⟨9404694408380454829901549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25079185089014546213070797 9404694408380454829901549)
                  ·
                    refine ⟨3526760403142670561213081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9404694408380454829901549 3526760403142670561213081)
                    ·
                      refine ⟨2645070302357002920909811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526760403142670561213081 2645070302357002920909811)
                      ·
                        rfl

theorem cell23_5151256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5151256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151256 prefixEnd_5151256 := by exact prefixLift 5151256
  have htrace : WordTrace (prefixWord ++ tailWord_5151256) baseStart_5151256 baseEnd_5151256 := by
    simpa [prefixWord, tailWord_5151256, baseEnd_5151256] using wordTrace_append hprefix tailTrace_5151256
  have hstable : (prefixWord ++ tailWord_5151256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151256).length < 2 ^ (prefixWord ++ tailWord_5151256).sum := by decide
  have hdescent : baseEnd_5151256 < baseStart_5151256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151303 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_5151303 : Nat := 118140960795 + 5151303 * 2 ^ 59
def prefixEnd_5151303 : Nat := 4983230072969 + 3 ^ 40 * 5151303 * 2
def baseEnd_5151303 : Nat := 2645094435947764237022095

theorem tailTrace_5151303 : CollatzResearch.WordTrace tailWord_5151303 prefixEnd_5151303 2645094435947764237022095 := by
  unfold tailWord_5151303
  simp only [CollatzResearch.WordTrace]
  refine ⟨187883455656716478355242563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125255637104477652236828375 187883455656716478355242563)
  ·
    refine ⟨281825183485074717532863845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187883455656716478355242563 281825183485074717532863845)
    ·
      refine ⟨52842221903451509537411971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281825183485074717532863845 52842221903451509537411971)
      ·
        refine ⟨79263332855177264306117957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52842221903451509537411971 79263332855177264306117957)
        ·
          refine ⟨14861874910345737057397117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79263332855177264306117957 14861874910345737057397117)
          ·
            refine ⟨5573203091379651396523919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14861874910345737057397117 5573203091379651396523919)
            ·
              refine ⟨8359804637069477094785879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573203091379651396523919 8359804637069477094785879)
              ·
                refine ⟨12539706955604215642178819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359804637069477094785879 12539706955604215642178819)
                ·
                  refine ⟨18809560433406323463268229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12539706955604215642178819 18809560433406323463268229)
                  ·
                    refine ⟨3526792581263685649362793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18809560433406323463268229 3526792581263685649362793)
                    ·
                      refine ⟨2645094435947764237022095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526792581263685649362793 2645094435947764237022095)
                      ·
                        rfl

theorem cell23_5151303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_5151303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151303 prefixEnd_5151303 := by exact prefixLift 5151303
  have htrace : WordTrace (prefixWord ++ tailWord_5151303) baseStart_5151303 baseEnd_5151303 := by
    simpa [prefixWord, tailWord_5151303, baseEnd_5151303] using wordTrace_append hprefix tailTrace_5151303
  have hstable : (prefixWord ++ tailWord_5151303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151303).length < 2 ^ (prefixWord ++ tailWord_5151303).sum := by decide
  have hdescent : baseEnd_5151303 < baseStart_5151303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151369 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_5151369 : Nat := 118140960795 + 5151369 * 2 ^ 59
def prefixEnd_5151369 : Nat := 4983230072969 + 3 ^ 40 * 5151369 * 2
def baseEnd_5151369 : Nat := 881709441890320326265597

theorem tailTrace_5151369 : CollatzResearch.WordTrace tailWord_5151369 prefixEnd_5151369 881709441890320326265597 := by
  unfold tailWord_5151369
  simp only [CollatzResearch.WordTrace]
  refine ⟨187885862874477371627145161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125257241916318247751430107 187885862874477371627145161)
  ·
    refine ⟨140914397155858028720358871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187885862874477371627145161 140914397155858028720358871)
    ·
      refine ⟨211371595733787043080538307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140914397155858028720358871 211371595733787043080538307)
      ·
        refine ⟨317057393600680564620807461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211371595733787043080538307 317057393600680564620807461)
        ·
          refine ⟨59448261300127605866401399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317057393600680564620807461 59448261300127605866401399)
          ·
            refine ⟨89172391950191408799602099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59448261300127605866401399 89172391950191408799602099)
            ·
              refine ⟨133758587925287113199403149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89172391950191408799602099 133758587925287113199403149)
              ·
                refine ⟨50159470471982667449776181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133758587925287113199403149 50159470471982667449776181)
                ·
                  refine ⟨4702450356748375073416517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50159470471982667449776181 4702450356748375073416517)
                  ·
                    refine ⟨881709441890320326265597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702450356748375073416517 881709441890320326265597)
                    ·
                      rfl

theorem cell23_5151369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_5151369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151369 prefixEnd_5151369 := by exact prefixLift 5151369
  have htrace : WordTrace (prefixWord ++ tailWord_5151369) baseStart_5151369 baseEnd_5151369 := by
    simpa [prefixWord, tailWord_5151369, baseEnd_5151369] using wordTrace_append hprefix tailTrace_5151369
  have hstable : (prefixWord ++ tailWord_5151369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151369).length < 2 ^ (prefixWord ++ tailWord_5151369).sum := by decide
  have hdescent : baseEnd_5151369 < baseStart_5151369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151379 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3]
def baseStart_5151379 : Nat := 118140960795 + 5151379 * 2 ^ 59
def prefixEnd_5151379 : Nat := 4983230072969 + 3 ^ 40 * 5151379 * 2
def baseEnd_5151379 : Nat := 2645133460477505939671745

theorem tailTrace_5151379 : CollatzResearch.WordTrace tailWord_5151379 prefixEnd_5151379 2645133460477505939671745 := by
  unfold tailWord_5151379
  simp only [CollatzResearch.WordTrace]
  refine ⟨187886227604441143335009191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125257485069627428890006127 187886227604441143335009191)
  ·
    refine ⟨281829341406661715002513787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187886227604441143335009191 281829341406661715002513787)
    ·
      refine ⟨422744012109992572503770681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281829341406661715002513787 422744012109992572503770681)
      ·
        refine ⟨317058009082494429377828011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422744012109992572503770681 317058009082494429377828011)
        ·
          refine ⟨475587013623741644066742017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317058009082494429377828011 475587013623741644066742017)
          ·
            refine ⟨356690260217806233050056513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475587013623741644066742017 356690260217806233050056513)
            ·
              refine ⟨267517695163354674787542385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356690260217806233050056513 267517695163354674787542385)
              ·
                refine ⟨200638271372516006090656789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267517695163354674787542385 200638271372516006090656789)
                ·
                  refine ⟨9404918970586687785499537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200638271372516006090656789 9404918970586687785499537)
                  ·
                    refine ⟨7053689227940015839124653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9404918970586687785499537 7053689227940015839124653)
                    ·
                      refine ⟨2645133460477505939671745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053689227940015839124653 2645133460477505939671745)
                      ·
                        rfl

theorem cell23_5151379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_5151379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151379 prefixEnd_5151379 := by exact prefixLift 5151379
  have htrace : WordTrace (prefixWord ++ tailWord_5151379) baseStart_5151379 baseEnd_5151379 := by
    simpa [prefixWord, tailWord_5151379, baseEnd_5151379] using wordTrace_append hprefix tailTrace_5151379
  have hstable : (prefixWord ++ tailWord_5151379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151379).length < 2 ^ (prefixWord ++ tailWord_5151379).sum := by decide
  have hdescent : baseEnd_5151379 < baseStart_5151379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151396 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_5151396 : Nat := 118140960795 + 5151396 * 2 ^ 59
def prefixEnd_5151396 : Nat := 4983230072969 + 3 ^ 40 * 5151396 * 2
def baseEnd_5151396 : Nat := 2645142189648632373159167

theorem tailTrace_5151396 : CollatzResearch.WordTrace tailWord_5151396 prefixEnd_5151396 2645142189648632373159167 := by
  unfold tailWord_5151396
  simp only [CollatzResearch.WordTrace]
  refine ⟨93943423822689777619189021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125257898430253036825585361 93943423822689777619189021)
  ·
    refine ⟨35228783933508666607195883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93943423822689777619189021 35228783933508666607195883)
    ·
      refine ⟨52843175900262999910793825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35228783933508666607195883 52843175900262999910793825)
      ·
        refine ⟨39632381925197249933095369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52843175900262999910793825 39632381925197249933095369)
        ·
          refine ⟨29724286443897937449821527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39632381925197249933095369 29724286443897937449821527)
          ·
            refine ⟨44586429665846906174732291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29724286443897937449821527 44586429665846906174732291)
            ·
              refine ⟨66879644498770359262098437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44586429665846906174732291 66879644498770359262098437)
              ·
                refine ⟨12539933343519442361643457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66879644498770359262098437 12539933343519442361643457)
                ·
                  refine ⟨9404950007639581771232593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12539933343519442361643457 9404950007639581771232593)
                  ·
                    refine ⟨7053712505729686328424445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9404950007639581771232593 7053712505729686328424445)
                    ·
                      refine ⟨2645142189648632373159167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053712505729686328424445 2645142189648632373159167)
                      ·
                        rfl

theorem cell23_5151396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_5151396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151396 prefixEnd_5151396 := by exact prefixLift 5151396
  have htrace : WordTrace (prefixWord ++ tailWord_5151396) baseStart_5151396 baseEnd_5151396 := by
    simpa [prefixWord, tailWord_5151396, baseEnd_5151396] using wordTrace_append hprefix tailTrace_5151396
  have hstable : (prefixWord ++ tailWord_5151396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151396).length < 2 ^ (prefixWord ++ tailWord_5151396).sum := by decide
  have hdescent : baseEnd_5151396 < baseStart_5151396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151460 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_5151460 : Nat := 118140960795 + 5151460 * 2 ^ 59
def prefixEnd_5151460 : Nat := 4983230072969 + 3 ^ 40 * 5151460 * 2
def baseEnd_5151460 : Nat := 2645175052410520122758873

theorem tailTrace_5151460 : CollatzResearch.WordTrace tailWord_5151460 prefixEnd_5151460 2645175052410520122758873 := by
  unfold tailWord_5151460
  simp only [CollatzResearch.WordTrace]
  refine ⟨93944590958573847084353917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125259454611431796112471889 93944590958573847084353917)
  ·
    refine ⟨35229221609465192656632719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93944590958573847084353917 35229221609465192656632719)
    ·
      refine ⟨52843832414197788984949079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35229221609465192656632719 52843832414197788984949079)
      ·
        refine ⟨79265748621296683477423619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52843832414197788984949079 79265748621296683477423619)
        ·
          refine ⟨118898622931945025216135429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79265748621296683477423619 118898622931945025216135429)
          ·
            refine ⟨22293491799739692228025393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118898622931945025216135429 22293491799739692228025393)
            ·
              refine ⟨16720118849804769171019045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22293491799739692228025393 16720118849804769171019045)
              ·
                refine ⟨3135022284338394219566071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16720118849804769171019045 3135022284338394219566071)
                ·
                  refine ⟨4702533426507591329349107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135022284338394219566071 4702533426507591329349107)
                  ·
                    refine ⟨7053800139761386994023661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4702533426507591329349107 7053800139761386994023661)
                    ·
                      refine ⟨2645175052410520122758873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053800139761386994023661 2645175052410520122758873)
                      ·
                        rfl

theorem cell23_5151460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_5151460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151460 prefixEnd_5151460 := by exact prefixLift 5151460
  have htrace : WordTrace (prefixWord ++ tailWord_5151460) baseStart_5151460 baseEnd_5151460 := by
    simpa [prefixWord, tailWord_5151460, baseEnd_5151460] using wordTrace_append hprefix tailTrace_5151460
  have hstable : (prefixWord ++ tailWord_5151460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151460).length < 2 ^ (prefixWord ++ tailWord_5151460).sum := by decide
  have hdescent : baseEnd_5151460 < baseStart_5151460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151529 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_5151529 : Nat := 118140960795 + 5151529 * 2 ^ 59
def prefixEnd_5151529 : Nat := 4983230072969 + 3 ^ 40 * 5151529 * 2
def baseEnd_5151529 : Nat := 2645210482575680352796055

theorem tailTrace_5151529 : CollatzResearch.WordTrace tailWord_5151529 prefixEnd_5151529 2645210482575680352796055 := by
  unfold tailWord_5151529
  simp only [CollatzResearch.WordTrace]
  refine ⟨187891698553897718952969641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125261132369265145968646427 187891698553897718952969641)
  ·
    refine ⟨140918773915423289214727231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187891698553897718952969641 140918773915423289214727231)
    ·
      refine ⟨211378160873134933822090847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140918773915423289214727231 211378160873134933822090847)
      ·
        refine ⟨317067241309702400733136271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211378160873134933822090847 317067241309702400733136271)
        ·
          refine ⟨475600861964553601099704407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317067241309702400733136271 475600861964553601099704407)
          ·
            refine ⟨713401292946830401649556611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475600861964553601099704407 713401292946830401649556611)
            ·
              refine ⟨1070101939420245602474334917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713401292946830401649556611 1070101939420245602474334917)
              ·
                refine ⟨200644113641296050463937797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1070101939420245602474334917 200644113641296050463937797)
                ·
                  refine ⟨37620771307743009461988337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200644113641296050463937797 37620771307743009461988337)
                  ·
                    refine ⟨28215578480807257096491253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37620771307743009461988337 28215578480807257096491253)
                    ·
                      refine ⟨2645210482575680352796055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28215578480807257096491253 2645210482575680352796055)
                      ·
                        rfl

theorem cell23_5151529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_5151529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151529 prefixEnd_5151529 := by exact prefixLift 5151529
  have htrace : WordTrace (prefixWord ++ tailWord_5151529) baseStart_5151529 baseEnd_5151529 := by
    simpa [prefixWord, tailWord_5151529, baseEnd_5151529] using wordTrace_append hprefix tailTrace_5151529
  have hstable : (prefixWord ++ tailWord_5151529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151529).length < 2 ^ (prefixWord ++ tailWord_5151529).sum := by decide
  have hdescent : baseEnd_5151529 < baseStart_5151529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151543 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_5151543 : Nat := 118140960795 + 5151543 * 2 ^ 59
def prefixEnd_5151543 : Nat := 4983230072969 + 3 ^ 40 * 5151543 * 2
def baseEnd_5151543 : Nat := 2645217671304843298020991

theorem tailTrace_5151543 : CollatzResearch.WordTrace tailWord_5151543 prefixEnd_5151543 2645217671304843298020991 := by
  unfold tailWord_5151543
  simp only [CollatzResearch.WordTrace]
  refine ⟨187892209175846999343979283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125261472783897999562652855 187892209175846999343979283)
  ·
    refine ⟨281838313763770499015968925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187892209175846999343979283 281838313763770499015968925)
    ·
      refine ⟨105689367661413937130988347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281838313763770499015968925 105689367661413937130988347)
      ·
        refine ⟨158534051492120905696482521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105689367661413937130988347 158534051492120905696482521)
        ·
          refine ⟨118900538619090679272361891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158534051492120905696482521 118900538619090679272361891)
          ·
            refine ⟨178350807928636018908542837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118900538619090679272361891 178350807928636018908542837)
            ·
              refine ⟨16720388243309626772675891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178350807928636018908542837 16720388243309626772675891)
              ·
                refine ⟨25080582364964440159013837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16720388243309626772675891 25080582364964440159013837)
                ·
                  refine ⟨9405218386861665059630189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25080582364964440159013837 9405218386861665059630189)
                  ·
                    refine ⟨3526956895073124397361321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9405218386861665059630189 3526956895073124397361321)
                    ·
                      refine ⟨2645217671304843298020991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526956895073124397361321 2645217671304843298020991)
                      ·
                        rfl

theorem cell23_5151543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_5151543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151543 prefixEnd_5151543 := by exact prefixLift 5151543
  have htrace : WordTrace (prefixWord ++ tailWord_5151543) baseStart_5151543 baseEnd_5151543 := by
    simpa [prefixWord, tailWord_5151543, baseEnd_5151543] using wordTrace_append hprefix tailTrace_5151543
  have hstable : (prefixWord ++ tailWord_5151543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151543).length < 2 ^ (prefixWord ++ tailWord_5151543).sum := by decide
  have hdescent : baseEnd_5151543 < baseStart_5151543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151550 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5151550 : Nat := 118140960795 + 5151550 * 2 ^ 59
def prefixEnd_5151550 : Nat := 4983230072969 + 3 ^ 40 * 5151550 * 2
def baseEnd_5151550 : Nat := 2645221265669424770633459

theorem tailTrace_5151550 : CollatzResearch.WordTrace tailWord_5151550 prefixEnd_5151550 2645221265669424770633459 := by
  unfold tailWord_5151550
  simp only [CollatzResearch.WordTrace]
  refine ⟨23486558060852704942435513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125261642991214426359656069 23486558060852704942435513)
  ·
    refine ⟨17614918545639528706826635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23486558060852704942435513 17614918545639528706826635)
    ·
      refine ⟨26422377818459293060239953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17614918545639528706826635 26422377818459293060239953)
      ·
        refine ⟨19816783363844469795179965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26422377818459293060239953 19816783363844469795179965)
        ·
          refine ⟨7431293761441676173192487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19816783363844469795179965 7431293761441676173192487)
          ·
            refine ⟨11146940642162514259788731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431293761441676173192487 11146940642162514259788731)
            ·
              refine ⟨16720410963243771389683097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11146940642162514259788731 16720410963243771389683097)
              ·
                refine ⟨12540308222432828542262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16720410963243771389683097 12540308222432828542262323)
                ·
                  refine ⟨18810462333649242813393485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540308222432828542262323 18810462333649242813393485)
                  ·
                    refine ⟨7053923375118466055022557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18810462333649242813393485 7053923375118466055022557)
                    ·
                      refine ⟨2645221265669424770633459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7053923375118466055022557 2645221265669424770633459)
                      ·
                        rfl

theorem cell23_5151550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5151550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151550 prefixEnd_5151550 := by exact prefixLift 5151550
  have htrace : WordTrace (prefixWord ++ tailWord_5151550) baseStart_5151550 baseEnd_5151550 := by
    simpa [prefixWord, tailWord_5151550, baseEnd_5151550] using wordTrace_append hprefix tailTrace_5151550
  have hstable : (prefixWord ++ tailWord_5151550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151550).length < 2 ^ (prefixWord ++ tailWord_5151550).sum := by decide
  have hdescent : baseEnd_5151550 < baseStart_5151550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151573 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5151573 : Nat := 118140960795 + 5151573 * 2 ^ 59
def prefixEnd_5151573 : Nat := 4983230072969 + 3 ^ 40 * 5151573 * 2
def baseEnd_5151573 : Nat := 2645233075724478180645853

theorem tailTrace_5151573 : CollatzResearch.WordTrace tailWord_5151573 prefixEnd_5151573 2645233075724478180645853 := by
  unfold tailWord_5151573
  simp only [CollatzResearch.WordTrace]
  refine ⟨187893303365738314467571373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125262202243825542978380915 187893303365738314467571373)
  ·
    refine ⟨70459988762151867925339265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187893303365738314467571373 70459988762151867925339265)
    ·
      refine ⟨52844991571613900944004449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70459988762151867925339265 52844991571613900944004449)
      ·
        refine ⟨39633743678710425708003337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52844991571613900944004449 39633743678710425708003337)
        ·
          refine ⟨29725307759032819281002503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39633743678710425708003337 29725307759032819281002503)
          ·
            refine ⟨44587961638549228921503755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29725307759032819281002503 44587961638549228921503755)
            ·
              refine ⟨66881942457823843382255633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44587961638549228921503755 66881942457823843382255633)
              ·
                refine ⟨50161456843367882536691725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66881942457823843382255633 50161456843367882536691725)
                ·
                  refine ⟨18810546316262955951259397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50161456843367882536691725 18810546316262955951259397)
                  ·
                    refine ⟨3526977434299304240861137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18810546316262955951259397 3526977434299304240861137)
                    ·
                      refine ⟨2645233075724478180645853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3526977434299304240861137 2645233075724478180645853)
                      ·
                        rfl

theorem cell23_5151573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5151573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151573 prefixEnd_5151573 := by exact prefixLift 5151573
  have htrace : WordTrace (prefixWord ++ tailWord_5151573) baseStart_5151573 baseEnd_5151573 := by
    simpa [prefixWord, tailWord_5151573, baseEnd_5151573] using wordTrace_append hprefix tailTrace_5151573
  have hstable : (prefixWord ++ tailWord_5151573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151573).length < 2 ^ (prefixWord ++ tailWord_5151573).sum := by decide
  have hdescent : baseEnd_5151573 < baseStart_5151573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151596 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 7]
def baseStart_5151596 : Nat := 118140960795 + 5151596 * 2 ^ 59
def prefixEnd_5151596 : Nat := 4983230072969 + 3 ^ 40 * 5151596 * 2
def baseEnd_5151596 : Nat := 293916098419947954517583

theorem tailTrace_5151596 : CollatzResearch.WordTrace tailWord_5151596 prefixEnd_5151596 293916098419947954517583 := by
  unfold tailWord_5151596
  simp only [CollatzResearch.WordTrace]
  refine ⟨93947071122327494697829321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125262761496436659597105761 93947071122327494697829321)
  ·
    refine ⟨70460303341745621023371991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93947071122327494697829321 70460303341745621023371991)
    ·
      refine ⟨105690455012618431535057987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70460303341745621023371991 105690455012618431535057987)
      ·
        refine ⟨158535682518927647302586981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105690455012618431535057987 158535682518927647302586981)
        ·
          refine ⟨29725440472298933869235059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158535682518927647302586981 29725440472298933869235059)
          ·
            refine ⟨44588160708448400803852589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29725440472298933869235059 44588160708448400803852589)
            ·
              refine ⟨16720560265668150301444721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44588160708448400803852589 16720560265668150301444721)
              ·
                refine ⟨12540420199251112726083541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16720560265668150301444721 12540420199251112726083541)
                ·
                  refine ⟨293916098419947954517583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12540420199251112726083541 293916098419947954517583)
                  ·
                    rfl

theorem cell23_5151596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_5151596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151596 prefixEnd_5151596 := by exact prefixLift 5151596
  have htrace : WordTrace (prefixWord ++ tailWord_5151596) baseStart_5151596 baseEnd_5151596 := by
    simpa [prefixWord, tailWord_5151596, baseEnd_5151596] using wordTrace_append hprefix tailTrace_5151596
  have hstable : (prefixWord ++ tailWord_5151596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151596).length < 2 ^ (prefixWord ++ tailWord_5151596).sum := by decide
  have hdescent : baseEnd_5151596 < baseStart_5151596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151613 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 5]
def baseStart_5151613 : Nat := 118140960795 + 5151613 * 2 ^ 59
def prefixEnd_5151613 : Nat := 4983230072969 + 3 ^ 40 * 5151613 * 2
def baseEnd_5151613 : Nat := 293917068327850891571741

theorem tailTrace_5151613 : CollatzResearch.WordTrace tailWord_5151613 prefixEnd_5151613 293917068327850891571741 := by
  unfold tailWord_5151613
  simp only [CollatzResearch.WordTrace]
  refine ⟨187894762285593401299027493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125263174857062267532684995 187894762285593401299027493)
  ·
    refine ⟨35230267928548762743567655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187894762285593401299027493 35230267928548762743567655)
    ·
      refine ⟨52845401892823144115351483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35230267928548762743567655 52845401892823144115351483)
      ·
        refine ⟨79268102839234716173027225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52845401892823144115351483 79268102839234716173027225)
        ·
          refine ⟨59451077129426037129770419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79268102839234716173027225 59451077129426037129770419)
          ·
            refine ⟨89176615694139055694655629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59451077129426037129770419 89176615694139055694655629)
            ·
              refine ⟨33441230885302145885495861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89176615694139055694655629 33441230885302145885495861)
              ·
                refine ⟨3135115395497076176765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33441230885302145885495861 3135115395497076176765237)
                ·
                  refine ⟨293917068327850891571741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135115395497076176765237 293917068327850891571741)
                  ·
                    rfl

theorem cell23_5151613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_5151613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151613 prefixEnd_5151613 := by exact prefixLift 5151613
  have htrace : WordTrace (prefixWord ++ tailWord_5151613) baseStart_5151613 baseEnd_5151613 := by
    simpa [prefixWord, tailWord_5151613, baseEnd_5151613] using wordTrace_append hprefix tailTrace_5151613
  have hstable : (prefixWord ++ tailWord_5151613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151613).length < 2 ^ (prefixWord ++ tailWord_5151613).sum := by decide
  have hdescent : baseEnd_5151613 < baseStart_5151613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151618 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5151618 : Nat := 118140960795 + 5151618 * 2 ^ 59
def prefixEnd_5151618 : Nat := 4983230072969 + 3 ^ 40 * 5151618 * 2
def baseEnd_5151618 : Nat := 2645256182353930504583147

theorem tailTrace_5151618 : CollatzResearch.WordTrace tailWord_5151618 prefixEnd_5151618 2645256182353930504583147 := by
  unfold tailWord_5151618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46973736162643821788239877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125263296433716858101973005 46973736162643821788239877)
  ·
    refine ⟨8807575530495716585294977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46973736162643821788239877 8807575530495716585294977)
    ·
      refine ⟨6605681647871787438971233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8807575530495716585294977 6605681647871787438971233)
      ·
        refine ⟨4954261235903840579228425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605681647871787438971233 4954261235903840579228425)
        ·
          refine ⟨3715695926927880434421319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4954261235903840579228425 3715695926927880434421319)
          ·
            refine ⟨5573543890391820651631979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715695926927880434421319 5573543890391820651631979)
            ·
              refine ⟨8360315835587730977447969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573543890391820651631979 8360315835587730977447969)
              ·
                refine ⟨6270236876690798233085977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360315835587730977447969 6270236876690798233085977)
                ·
                  refine ⟨4702677657518098674814483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270236876690798233085977 4702677657518098674814483)
                  ·
                    refine ⟨7054016486277148012221725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4702677657518098674814483 7054016486277148012221725)
                    ·
                      refine ⟨2645256182353930504583147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054016486277148012221725 2645256182353930504583147)
                      ·
                        rfl

theorem cell23_5151618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5151618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151618 prefixEnd_5151618 := by exact prefixLift 5151618
  have htrace : WordTrace (prefixWord ++ tailWord_5151618) baseStart_5151618 baseEnd_5151618 := by
    simpa [prefixWord, tailWord_5151618, baseEnd_5151618] using wordTrace_append hprefix tailTrace_5151618
  have hstable : (prefixWord ++ tailWord_5151618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151618).length < 2 ^ (prefixWord ++ tailWord_5151618).sum := by decide
  have hdescent : baseEnd_5151618 < baseStart_5151618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151623 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_5151623 : Nat := 118140960795 + 5151623 * 2 ^ 59
def prefixEnd_5151623 : Nat := 4983230072969 + 3 ^ 40 * 5151623 * 2
def baseEnd_5151623 : Nat := 2645258749757202985020623

theorem tailTrace_5151623 : CollatzResearch.WordTrace tailWord_5151623 prefixEnd_5151623 2645258749757202985020623 := by
  unfold tailWord_5151623
  simp only [CollatzResearch.WordTrace]
  refine ⟨187895127015557173006891523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125263418010371448671261015 187895127015557173006891523)
  ·
    refine ⟨281842690523335759510337285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187895127015557173006891523 281842690523335759510337285)
    ·
      refine ⟨52845504473125454908188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281842690523335759510337285 52845504473125454908188241)
      ·
        refine ⟨39634128354844091181141181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52845504473125454908188241 39634128354844091181141181)
        ·
          refine ⟨14862798133066534192927943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39634128354844091181141181 14862798133066534192927943)
          ·
            refine ⟨22294197199599801289391915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14862798133066534192927943 22294197199599801289391915)
            ·
              refine ⟨33441295799399701934087873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22294197199599801289391915 33441295799399701934087873)
              ·
                refine ⟨25080971849549776450565905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33441295799399701934087873 25080971849549776450565905)
                ·
                  refine ⟨18810728887162332337924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25080971849549776450565905 18810728887162332337924429)
                  ·
                    refine ⟨7054023332685874626721661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18810728887162332337924429 7054023332685874626721661)
                    ·
                      refine ⟨2645258749757202985020623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054023332685874626721661 2645258749757202985020623)
                      ·
                        rfl

theorem cell23_5151623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_5151623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151623 prefixEnd_5151623 := by exact prefixLift 5151623
  have htrace : WordTrace (prefixWord ++ tailWord_5151623) baseStart_5151623 baseEnd_5151623 := by
    simpa [prefixWord, tailWord_5151623, baseEnd_5151623] using wordTrace_append hprefix tailTrace_5151623
  have hstable : (prefixWord ++ tailWord_5151623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151623).length < 2 ^ (prefixWord ++ tailWord_5151623).sum := by decide
  have hdescent : baseEnd_5151623 < baseStart_5151623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151624 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_5151624 : Nat := 118140960795 + 5151624 * 2 ^ 59
def prefixEnd_5151624 : Nat := 4983230072969 + 3 ^ 40 * 5151624 * 2
def baseEnd_5151624 : Nat := 2645259263237857481108119

theorem tailTrace_5151624 : CollatzResearch.WordTrace tailWord_5151624 prefixEnd_5151624 2645259263237857481108119 := by
  unfold tailWord_5151624
  simp only [CollatzResearch.WordTrace]
  refine ⟨93947581744276775088838963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125263442325702366785118617 93947581744276775088838963)
  ·
    refine ⟨140921372616415162633258445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93947581744276775088838963 140921372616415162633258445)
    ·
      refine ⟨52845514731155685987471917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140921372616415162633258445 52845514731155685987471917)
      ·
        refine ⟨19817068024183382245301969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52845514731155685987471917 19817068024183382245301969)
        ·
          refine ⟨14862801018137536683976477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19817068024183382245301969 14862801018137536683976477)
          ·
            refine ⟨5573550381801576256491179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14862801018137536683976477 5573550381801576256491179)
            ·
              refine ⟨8360325572702364384736769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573550381801576256491179 8360325572702364384736769)
              ·
                refine ⟨6270244179526773288552577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360325572702364384736769 6270244179526773288552577)
                ·
                  refine ⟨4702683134645079966414433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270244179526773288552577 4702683134645079966414433)
                  ·
                    refine ⟨3527012350983809974810825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4702683134645079966414433 3527012350983809974810825)
                    ·
                      refine ⟨2645259263237857481108119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527012350983809974810825 2645259263237857481108119)
                      ·
                        rfl

theorem cell23_5151624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_5151624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151624 prefixEnd_5151624 := by exact prefixLift 5151624
  have htrace : WordTrace (prefixWord ++ tailWord_5151624) baseStart_5151624 baseEnd_5151624 := by
    simpa [prefixWord, tailWord_5151624, baseEnd_5151624] using wordTrace_append hprefix tailTrace_5151624
  have hstable : (prefixWord ++ tailWord_5151624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151624).length < 2 ^ (prefixWord ++ tailWord_5151624).sum := by decide
  have hdescent : baseEnd_5151624 < baseStart_5151624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 4, 2]
def baseStart_5151663 : Nat := 118140960795 + 5151663 * 2 ^ 59
def prefixEnd_5151663 : Nat := 4983230072969 + 3 ^ 40 * 5151663 * 2
def baseEnd_5151663 : Nat := 2645279288983382828520439

theorem tailTrace_5151663 : CollatzResearch.WordTrace tailWord_5151663 prefixEnd_5151663 2645279288983382828520439 := by
  unfold tailWord_5151663
  simp only [CollatzResearch.WordTrace]
  refine ⟨187896585935412259838347643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125264390623608173225565095 187896585935412259838347643)
  ·
    refine ⟨281844878903118389757521465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187896585935412259838347643 281844878903118389757521465)
    ·
      refine ⟨211383659177338792318141099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281844878903118389757521465 211383659177338792318141099)
      ·
        refine ⟨317075488766008188477211649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211383659177338792318141099 317075488766008188477211649)
        ·
          refine ⟨237806616574506141357908737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317075488766008188477211649 237806616574506141357908737)
          ·
            refine ⟨178354962430879606018431553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237806616574506141357908737 178354962430879606018431553)
            ·
              refine ⟨133766221823159704513823665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178354962430879606018431553 133766221823159704513823665)
              ·
                refine ⟨100324666367369778385367749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133766221823159704513823665 100324666367369778385367749)
                ·
                  refine ⟨18810874943881833447256453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100324666367369778385367749 18810874943881833447256453)
                  ·
                    refine ⟨3527039051977843771360585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18810874943881833447256453 3527039051977843771360585)
                    ·
                      refine ⟨2645279288983382828520439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527039051977843771360585 2645279288983382828520439)
                      ·
                        rfl

theorem cell23_5151663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4, 2].length) (baseStart_5151663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151663 prefixEnd_5151663 := by exact prefixLift 5151663
  have htrace : WordTrace (prefixWord ++ tailWord_5151663) baseStart_5151663 baseEnd_5151663 := by
    simpa [prefixWord, tailWord_5151663, baseEnd_5151663] using wordTrace_append hprefix tailTrace_5151663
  have hstable : (prefixWord ++ tailWord_5151663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151663).length < 2 ^ (prefixWord ++ tailWord_5151663).sum := by decide
  have hdescent : baseEnd_5151663 < baseStart_5151663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151666 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5151666 : Nat := 118140960795 + 5151666 * 2 ^ 59
def prefixEnd_5151666 : Nat := 4983230072969 + 3 ^ 40 * 5151666 * 2
def baseEnd_5151666 : Nat := 2645280829425346316782925

theorem tailTrace_5151666 : CollatzResearch.WordTrace tailWord_5151666 prefixEnd_5151666 2645280829425346316782925 := by
  unfold tailWord_5151666
  simp only [CollatzResearch.WordTrace]
  refine ⟨46974173838600347837676713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125264463569600927567137901 46974173838600347837676713)
  ·
    refine ⟨35230630378950260878257535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46974173838600347837676713 35230630378950260878257535)
    ·
      refine ⟨52845945568425391317386303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35230630378950260878257535 52845945568425391317386303)
      ·
        refine ⟨79268918352638086976079455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52845945568425391317386303 79268918352638086976079455)
        ·
          refine ⟨118903377528957130464119183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79268918352638086976079455 118903377528957130464119183)
          ·
            refine ⟨178355066293435695696178775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118903377528957130464119183 178355066293435695696178775)
            ·
              refine ⟨267532599440153543544268163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178355066293435695696178775 267532599440153543544268163)
              ·
                refine ⟨401298899160230315316402245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267532599440153543544268163 401298899160230315316402245)
                ·
                  refine ⟨75243543592543184121825421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401298899160230315316402245 75243543592543184121825421)
                  ·
                    refine ⟨28216328847203694045684533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75243543592543184121825421 28216328847203694045684533)
                    ·
                      refine ⟨2645280829425346316782925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28216328847203694045684533 2645280829425346316782925)
                      ·
                        rfl

theorem cell23_5151666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5151666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151666 prefixEnd_5151666 := by exact prefixLift 5151666
  have htrace : WordTrace (prefixWord ++ tailWord_5151666) baseStart_5151666 baseEnd_5151666 := by
    simpa [prefixWord, tailWord_5151666, baseEnd_5151666] using wordTrace_append hprefix tailTrace_5151666
  have hstable : (prefixWord ++ tailWord_5151666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151666).length < 2 ^ (prefixWord ++ tailWord_5151666).sum := by decide
  have hdescent : baseEnd_5151666 < baseStart_5151666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151683 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3]
def baseStart_5151683 : Nat := 118140960795 + 5151683 * 2 ^ 59
def prefixEnd_5151683 : Nat := 4983230072969 + 3 ^ 40 * 5151683 * 2
def baseEnd_5151683 : Nat := 2645289558596472750270347

theorem tailTrace_5151683 : CollatzResearch.WordTrace tailWord_5151683 prefixEnd_5151683 2645289558596472750270347 := by
  unfold tailWord_5151683
  simp only [CollatzResearch.WordTrace]
  refine ⟨187897315395339803254075703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125264876930226535502717135 187897315395339803254075703)
  ·
    refine ⟨281845973093009704881113555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187897315395339803254075703 281845973093009704881113555)
    ·
      refine ⟨422768959639514557321670333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281845973093009704881113555 422768959639514557321670333)
      ·
        refine ⟨158538359864817958995626375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 422768959639514557321670333 158538359864817958995626375)
        ·
          refine ⟨237807539797226938493439563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158538359864817958995626375 237807539797226938493439563)
          ·
            refine ⟨356711309695840407740159345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237807539797226938493439563 356711309695840407740159345)
            ·
              refine ⟨267533482271880305805119509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356711309695840407740159345 267533482271880305805119509)
              ·
                refine ⟨12540631981494389334614977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267533482271880305805119509 12540631981494389334614977)
                ·
                  refine ⟨9405473986120792000961233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12540631981494389334614977 9405473986120792000961233)
                  ·
                    refine ⟨7054105489590594000720925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9405473986120792000961233 7054105489590594000720925)
                    ·
                      refine ⟨2645289558596472750270347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054105489590594000720925 2645289558596472750270347)
                      ·
                        rfl

theorem cell23_5151683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_5151683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151683 prefixEnd_5151683 := by exact prefixLift 5151683
  have htrace : WordTrace (prefixWord ++ tailWord_5151683) baseStart_5151683 baseEnd_5151683 := by
    simpa [prefixWord, tailWord_5151683, baseEnd_5151683] using wordTrace_append hprefix tailTrace_5151683
  have hstable : (prefixWord ++ tailWord_5151683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151683).length < 2 ^ (prefixWord ++ tailWord_5151683).sum := by decide
  have hdescent : baseEnd_5151683 < baseStart_5151683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151763 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 6, 4]
def baseStart_5151763 : Nat := 118140960795 + 5151763 * 2 ^ 59
def prefixEnd_5151763 : Nat := 4983230072969 + 3 ^ 40 * 5151763 * 2
def baseEnd_5151763 : Nat := 881776879016277479089993

theorem tailTrace_5151763 : CollatzResearch.WordTrace tailWord_5151763 prefixEnd_5151763 881776879016277479089993 := by
  unfold tailWord_5151763
  simp only [CollatzResearch.WordTrace]
  refine ⟨187900233235049976916987943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125266822156699984611325295 187900233235049976916987943)
  ·
    refine ⟨281850349852574965375481915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187900233235049976916987943 281850349852574965375481915)
    ·
      refine ⟨422775524778862448063222873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281850349852574965375481915 422775524778862448063222873)
      ·
        refine ⟨317081643584146836047417155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422775524778862448063222873 317081643584146836047417155)
        ·
          refine ⟨475622465376220254071125733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317081643584146836047417155 475622465376220254071125733)
          ·
            refine ⟨89179212258041297638336075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475622465376220254071125733 89179212258041297638336075)
            ·
              refine ⟨133768818387061946457504113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89179212258041297638336075 133768818387061946457504113)
              ·
                refine ⟨100326613790296459843128085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133768818387061946457504113 100326613790296459843128085)
                ·
                  refine ⟨4702810021420146555146629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100326613790296459843128085 4702810021420146555146629)
                  ·
                    refine ⟨881776879016277479089993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702810021420146555146629 881776879016277479089993)
                    ·
                      rfl

theorem cell23_5151763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 4].length) (baseStart_5151763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151763 prefixEnd_5151763 := by exact prefixLift 5151763
  have htrace : WordTrace (prefixWord ++ tailWord_5151763) baseStart_5151763 baseEnd_5151763 := by
    simpa [prefixWord, tailWord_5151763, baseEnd_5151763] using wordTrace_append hprefix tailTrace_5151763
  have hstable : (prefixWord ++ tailWord_5151763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151763).length < 2 ^ (prefixWord ++ tailWord_5151763).sum := by decide
  have hdescent : baseEnd_5151763 < baseStart_5151763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151770 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_5151770 : Nat := 118140960795 + 5151770 * 2 ^ 59
def prefixEnd_5151770 : Nat := 4983230072969 + 3 ^ 40 * 5151770 * 2
def baseEnd_5151770 : Nat := 2645334231413413909882447

theorem tailTrace_5151770 : CollatzResearch.WordTrace tailWord_5151770 prefixEnd_5151770 2645334231413413909882447 := by
  unfold tailWord_5151770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46975122136506154278123191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125266992364016411408328509 46975122136506154278123191)
  ·
    refine ⟨70462683204759231417184787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46975122136506154278123191 70462683204759231417184787)
    ·
      refine ⟨105694024807138847125777181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70462683204759231417184787 105694024807138847125777181)
      ·
        refine ⟨39635259302677067672166443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105694024807138847125777181 39635259302677067672166443)
        ·
          refine ⟨59452888954015601508249665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39635259302677067672166443 59452888954015601508249665)
          ·
            refine ⟨44589666715511701131187249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59452888954015601508249665 44589666715511701131187249)
            ·
              refine ⟨33442250036633775848390437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44589666715511701131187249 33442250036633775848390437)
              ·
                refine ⟨6270421881868832971573207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33442250036633775848390437 6270421881868832971573207)
                ·
                  refine ⟨9405632822803249457359811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6270421881868832971573207 9405632822803249457359811)
                  ·
                    refine ⟨14108449234204874186039717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9405632822803249457359811 14108449234204874186039717)
                    ·
                      refine ⟨2645334231413413909882447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14108449234204874186039717 2645334231413413909882447)
                      ·
                        rfl

theorem cell23_5151770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_5151770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151770 prefixEnd_5151770 := by exact prefixLift 5151770
  have htrace : WordTrace (prefixWord ++ tailWord_5151770) baseStart_5151770 baseEnd_5151770 := by
    simpa [prefixWord, tailWord_5151770, baseEnd_5151770] using wordTrace_append hprefix tailTrace_5151770
  have hstable : (prefixWord ++ tailWord_5151770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151770).length < 2 ^ (prefixWord ++ tailWord_5151770).sum := by decide
  have hdescent : baseEnd_5151770 < baseStart_5151770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151780 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_5151780 : Nat := 118140960795 + 5151780 * 2 ^ 59
def prefixEnd_5151780 : Nat := 4983230072969 + 3 ^ 40 * 5151780 * 2
def baseEnd_5151780 : Nat := 881779788739986290252467

theorem tailTrace_5151780 : CollatzResearch.WordTrace tailWord_5151780 prefixEnd_5151780 881779788739986290252467 := by
  unfold tailWord_5151780
  simp only [CollatzResearch.WordTrace]
  refine ⟨93950426637994194410178397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125267235517325592546904529 93950426637994194410178397)
  ·
    refine ⟨35231409989247822903816899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93950426637994194410178397 35231409989247822903816899)
    ·
      refine ⟨52847114983871734355725349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35231409989247822903816899 52847114983871734355725349)
      ·
        refine ⟨9908834059475950191698503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52847114983871734355725349 9908834059475950191698503)
        ·
          refine ⟨14863251089213925287547755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908834059475950191698503 14863251089213925287547755)
          ·
            refine ⟨22294876633820887931321633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863251089213925287547755 22294876633820887931321633)
            ·
              refine ⟨16721157475365665948491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22294876633820887931321633 16721157475365665948491225)
              ·
                refine ⟨12540868106524249461368419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16721157475365665948491225 12540868106524249461368419)
                ·
                  refine ⟨18811302159786374192052629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540868106524249461368419 18811302159786374192052629)
                  ·
                    refine ⟨881779788739986290252467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18811302159786374192052629 881779788739986290252467)
                    ·
                      rfl

theorem cell23_5151780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_5151780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151780 prefixEnd_5151780 := by exact prefixLift 5151780
  have htrace : WordTrace (prefixWord ++ tailWord_5151780) baseStart_5151780 baseEnd_5151780 := by
    simpa [prefixWord, tailWord_5151780, baseEnd_5151780] using wordTrace_append hprefix tailTrace_5151780
  have hstable : (prefixWord ++ tailWord_5151780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151780).length < 2 ^ (prefixWord ++ tailWord_5151780).sum := by decide
  have hdescent : baseEnd_5151780 < baseStart_5151780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151790 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5151790 : Nat := 118140960795 + 5151790 * 2 ^ 59
def prefixEnd_5151790 : Nat := 4983230072969 + 3 ^ 40 * 5151790 * 2
def baseEnd_5151790 : Nat := 2645344501026503831632355

theorem tailTrace_5151790 : CollatzResearch.WordTrace tailWord_5151790 prefixEnd_5151790 2645344501026503831632355 := by
  unfold tailWord_5151790
  simp only [CollatzResearch.WordTrace]
  refine ⟨23487652250744020066027603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125267478670634773685480549 23487652250744020066027603)
  ·
    refine ⟨35231478376116030099041405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23487652250744020066027603 35231478376116030099041405)
    ·
      refine ⟨13211804391043511287140527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35231478376116030099041405 13211804391043511287140527)
      ·
        refine ⟨19817706586565266930710791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13211804391043511287140527 19817706586565266930710791)
        ·
          refine ⟨29726559879847900396066187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19817706586565266930710791 29726559879847900396066187)
          ·
            refine ⟨44589839819771850594099281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29726559879847900396066187 44589839819771850594099281)
            ·
              refine ⟨33442379864828887945574461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44589839819771850594099281 33442379864828887945574461)
              ·
                refine ⟨12540892449310832979590423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33442379864828887945574461 12540892449310832979590423)
                ·
                  refine ⟨18811338673966249469385635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540892449310832979590423 18811338673966249469385635)
                  ·
                    refine ⟨28217008010949374204078453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18811338673966249469385635 28217008010949374204078453)
                    ·
                      refine ⟨2645344501026503831632355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28217008010949374204078453 2645344501026503831632355)
                      ·
                        rfl

theorem cell23_5151790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5151790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151790 prefixEnd_5151790 := by exact prefixLift 5151790
  have htrace : WordTrace (prefixWord ++ tailWord_5151790) baseStart_5151790 baseEnd_5151790 := by
    simpa [prefixWord, tailWord_5151790, baseEnd_5151790] using wordTrace_append hprefix tailTrace_5151790
  have hstable : (prefixWord ++ tailWord_5151790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151790).length < 2 ^ (prefixWord ++ tailWord_5151790).sum := by decide
  have hdescent : baseEnd_5151790 < baseStart_5151790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151804 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_5151804 : Nat := 118140960795 + 5151804 * 2 ^ 59
def prefixEnd_5151804 : Nat := 4983230072969 + 3 ^ 40 * 5151804 * 2
def baseEnd_5151804 : Nat := 2645351689755666776857291

theorem tailTrace_5151804 : CollatzResearch.WordTrace tailWord_5151804 prefixEnd_5151804 2645351689755666776857291 := by
  unfold tailWord_5151804
  simp only [CollatzResearch.WordTrace]
  refine ⟨93950864313950720459615233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125267819085267627279486977 93950864313950720459615233)
  ·
    refine ⟨70463148235463040344711425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93950864313950720459615233 70463148235463040344711425)
    ·
      refine ⟨52847361176597280258533569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70463148235463040344711425 52847361176597280258533569)
      ·
        refine ⟨39635520882447960193900177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52847361176597280258533569 39635520882447960193900177)
        ·
          refine ⟨29726640661835970145425133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39635520882447960193900177 29726640661835970145425133)
          ·
            refine ⟨11147490248188488804534425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29726640661835970145425133 11147490248188488804534425)
            ·
              refine ⟨8360617686141366603400819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11147490248188488804534425 8360617686141366603400819)
              ·
                refine ⟨12540926529212049905101229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8360617686141366603400819 12540926529212049905101229)
                ·
                  refine ⟨4702847448454518714412961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12540926529212049905101229 4702847448454518714412961)
                  ·
                    refine ⟨3527135586340889035809721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4702847448454518714412961 3527135586340889035809721)
                    ·
                      refine ⟨2645351689755666776857291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527135586340889035809721 2645351689755666776857291)
                      ·
                        rfl

theorem cell23_5151804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_5151804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151804 prefixEnd_5151804 := by exact prefixLift 5151804
  have htrace : WordTrace (prefixWord ++ tailWord_5151804) baseStart_5151804 baseEnd_5151804 := by
    simpa [prefixWord, tailWord_5151804, baseEnd_5151804] using wordTrace_append hprefix tailTrace_5151804
  have hstable : (prefixWord ++ tailWord_5151804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151804).length < 2 ^ (prefixWord ++ tailWord_5151804).sum := by decide
  have hdescent : baseEnd_5151804 < baseStart_5151804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151814 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5151814 : Nat := 118140960795 + 5151814 * 2 ^ 59
def prefixEnd_5151814 : Nat := 4983230072969 + 3 ^ 40 * 5151814 * 2
def baseEnd_5151814 : Nat := 881785608187403912577415

theorem tailTrace_5151814 : CollatzResearch.WordTrace tailWord_5151814 prefixEnd_5151814 881785608187403912577415 := by
  unfold tailWord_5151814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871940417433287894596703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125268062238576808418062997 5871940417433287894596703)
  ·
    refine ⟨8807910626149931841895055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5871940417433287894596703 8807910626149931841895055)
    ·
      refine ⟨13211865939224897762842583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807910626149931841895055 13211865939224897762842583)
      ·
        refine ⟨19817798908837346644263875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13211865939224897762842583 19817798908837346644263875)
        ·
          refine ⟨29726698363256019966395813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19817798908837346644263875 29726698363256019966395813)
          ·
            refine ⟨5573755943110503743699215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29726698363256019966395813 5573755943110503743699215)
            ·
              refine ⟨8360633914665755615548823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573755943110503743699215 8360633914665755615548823)
              ·
                refine ⟨12540950871998633423323235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8360633914665755615548823 12540950871998633423323235)
                ·
                  refine ⟨18811426307997950134984853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540950871998633423323235 18811426307997950134984853)
                  ·
                    refine ⟨881785608187403912577415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18811426307997950134984853 881785608187403912577415)
                    ·
                      rfl

theorem cell23_5151814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5151814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151814 prefixEnd_5151814 := by exact prefixLift 5151814
  have htrace : WordTrace (prefixWord ++ tailWord_5151814) baseStart_5151814 baseEnd_5151814 := by
    simpa [prefixWord, tailWord_5151814, baseEnd_5151814] using wordTrace_append hprefix tailTrace_5151814
  have hstable : (prefixWord ++ tailWord_5151814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151814).length < 2 ^ (prefixWord ++ tailWord_5151814).sum := by decide
  have hdescent : baseEnd_5151814 < baseStart_5151814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151843 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5151843 : Nat := 118140960795 + 5151843 * 2 ^ 59
def prefixEnd_5151843 : Nat := 4983230072969 + 3 ^ 40 * 5151843 * 2
def baseEnd_5151843 : Nat := 2645371715501192124269611

theorem tailTrace_5151843 : CollatzResearch.WordTrace tailWord_5151843 prefixEnd_5151843 2645371715501192124269611 := by
  unfold tailWord_5151843
  simp only [CollatzResearch.WordTrace]
  refine ⟨187903151074760150579900183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125268767383173433719933455 187903151074760150579900183)
  ·
    refine ⟨281854726612140225869850275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187903151074760150579900183 281854726612140225869850275)
    ·
      refine ⟨422782089918210338804775413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281854726612140225869850275 422782089918210338804775413)
      ·
        refine ⟨39635820929832219262947695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422782089918210338804775413 39635820929832219262947695)
        ·
          refine ⟨59453731394748328894421543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39635820929832219262947695 59453731394748328894421543)
          ·
            refine ⟨89180597092122493341632315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59453731394748328894421543 89180597092122493341632315)
            ·
              refine ⟨133770895638183740012448473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89180597092122493341632315 133770895638183740012448473)
              ·
                refine ⟨100328171728637805009336355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133770895638183740012448473 100328171728637805009336355)
                ·
                  refine ⟨150492257592956707514004533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100328171728637805009336355 150492257592956707514004533)
                  ·
                    refine ⟨14108649149339691329437925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150492257592956707514004533 14108649149339691329437925)
                    ·
                      refine ⟨2645371715501192124269611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14108649149339691329437925 2645371715501192124269611)
                      ·
                        rfl

theorem cell23_5151843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5151843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151843 prefixEnd_5151843 := by exact prefixLift 5151843
  have htrace : WordTrace (prefixWord ++ tailWord_5151843) baseStart_5151843 baseEnd_5151843 := by
    simpa [prefixWord, tailWord_5151843, baseEnd_5151843] using wordTrace_append hprefix tailTrace_5151843
  have hstable : (prefixWord ++ tailWord_5151843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151843).length < 2 ^ (prefixWord ++ tailWord_5151843).sum := by decide
  have hdescent : baseEnd_5151843 < baseStart_5151843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151863 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_5151863 : Nat := 118140960795 + 5151863 * 2 ^ 59
def prefixEnd_5151863 : Nat := 4983230072969 + 3 ^ 40 * 5151863 * 2
def baseEnd_5151863 : Nat := 2645381985114282046019519

theorem tailTrace_5151863 : CollatzResearch.WordTrace tailWord_5151863 prefixEnd_5151863 2645381985114282046019519 := by
  unfold tailWord_5151863
  simp only [CollatzResearch.WordTrace]
  refine ⟨187903880534687693995628243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125269253689791795997085495 187903880534687693995628243)
  ·
    refine ⟨281855820802031540993442365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187903880534687693995628243 281855820802031540993442365)
    ·
      refine ⟨105695932800761827872540887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281855820802031540993442365 105695932800761827872540887)
      ·
        refine ⟨158543899201142741808811331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105695932800761827872540887 158543899201142741808811331)
        ·
          refine ⟨237815848801714112713216997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158543899201142741808811331 237815848801714112713216997)
          ·
            refine ⟨44590471650321396133728187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237815848801714112713216997 44590471650321396133728187)
            ·
              refine ⟨66885707475482094200592281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44590471650321396133728187 66885707475482094200592281)
              ·
                refine ⟨50164280606611570650444211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66885707475482094200592281 50164280606611570650444211)
                ·
                  refine ⟨75246420909917355975666317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50164280606611570650444211 75246420909917355975666317)
                  ·
                    refine ⟨28217407841219008490874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75246420909917355975666317 28217407841219008490874869)
                    ·
                      refine ⟨2645381985114282046019519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28217407841219008490874869 2645381985114282046019519)
                      ·
                        rfl

theorem cell23_5151863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_5151863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151863 prefixEnd_5151863 := by exact prefixLift 5151863
  have htrace : WordTrace (prefixWord ++ tailWord_5151863) baseStart_5151863 baseEnd_5151863 := by
    simpa [prefixWord, tailWord_5151863, baseEnd_5151863] using wordTrace_append hprefix tailTrace_5151863
  have hstable : (prefixWord ++ tailWord_5151863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151863).length < 2 ^ (prefixWord ++ tailWord_5151863).sum := by decide
  have hdescent : baseEnd_5151863 < baseStart_5151863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151883 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 7]
def baseStart_5151883 : Nat := 118140960795 + 5151883 * 2 ^ 59
def prefixEnd_5151883 : Nat := 4983230072969 + 3 ^ 40 * 5151883 * 2
def baseEnd_5151883 : Nat := 293932472747485774196603

theorem tailTrace_5151883 : CollatzResearch.WordTrace tailWord_5151883 prefixEnd_5151883 293932472747485774196603 := by
  unfold tailWord_5151883
  simp only [CollatzResearch.WordTrace]
  refine ⟨187904609994615237411356303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125269739996410158274237535 187904609994615237411356303)
  ·
    refine ⟨281856914991922856117034455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187904609994615237411356303 281856914991922856117034455)
    ·
      refine ⟨422785372487884284175551683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281856914991922856117034455 422785372487884284175551683)
      ·
        refine ⟨634178058731826426263327525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422785372487884284175551683 634178058731826426263327525)
        ·
          refine ⟨118908386012217454924373911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 634178058731826426263327525 118908386012217454924373911)
          ·
            refine ⟨178362579018326182386560867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118908386012217454924373911 178362579018326182386560867)
            ·
              refine ⟨267543868527489273579841301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178362579018326182386560867 267543868527489273579841301)
              ·
                refine ⟨12541118837226059699055061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267543868527489273579841301 12541118837226059699055061)
                ·
                  refine ⟨293932472747485774196603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12541118837226059699055061 293932472747485774196603)
                  ·
                    rfl

theorem cell23_5151883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 7].length) (baseStart_5151883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151883 prefixEnd_5151883 := by exact prefixLift 5151883
  have htrace : WordTrace (prefixWord ++ tailWord_5151883) baseStart_5151883 baseEnd_5151883 := by
    simpa [prefixWord, tailWord_5151883, baseEnd_5151883] using wordTrace_append hprefix tailTrace_5151883
  have hstable : (prefixWord ++ tailWord_5151883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151883).length < 2 ^ (prefixWord ++ tailWord_5151883).sum := by decide
  have hdescent : baseEnd_5151883 < baseStart_5151883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_5151893 : Nat := 118140960795 + 5151893 * 2 ^ 59
def prefixEnd_5151893 : Nat := 4983230072969 + 3 ^ 40 * 5151893 * 2
def baseEnd_5151893 : Nat := 2645397389533916928644381

theorem tailTrace_5151893 : CollatzResearch.WordTrace tailWord_5151893 prefixEnd_5151893 2645397389533916928644381 := by
  unfold tailWord_5151893
  simp only [CollatzResearch.WordTrace]
  refine ⟨187904974724579009119220333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125269983149719339412813555 187904974724579009119220333)
  ·
    refine ⟨70464365521717128419707625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187904974724579009119220333 70464365521717128419707625)
    ·
      refine ⟨52848274141287846314780719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70464365521717128419707625 52848274141287846314780719)
      ·
        refine ⟨79272411211931769472171079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52848274141287846314780719 79272411211931769472171079)
        ·
          refine ⟨118908616817897654208256619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79272411211931769472171079 118908616817897654208256619)
          ·
            refine ⟨178362925226846481312384929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118908616817897654208256619 178362925226846481312384929)
            ·
              refine ⟨133772193920134860984288697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178362925226846481312384929 133772193920134860984288697)
              ·
                refine ⟨100329145440101145738216523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133772193920134860984288697 100329145440101145738216523)
                ·
                  refine ⟨150493718160151718607324785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100329145440101145738216523 150493718160151718607324785)
                  ·
                    refine ⟨112870288620113788955493589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150493718160151718607324785 112870288620113788955493589)
                    ·
                      refine ⟨2645397389533916928644381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112870288620113788955493589 2645397389533916928644381)
                      ·
                        rfl

theorem cell23_5151893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_5151893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151893 prefixEnd_5151893 := by exact prefixLift 5151893
  have htrace : WordTrace (prefixWord ++ tailWord_5151893) baseStart_5151893 baseEnd_5151893 := by
    simpa [prefixWord, tailWord_5151893, baseEnd_5151893] using wordTrace_append hprefix tailTrace_5151893
  have hstable : (prefixWord ++ tailWord_5151893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151893).length < 2 ^ (prefixWord ++ tailWord_5151893).sum := by decide
  have hdescent : baseEnd_5151893 < baseStart_5151893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151911 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5151911 : Nat := 118140960795 + 5151911 * 2 ^ 59
def prefixEnd_5151911 : Nat := 4983230072969 + 3 ^ 40 * 5151911 * 2
def baseEnd_5151911 : Nat := 2645406632185697858219299

theorem tailTrace_5151911 : CollatzResearch.WordTrace tailWord_5151911 prefixEnd_5151911 2645406632185697858219299 := by
  unfold tailWord_5151911
  simp only [CollatzResearch.WordTrace]
  refine ⟨187905631238513798193375587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125270420825675865462250391 187905631238513798193375587)
  ·
    refine ⟨281858446857770697290063381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187905631238513798193375587 281858446857770697290063381)
    ·
      refine ⟨13212114696458001435471721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 281858446857770697290063381 13212114696458001435471721)
      ·
        refine ⟨9909086022343501076603791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13212114696458001435471721 9909086022343501076603791)
        ·
          refine ⟨14863629033515251614905687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909086022343501076603791 14863629033515251614905687)
          ·
            refine ⟨22295443550272877422358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863629033515251614905687 22295443550272877422358531)
            ·
              refine ⟨33443165325409316133537797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22295443550272877422358531 33443165325409316133537797)
              ·
                refine ⟨6270593498514246775038337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33443165325409316133537797 6270593498514246775038337)
                ·
                  refine ⟨4702945123885685081278753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270593498514246775038337 4702945123885685081278753)
                  ·
                    refine ⟨3527208842914263810959065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4702945123885685081278753 3527208842914263810959065)
                    ·
                      refine ⟨2645406632185697858219299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527208842914263810959065 2645406632185697858219299)
                      ·
                        rfl

theorem cell23_5151911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5151911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151911 prefixEnd_5151911 := by exact prefixLift 5151911
  have htrace : WordTrace (prefixWord ++ tailWord_5151911) baseStart_5151911 baseEnd_5151911 := by
    simpa [prefixWord, tailWord_5151911, baseEnd_5151911] using wordTrace_append hprefix tailTrace_5151911
  have hstable : (prefixWord ++ tailWord_5151911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151911).length < 2 ^ (prefixWord ++ tailWord_5151911).sum := by decide
  have hdescent : baseEnd_5151911 < baseStart_5151911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5151967 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 4, 2]
def baseStart_5151967 : Nat := 118140960795 + 5151967 * 2 ^ 59
def prefixEnd_5151967 : Nat := 4983230072969 + 3 ^ 40 * 5151967 * 2
def baseEnd_5151967 : Nat := 2645435387102349639119041

theorem tailTrace_5151967 : CollatzResearch.WordTrace tailWord_5151967 prefixEnd_5151967 2645435387102349639119041 := by
  unfold tailWord_5151967
  simp only [CollatzResearch.WordTrace]
  refine ⟨187907673726310919757414155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125271782484207279838276103 187907673726310919757414155)
  ·
    refine ⟨281861510589466379636121233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187907673726310919757414155 281861510589466379636121233)
    ·
      refine ⟨211396132942099784727090925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281861510589466379636121233 211396132942099784727090925)
      ·
        refine ⟨79273549853287419272659097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211396132942099784727090925 79273549853287419272659097)
        ·
          refine ⟨59455162389965564454494323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79273549853287419272659097 59455162389965564454494323)
          ·
            refine ⟨89182743584948346681741485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59455162389965564454494323 89182743584948346681741485)
            ·
              refine ⟨33443528844355630005653057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89182743584948346681741485 33443528844355630005653057)
              ·
                refine ⟨25082646633266722504239793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33443528844355630005653057 25082646633266722504239793)
                ·
                  refine ⟨18811984974950041878179845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25082646633266722504239793 18811984974950041878179845)
                  ·
                    refine ⟨3527247182803132852158721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18811984974950041878179845 3527247182803132852158721)
                    ·
                      refine ⟨2645435387102349639119041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527247182803132852158721 2645435387102349639119041)
                      ·
                        rfl

theorem cell23_5151967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_5151967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5151967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5151967 prefixEnd_5151967 := by exact prefixLift 5151967
  have htrace : WordTrace (prefixWord ++ tailWord_5151967) baseStart_5151967 baseEnd_5151967 := by
    simpa [prefixWord, tailWord_5151967, baseEnd_5151967] using wordTrace_append hprefix tailTrace_5151967
  have hstable : (prefixWord ++ tailWord_5151967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5151967).length < 2 ^ (prefixWord ++ tailWord_5151967).sum := by decide
  have hdescent : baseEnd_5151967 < baseStart_5151967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5151967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152000 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_5152000 : Nat := 118140960795 + 5152000 * 2 ^ 59
def prefixEnd_5152000 : Nat := 4983230072969 + 3 ^ 40 * 5152000 * 2
def baseEnd_5152000 : Nat := 2645452331963948010006389

theorem tailTrace_5152000 : CollatzResearch.WordTrace tailWord_5152000 prefixEnd_5152000 2645452331963948010006389 := by
  unfold tailWord_5152000
  simp only [CollatzResearch.WordTrace]
  refine ⟨93954438667595683196682727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125272584890127577595576969 93954438667595683196682727)
  ·
    refine ⟨140931658001393524795024091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93954438667595683196682727 140931658001393524795024091)
    ·
      refine ⟨211397487002090287192536137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140931658001393524795024091 211397487002090287192536137)
      ·
        refine ⟨158548115251567715394402103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211397487002090287192536137 158548115251567715394402103)
        ·
          refine ⟨237822172877351573091603155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158548115251567715394402103 237822172877351573091603155)
          ·
            refine ⟨356733259316027359637404733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237822172877351573091603155 356733259316027359637404733)
            ·
              refine ⟨133774972243510259864026775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356733259316027359637404733 133774972243510259864026775)
              ·
                refine ⟨200662458365265389796040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133774972243510259864026775 200662458365265389796040163)
                ·
                  refine ⟨300993687547898084694060245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200662458365265389796040163 300993687547898084694060245)
                  ·
                    refine ⟨7054539551903861360017037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 300993687547898084694060245 7054539551903861360017037)
                    ·
                      refine ⟨2645452331963948010006389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054539551903861360017037 2645452331963948010006389)
                      ·
                        rfl

theorem cell23_5152000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_5152000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152000 prefixEnd_5152000 := by exact prefixLift 5152000
  have htrace : WordTrace (prefixWord ++ tailWord_5152000) baseStart_5152000 baseEnd_5152000 := by
    simpa [prefixWord, tailWord_5152000, baseEnd_5152000] using wordTrace_append hprefix tailTrace_5152000
  have hstable : (prefixWord ++ tailWord_5152000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152000).length < 2 ^ (prefixWord ++ tailWord_5152000).sum := by decide
  have hdescent : baseEnd_5152000 < baseStart_5152000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152011 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 1, 4]
def baseStart_5152011 : Nat := 118140960795 + 5152011 * 2 ^ 59
def prefixEnd_5152011 : Nat := 4983230072969 + 3 ^ 40 * 5152011 * 2
def baseEnd_5152011 : Nat := 881819326750382488989613

theorem tailTrace_5152011 : CollatzResearch.WordTrace tailWord_5152011 prefixEnd_5152011 881819326750382488989613 := by
  unfold tailWord_5152011
  simp only [CollatzResearch.WordTrace]
  refine ⟨187909278538151515272015887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125272852358767676848010591 187909278538151515272015887)
  ·
    refine ⟨281863917807227272908023831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187909278538151515272015887 281863917807227272908023831)
    ·
      refine ⟨422795876710840909362035747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281863917807227272908023831 422795876710840909362035747)
      ·
        refine ⟨634193815066261364043053621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422795876710840909362035747 634193815066261364043053621)
        ·
          refine ⟨59455670162462002879036277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 634193815066261364043053621 59455670162462002879036277)
          ·
            refine ⟨5573969077730812769909651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59455670162462002879036277 5573969077730812769909651)
            ·
              refine ⟨8360953616596219154864477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573969077730812769909651 8360953616596219154864477)
              ·
                refine ⟨3135357606223582183074179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8360953616596219154864477 3135357606223582183074179)
                ·
                  refine ⟨4703036409335373274611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135357606223582183074179 4703036409335373274611269)
                  ·
                    refine ⟨881819326750382488989613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703036409335373274611269 881819326750382488989613)
                    ·
                      rfl

theorem cell23_5152011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 4].length) (baseStart_5152011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152011 prefixEnd_5152011 := by exact prefixLift 5152011
  have htrace : WordTrace (prefixWord ++ tailWord_5152011) baseStart_5152011 baseEnd_5152011 := by
    simpa [prefixWord, tailWord_5152011, baseEnd_5152011] using wordTrace_append hprefix tailTrace_5152011
  have hstable : (prefixWord ++ tailWord_5152011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152011).length < 2 ^ (prefixWord ++ tailWord_5152011).sum := by decide
  have hdescent : baseEnd_5152011 < baseStart_5152011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152085 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5152085 : Nat := 118140960795 + 5152085 * 2 ^ 59
def prefixEnd_5152085 : Nat := 4983230072969 + 3 ^ 40 * 5152085 * 2
def baseEnd_5152085 : Nat := 2645495977819580177443499

theorem tailTrace_5152085 : CollatzResearch.WordTrace tailWord_5152085 prefixEnd_5152085 2645495977819580177443499 := by
  unfold tailWord_5152085
  simp only [CollatzResearch.WordTrace]
  refine ⟨187911977539883425910209709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125274651693255617273473139 187911977539883425910209709)
  ·
    refine ⟨70466991577456284716328641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187911977539883425910209709 70466991577456284716328641)
    ·
      refine ⟨52850243683092213537246481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70466991577456284716328641 52850243683092213537246481)
      ·
        refine ⟨39637682762319160152934861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52850243683092213537246481 39637682762319160152934861)
        ·
          refine ⟨14864131035869685057350573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39637682762319160152934861 14864131035869685057350573)
          ·
            refine ⟨5574049138451131896506465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14864131035869685057350573 5574049138451131896506465)
            ·
              refine ⟨4180536853838348922379849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574049138451131896506465 4180536853838348922379849)
              ·
                refine ⟨3135402640378761691784887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4180536853838348922379849 3135402640378761691784887)
                ·
                  refine ⟨4703103960568142537677331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135402640378761691784887 4703103960568142537677331)
                  ·
                    refine ⟨7054655940852213806515997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703103960568142537677331 7054655940852213806515997)
                    ·
                      refine ⟨2645495977819580177443499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054655940852213806515997 2645495977819580177443499)
                      ·
                        rfl

theorem cell23_5152085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5152085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152085 prefixEnd_5152085 := by exact prefixLift 5152085
  have htrace : WordTrace (prefixWord ++ tailWord_5152085) baseStart_5152085 baseEnd_5152085 := by
    simpa [prefixWord, tailWord_5152085, baseEnd_5152085] using wordTrace_append hprefix tailTrace_5152085
  have hstable : (prefixWord ++ tailWord_5152085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152085).length < 2 ^ (prefixWord ++ tailWord_5152085).sum := by decide
  have hdescent : baseEnd_5152085 < baseStart_5152085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152124 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_5152124 : Nat := 118140960795 + 5152124 * 2 ^ 59
def prefixEnd_5152124 : Nat := 4983230072969 + 3 ^ 40 * 5152124 * 2
def baseEnd_5152124 : Nat := 2645516003565105524855819

theorem tailTrace_5152124 : CollatzResearch.WordTrace tailWord_5152124 prefixEnd_5152124 2645516003565105524855819 := by
  unfold tailWord_5152124
  simp only [CollatzResearch.WordTrace]
  refine ⟨93956699993371067785439713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125275599991161423713919617 93956699993371067785439713)
  ·
    refine ⟨70467524995028300839079785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93956699993371067785439713 70467524995028300839079785)
    ·
      refine ⟨52850643746271225629309839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70467524995028300839079785 52850643746271225629309839)
      ·
        refine ⟨79275965619406838443964759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52850643746271225629309839 79275965619406838443964759)
        ·
          refine ⟨118913948429110257665947139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79275965619406838443964759 118913948429110257665947139)
          ·
            refine ⟨178370922643665386498920709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118913948429110257665947139 178370922643665386498920709)
            ·
              refine ⟨33444547995687259968547633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178370922643665386498920709 33444547995687259968547633)
              ·
                refine ⟨25083410996765444976410725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33444547995687259968547633 25083410996765444976410725)
                ·
                  refine ⟨4703139561893520933077011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25083410996765444976410725 4703139561893520933077011)
                  ·
                    refine ⟨7054709342840281399615517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703139561893520933077011 7054709342840281399615517)
                    ·
                      refine ⟨2645516003565105524855819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054709342840281399615517 2645516003565105524855819)
                      ·
                        rfl

theorem cell23_5152124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_5152124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152124 prefixEnd_5152124 := by exact prefixLift 5152124
  have htrace : WordTrace (prefixWord ++ tailWord_5152124) baseStart_5152124 baseEnd_5152124 := by
    simpa [prefixWord, tailWord_5152124, baseEnd_5152124] using wordTrace_append hprefix tailTrace_5152124
  have hstable : (prefixWord ++ tailWord_5152124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152124).length < 2 ^ (prefixWord ++ tailWord_5152124).sum := by decide
  have hdescent : baseEnd_5152124 < baseStart_5152124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152204 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 7]
def baseStart_5152204 : Nat := 118140960795 + 5152204 * 2 ^ 59
def prefixEnd_5152204 : Nat := 4983230072969 + 3 ^ 40 * 5152204 * 2
def baseEnd_5152204 : Nat := 293950786890829467983939

theorem tailTrace_5152204 : CollatzResearch.WordTrace tailWord_5152204 prefixEnd_5152204 293950786890829467983939 := by
  unfold tailWord_5152204
  simp only [CollatzResearch.WordTrace]
  refine ⟨93958158913226154616895833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125277545217634872822527777 93958158913226154616895833)
  ·
    refine ⟨70468619184919615962671875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93958158913226154616895833 70468619184919615962671875)
    ·
      refine ⟨105702928777379423944007813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70468619184919615962671875 105702928777379423944007813)
      ·
        refine ⟨19819299145758641989501465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105702928777379423944007813 19819299145758641989501465)
        ·
          refine ⟨14864474359318981492126099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19819299145758641989501465 14864474359318981492126099)
          ·
            refine ⟨22296711538978472238189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14864474359318981492126099 22296711538978472238189149)
            ·
              refine ⟨8361266827116927089320931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22296711538978472238189149 8361266827116927089320931)
              ·
                refine ⟨12541900240675390633981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361266827116927089320931 12541900240675390633981397)
                ·
                  refine ⟨293950786890829467983939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12541900240675390633981397 293950786890829467983939)
                  ·
                    rfl

theorem cell23_5152204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_5152204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152204 prefixEnd_5152204 := by exact prefixLift 5152204
  have htrace : WordTrace (prefixWord ++ tailWord_5152204) baseStart_5152204 baseEnd_5152204 := by
    simpa [prefixWord, tailWord_5152204, baseEnd_5152204] using wordTrace_append hprefix tailTrace_5152204
  have hstable : (prefixWord ++ tailWord_5152204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152204).length < 2 ^ (prefixWord ++ tailWord_5152204).sum := by decide
  have hdescent : baseEnd_5152204 < baseStart_5152204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152224 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2]
def baseStart_5152224 : Nat := 118140960795 + 5152224 * 2 ^ 59
def prefixEnd_5152224 : Nat := 4983230072969 + 3 ^ 40 * 5152224 * 2
def baseEnd_5152224 : Nat := 2645567351630555133605359

theorem tailTrace_5152224 : CollatzResearch.WordTrace tailWord_5152224 prefixEnd_5152224 2645567351630555133605359 := by
  unfold tailWord_5152224
  simp only [CollatzResearch.WordTrace]
  refine ⟨93958523643189926324759863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125278031524253235099679817 93958523643189926324759863)
  ·
    refine ⟨140937785464784889487139795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93958523643189926324759863 140937785464784889487139795)
    ·
      refine ⟨211406678197177334230709693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140937785464784889487139795 211406678197177334230709693)
      ·
        refine ⟨79277504323941500336516135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211406678197177334230709693 79277504323941500336516135)
        ·
          refine ⟨118916256485912250504774203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79277504323941500336516135 118916256485912250504774203)
          ·
            refine ⟨178374384728868375757161305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118916256485912250504774203 178374384728868375757161305)
            ·
              refine ⟨133780788546651281817870979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178374384728868375757161305 133780788546651281817870979)
              ·
                refine ⟨200671182819976922726806469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133780788546651281817870979 200671182819976922726806469)
                ·
                  refine ⟨37625846778745673011276213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200671182819976922726806469 37625846778745673011276213)
                  ·
                    refine ⟨3527423135507406844807145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37625846778745673011276213 3527423135507406844807145)
                    ·
                      refine ⟨2645567351630555133605359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527423135507406844807145 2645567351630555133605359)
                      ·
                        rfl

theorem cell23_5152224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_5152224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152224 prefixEnd_5152224 := by exact prefixLift 5152224
  have htrace : WordTrace (prefixWord ++ tailWord_5152224) baseStart_5152224 baseEnd_5152224 := by
    simpa [prefixWord, tailWord_5152224, baseEnd_5152224] using wordTrace_append hprefix tailTrace_5152224
  have hstable : (prefixWord ++ tailWord_5152224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152224).length < 2 ^ (prefixWord ++ tailWord_5152224).sum := by decide
  have hdescent : baseEnd_5152224 < baseStart_5152224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152258 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5152258 : Nat := 118140960795 + 5152258 * 2 ^ 59
def prefixEnd_5152258 : Nat := 4983230072969 + 3 ^ 40 * 5152258 * 2
def baseEnd_5152258 : Nat := 2645584809972808000580203

theorem tailTrace_5152258 : CollatzResearch.WordTrace tailWord_5152258 prefixEnd_5152258 2645584809972808000580203 := by
  unfold tailWord_5152258
  simp only [CollatzResearch.WordTrace]
  refine ⟨46979571842064169114064357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125278858245504450970838285 46979571842064169114064357)
  ·
    refine ⟨8808669720387031708887067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46979571842064169114064357 8808669720387031708887067)
    ·
      refine ⟨13213004580580547563330601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8808669720387031708887067 13213004580580547563330601)
      ·
        refine ⟨9909753435435410672497951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13213004580580547563330601 9909753435435410672497951)
        ·
          refine ⟨14864630153153116008746927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909753435435410672497951 14864630153153116008746927)
          ·
            refine ⟨22296945229729674013120391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14864630153153116008746927 22296945229729674013120391)
            ·
              refine ⟨33445417844594511019680587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22296945229729674013120391 33445417844594511019680587)
              ·
                refine ⟨50168126766891766529520881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33445417844594511019680587 50168126766891766529520881)
                ·
                  refine ⟨37626095075168824897140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50168126766891766529520881 37626095075168824897140661)
                  ·
                    refine ⟨3527446413297077334106937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37626095075168824897140661 3527446413297077334106937)
                    ·
                      refine ⟨2645584809972808000580203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527446413297077334106937 2645584809972808000580203)
                      ·
                        rfl

theorem cell23_5152258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5152258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152258 prefixEnd_5152258 := by exact prefixLift 5152258
  have htrace : WordTrace (prefixWord ++ tailWord_5152258) baseStart_5152258 baseEnd_5152258 := by
    simpa [prefixWord, tailWord_5152258, baseEnd_5152258] using wordTrace_append hprefix tailTrace_5152258
  have hstable : (prefixWord ++ tailWord_5152258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152258).length < 2 ^ (prefixWord ++ tailWord_5152258).sum := by decide
  have hdescent : baseEnd_5152258 < baseStart_5152258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152288 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5152288 : Nat := 118140960795 + 5152288 * 2 ^ 59
def prefixEnd_5152288 : Nat := 4983230072969 + 3 ^ 40 * 5152288 * 2
def baseEnd_5152288 : Nat := 2645600214392442883205065

theorem tailTrace_5152288 : CollatzResearch.WordTrace tailWord_5152288 prefixEnd_5152288 2645600214392442883205065 := by
  unfold tailWord_5152288
  simp only [CollatzResearch.WordTrace]
  refine ⟨93959690779073995789924759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125279587705431994386566345 93959690779073995789924759)
  ·
    refine ⟨140939536168610993684887139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93959690779073995789924759 140939536168610993684887139)
    ·
      refine ⟨211409304252916490527330709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140939536168610993684887139 211409304252916490527330709)
      ·
        refine ⟨9909811136855460493468627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211409304252916490527330709 9909811136855460493468627)
        ·
          refine ⟨14864716705283190740202941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909811136855460493468627 14864716705283190740202941)
          ·
            refine ⟨5574268764481196527576103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14864716705283190740202941 5574268764481196527576103)
            ·
              refine ⟨8361403146721794791364155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574268764481196527576103 8361403146721794791364155)
              ·
                refine ⟨12542104720082692187046233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361403146721794791364155 12542104720082692187046233)
                ·
                  refine ⟨9406578540062019140284675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542104720082692187046233 9406578540062019140284675)
                  ·
                    refine ⟨14109867810093028710427013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9406578540062019140284675 14109867810093028710427013)
                    ·
                      refine ⟨2645600214392442883205065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14109867810093028710427013 2645600214392442883205065)
                      ·
                        rfl

theorem cell23_5152288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5152288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152288 prefixEnd_5152288 := by exact prefixLift 5152288
  have htrace : WordTrace (prefixWord ++ tailWord_5152288) baseStart_5152288 baseEnd_5152288 := by
    simpa [prefixWord, tailWord_5152288, baseEnd_5152288] using wordTrace_append hprefix tailTrace_5152288
  have hstable : (prefixWord ++ tailWord_5152288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152288).length < 2 ^ (prefixWord ++ tailWord_5152288).sum := by decide
  have hdescent : baseEnd_5152288 < baseStart_5152288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152291 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3]
def baseStart_5152291 : Nat := 118140960795 + 5152291 * 2 ^ 59
def prefixEnd_5152291 : Nat := 4983230072969 + 3 ^ 40 * 5152291 * 2
def baseEnd_5152291 : Nat := 2645601754834406371467551

theorem tailTrace_5152291 : CollatzResearch.WordTrace tailWord_5152291 prefixEnd_5152291 2645601754834406371467551 := by
  unfold tailWord_5152291
  simp only [CollatzResearch.WordTrace]
  refine ⟨187919490977137123092208727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125279660651424748728139151 187919490977137123092208727)
  ·
    refine ⟨281879236465705684638313091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187919490977137123092208727 281879236465705684638313091)
    ·
      refine ⟨422818854698558526957469637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281879236465705684638313091 422818854698558526957469637)
      ·
        refine ⟨79278535255979723804525557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422818854698558526957469637 79278535255979723804525557)
        ·
          refine ⟨7432362680248099106674271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79278535255979723804525557 7432362680248099106674271)
          ·
            refine ⟨11148544020372148660011407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432362680248099106674271 11148544020372148660011407)
            ·
              refine ⟨16722816030558222990017111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148544020372148660011407 16722816030558222990017111)
              ·
                refine ⟨25084224045837334485025667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16722816030558222990017111 25084224045837334485025667)
                ·
                  refine ⟨37626336068756001727538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25084224045837334485025667 37626336068756001727538501)
                  ·
                    refine ⟨7054938012891750323913469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37626336068756001727538501 7054938012891750323913469)
                    ·
                      refine ⟨2645601754834406371467551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7054938012891750323913469 2645601754834406371467551)
                      ·
                        rfl

theorem cell23_5152291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_5152291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152291 prefixEnd_5152291 := by exact prefixLift 5152291
  have htrace : WordTrace (prefixWord ++ tailWord_5152291) baseStart_5152291 baseEnd_5152291 := by
    simpa [prefixWord, tailWord_5152291, baseEnd_5152291] using wordTrace_append hprefix tailTrace_5152291
  have hstable : (prefixWord ++ tailWord_5152291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152291).length < 2 ^ (prefixWord ++ tailWord_5152291).sum := by decide
  have hdescent : baseEnd_5152291 < baseStart_5152291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152311 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 6]
def baseStart_5152311 : Nat := 118140960795 + 5152311 * 2 ^ 59
def prefixEnd_5152311 : Nat := 4983230072969 + 3 ^ 40 * 5152311 * 2
def baseEnd_5152311 : Nat := 293956891605277365913051

theorem tailTrace_5152311 : CollatzResearch.WordTrace tailWord_5152311 prefixEnd_5152311 293956891605277365913051 := by
  unfold tailWord_5152311
  simp only [CollatzResearch.WordTrace]
  refine ⟨187920220437064666507936787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125280146958043111005291191 187920220437064666507936787)
  ·
    refine ⟨281880330655596999761905181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187920220437064666507936787 281880330655596999761905181)
    ·
      refine ⟨105705123995848874910714443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281880330655596999761905181 105705123995848874910714443)
      ·
        refine ⟨158557685993773312366071665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105705123995848874910714443 158557685993773312366071665)
        ·
          refine ⟨118918264495329984274553749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158557685993773312366071665 118918264495329984274553749)
          ·
            refine ⟨5574293648218593012869707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118918264495329984274553749 5574293648218593012869707)
            ·
              refine ⟨8361440472327889519304561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574293648218593012869707 8361440472327889519304561)
              ·
                refine ⟨6271080354245917139478421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8361440472327889519304561 6271080354245917139478421)
                ·
                  refine ⟨293956891605277365913051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6271080354245917139478421 293956891605277365913051)
                  ·
                    rfl

theorem cell23_5152311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 6].length) (baseStart_5152311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152311 prefixEnd_5152311 := by exact prefixLift 5152311
  have htrace : WordTrace (prefixWord ++ tailWord_5152311) baseStart_5152311 baseEnd_5152311 := by
    simpa [prefixWord, tailWord_5152311, baseEnd_5152311] using wordTrace_append hprefix tailTrace_5152311
  have hstable : (prefixWord ++ tailWord_5152311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152311).length < 2 ^ (prefixWord ++ tailWord_5152311).sum := by decide
  have hdescent : baseEnd_5152311 < baseStart_5152311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152338 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_5152338 : Nat := 118140960795 + 5152338 * 2 ^ 59
def prefixEnd_5152338 : Nat := 4983230072969 + 3 ^ 40 * 5152338 * 2
def baseEnd_5152338 : Nat := 2645625888425167687579835

theorem tailTrace_5152338 : CollatzResearch.WordTrace tailWord_5152338 prefixEnd_5152338 2645625888425167687579835 := by
  unfold tailWord_5152338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980301301991712529792417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125280803471977900079446445 46980301301991712529792417)
  ·
    refine ⟨35235225976493784397344313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46980301301991712529792417 35235225976493784397344313)
    ·
      refine ⟨26426419482370338298008235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35235225976493784397344313 26426419482370338298008235)
      ·
        refine ⟨39639629223555507447012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26426419482370338298008235 39639629223555507447012353)
        ·
          refine ⟨29729721917666630585259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39639629223555507447012353 29729721917666630585259265)
          ·
            refine ⟨22297291438249972938944449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29729721917666630585259265 22297291438249972938944449)
            ·
              refine ⟨16722968578687479704208337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22297291438249972938944449 16722968578687479704208337)
              ·
                refine ⟨12542226434015609778156253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16722968578687479704208337 12542226434015609778156253)
                ·
                  refine ⟨4703334912755853666808595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12542226434015609778156253 4703334912755853666808595)
                  ·
                    refine ⟨7055002369133780500212893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703334912755853666808595 7055002369133780500212893)
                    ·
                      refine ⟨2645625888425167687579835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055002369133780500212893 2645625888425167687579835)
                      ·
                        rfl

theorem cell23_5152338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_5152338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152338 prefixEnd_5152338 := by exact prefixLift 5152338
  have htrace : WordTrace (prefixWord ++ tailWord_5152338) baseStart_5152338 baseEnd_5152338 := by
    simpa [prefixWord, tailWord_5152338, baseEnd_5152338] using wordTrace_append hprefix tailTrace_5152338
  have hstable : (prefixWord ++ tailWord_5152338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152338).length < 2 ^ (prefixWord ++ tailWord_5152338).sum := by decide
  have hdescent : baseEnd_5152338 < baseStart_5152338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152348 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_5152348 : Nat := 118140960795 + 5152348 * 2 ^ 59
def prefixEnd_5152348 : Nat := 4983230072969 + 3 ^ 40 * 5152348 * 2
def baseEnd_5152348 : Nat := 2645631023231712648454789

theorem tailTrace_5152348 : CollatzResearch.WordTrace tailWord_5152348 prefixEnd_5152348 2645631023231712648454789 := by
  unfold tailWord_5152348
  simp only [CollatzResearch.WordTrace]
  refine ⟨93960784968965310913516849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125281046625287081218022465 93960784968965310913516849)
  ·
    refine ⟨70470588726723983185137637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93960784968965310913516849 70470588726723983185137637)
    ·
      refine ⟨13213235386260746847213307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70470588726723983185137637 13213235386260746847213307)
      ·
        refine ⟨19819853079391120270819961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13213235386260746847213307 19819853079391120270819961)
        ·
          refine ⟨14864889809543340203114971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19819853079391120270819961 14864889809543340203114971)
          ·
            refine ⟨22297334714315010304672457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14864889809543340203114971 22297334714315010304672457)
            ·
              refine ⟨16723001035736257728504343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22297334714315010304672457 16723001035736257728504343)
              ·
                refine ⟨25084501553604386592756515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723001035736257728504343 25084501553604386592756515)
                ·
                  refine ⟨37626752330406579889134773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25084501553604386592756515 37626752330406579889134773)
                  ·
                    refine ⟨3527508030975616864606385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37626752330406579889134773 3527508030975616864606385)
                    ·
                      refine ⟨2645631023231712648454789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527508030975616864606385 2645631023231712648454789)
                      ·
                        rfl

theorem cell23_5152348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_5152348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152348 prefixEnd_5152348 := by exact prefixLift 5152348
  have htrace : WordTrace (prefixWord ++ tailWord_5152348) baseStart_5152348 baseEnd_5152348 := by
    simpa [prefixWord, tailWord_5152348, baseEnd_5152348] using wordTrace_append hprefix tailTrace_5152348
  have hstable : (prefixWord ++ tailWord_5152348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152348).length < 2 ^ (prefixWord ++ tailWord_5152348).sum := by decide
  have hdescent : baseEnd_5152348 < baseStart_5152348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152349 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5152349 : Nat := 118140960795 + 5152349 * 2 ^ 59
def prefixEnd_5152349 : Nat := 4983230072969 + 3 ^ 40 * 5152349 * 2
def baseEnd_5152349 : Nat := 881877178904122381514095

theorem tailTrace_5152349 : CollatzResearch.WordTrace tailWord_5152349 prefixEnd_5152349 881877178904122381514095 := by
  unfold tailWord_5152349
  simp only [CollatzResearch.WordTrace]
  refine ⟨187921606410926998997820101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125281070940617999331880067 187921606410926998997820101)
  ·
    refine ⟨35235301202048812312091269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187921606410926998997820101 35235301202048812312091269)
    ·
      refine ⟨6606618975384152308517113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35235301202048812312091269 6606618975384152308517113)
      ·
        refine ⟨4954964231538114231387835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6606618975384152308517113 4954964231538114231387835)
        ·
          refine ⟨7432446347307171347081753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954964231538114231387835 7432446347307171347081753)
          ·
            refine ⟨5574334760480378510311315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7432446347307171347081753 5574334760480378510311315)
            ·
              refine ⟨8361502140720567765466973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574334760480378510311315 8361502140720567765466973)
              ·
                refine ⟨3135563302770212912050115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8361502140720567765466973 3135563302770212912050115)
                ·
                  refine ⟨4703344954155319368075173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135563302770212912050115 4703344954155319368075173)
                  ·
                    refine ⟨881877178904122381514095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703344954155319368075173 881877178904122381514095)
                    ·
                      rfl

theorem cell23_5152349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5152349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152349 prefixEnd_5152349 := by exact prefixLift 5152349
  have htrace : WordTrace (prefixWord ++ tailWord_5152349) baseStart_5152349 baseEnd_5152349 := by
    simpa [prefixWord, tailWord_5152349, baseEnd_5152349] using wordTrace_append hprefix tailTrace_5152349
  have hstable : (prefixWord ++ tailWord_5152349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152349).length < 2 ^ (prefixWord ++ tailWord_5152349).sum := by decide
  have hdescent : baseEnd_5152349 < baseStart_5152349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152355 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 1, 1, 3]
def baseStart_5152355 : Nat := 118140960795 + 5152355 * 2 ^ 59
def prefixEnd_5152355 : Nat := 4983230072969 + 3 ^ 40 * 5152355 * 2
def baseEnd_5152355 : Nat := 2645634617596294121067257

theorem tailTrace_5152355 : CollatzResearch.WordTrace tailWord_5152355 prefixEnd_5152355 2645634617596294121067257 := by
  unfold tailWord_5152355
  simp only [CollatzResearch.WordTrace]
  refine ⟨187921825248905262022538519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125281216832603508015025679 187921825248905262022538519)
  ·
    refine ⟨281882737873357893033807779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187921825248905262022538519 281882737873357893033807779)
    ·
      refine ⟨422824106810036839550711669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281882737873357893033807779 422824106810036839550711669)
      ·
        refine ⟨39639760013440953707879219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422824106810036839550711669 39639760013440953707879219)
        ·
          refine ⟨59459640020161430561818829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39639760013440953707879219 59459640020161430561818829)
          ·
            refine ⟨22297365007560536460682061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59459640020161430561818829 22297365007560536460682061)
            ·
              refine ⟨8361511877835201172755773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22297365007560536460682061 8361511877835201172755773)
              ·
                refine ⟨3135566954188200439783415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8361511877835201172755773 3135566954188200439783415)
                ·
                  refine ⟨4703350431282300659675123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135566954188200439783415 4703350431282300659675123)
                  ·
                    refine ⟨7055025646923450989512685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703350431282300659675123 7055025646923450989512685)
                    ·
                      refine ⟨2645634617596294121067257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055025646923450989512685 2645634617596294121067257)
                      ·
                        rfl

theorem cell23_5152355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_5152355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152355 prefixEnd_5152355 := by exact prefixLift 5152355
  have htrace : WordTrace (prefixWord ++ tailWord_5152355) baseStart_5152355 baseEnd_5152355 := by
    simpa [prefixWord, tailWord_5152355, baseEnd_5152355] using wordTrace_append hprefix tailTrace_5152355
  have hstable : (prefixWord ++ tailWord_5152355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152355).length < 2 ^ (prefixWord ++ tailWord_5152355).sum := by decide
  have hdescent : baseEnd_5152355 < baseStart_5152355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152361 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_5152361 : Nat := 118140960795 + 5152361 * 2 ^ 59
def prefixEnd_5152361 : Nat := 4983230072969 + 3 ^ 40 * 5152361 * 2
def baseEnd_5152361 : Nat := 2645637698480221097592229

theorem tailTrace_5152361 : CollatzResearch.WordTrace tailWord_5152361 prefixEnd_5152361 2645637698480221097592229 := by
  unfold tailWord_5152361
  simp only [CollatzResearch.WordTrace]
  refine ⟨187922044086883525047256937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125281362724589016698171291 187922044086883525047256937)
  ·
    refine ⟨140941533065162643785442703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187922044086883525047256937 140941533065162643785442703)
    ·
      refine ⟨211412299597743965678164055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140941533065162643785442703 211412299597743965678164055)
      ·
        refine ⟨317118449396615948517246083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211412299597743965678164055 317118449396615948517246083)
        ·
          refine ⟨475677674094923922775869125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317118449396615948517246083 475677674094923922775869125)
          ·
            refine ⟨89189563892798235520475461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475677674094923922775869125 89189563892798235520475461)
            ·
              refine ⟨16723043229899669160089149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89189563892798235520475461 16723043229899669160089149)
              ·
                refine ⟨6271141211212375935033431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16723043229899669160089149 6271141211212375935033431)
                ·
                  refine ⟨9406711816818563902550147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271141211212375935033431 9406711816818563902550147)
                  ·
                    refine ⟨14110067725227845853825221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9406711816818563902550147 14110067725227845853825221)
                    ·
                      refine ⟨2645637698480221097592229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14110067725227845853825221 2645637698480221097592229)
                      ·
                        rfl

theorem cell23_5152361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_5152361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152361 prefixEnd_5152361 := by exact prefixLift 5152361
  have htrace : WordTrace (prefixWord ++ tailWord_5152361) baseStart_5152361 baseEnd_5152361 := by
    simpa [prefixWord, tailWord_5152361, baseEnd_5152361] using wordTrace_append hprefix tailTrace_5152361
  have hstable : (prefixWord ++ tailWord_5152361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152361).length < 2 ^ (prefixWord ++ tailWord_5152361).sum := by decide
  have hdescent : baseEnd_5152361 < baseStart_5152361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152365 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5152365 : Nat := 118140960795 + 5152365 * 2 ^ 59
def prefixEnd_5152365 : Nat := 4983230072969 + 3 ^ 40 * 5152365 * 2
def baseEnd_5152365 : Nat := 2645639752402839081942211

theorem tailTrace_5152365 : CollatzResearch.WordTrace tailWord_5152365 prefixEnd_5152365 2645639752402839081942211 := by
  unfold tailWord_5152365
  simp only [CollatzResearch.WordTrace]
  refine ⟨187922189978869033730402549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125281459985912689153601699 187922189978869033730402549)
  ·
    refine ⟨17617705310518971912225239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187922189978869033730402549 17617705310518971912225239)
    ·
      refine ⟨26426557965778457868337859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617705310518971912225239 26426557965778457868337859)
      ·
        refine ⟨39639836948667686802506789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26426557965778457868337859 39639836948667686802506789)
        ·
          refine ⟨7432469427875191275470023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39639836948667686802506789 7432469427875191275470023)
          ·
            refine ⟨11148704141812786913205035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432469427875191275470023 11148704141812786913205035)
            ·
              refine ⟨16723056212719180369807553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148704141812786913205035 16723056212719180369807553)
              ·
                refine ⟨12542292159539385277355665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723056212719180369807553 12542292159539385277355665)
                ·
                  refine ⟨9406719119654538958016749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542292159539385277355665 9406719119654538958016749)
                  ·
                    refine ⟨3527519669870452109256281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9406719119654538958016749 3527519669870452109256281)
                    ·
                      refine ⟨2645639752402839081942211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527519669870452109256281 2645639752402839081942211)
                      ·
                        rfl

theorem cell23_5152365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5152365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152365 prefixEnd_5152365 := by exact prefixLift 5152365
  have htrace : WordTrace (prefixWord ++ tailWord_5152365) baseStart_5152365 baseEnd_5152365 := by
    simpa [prefixWord, tailWord_5152365, baseEnd_5152365] using wordTrace_append hprefix tailTrace_5152365
  have hstable : (prefixWord ++ tailWord_5152365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152365).length < 2 ^ (prefixWord ++ tailWord_5152365).sum := by decide
  have hdescent : baseEnd_5152365 < baseStart_5152365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152378 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_5152378 : Nat := 118140960795 + 5152378 * 2 ^ 59
def prefixEnd_5152378 : Nat := 4983230072969 + 3 ^ 40 * 5152378 * 2
def baseEnd_5152378 : Nat := 2645646427651347531079651

theorem tailTrace_5152378 : CollatzResearch.WordTrace tailWord_5152378 prefixEnd_5152378 2645646427651347531079651 := by
  unfold tailWord_5152378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980666031955484237656447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125281776085214624633750525 46980666031955484237656447)
  ·
    refine ⟨70470999047933226356484671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46980666031955484237656447 70470999047933226356484671)
    ·
      refine ⟨105706498571899839534727007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70470999047933226356484671 105706498571899839534727007)
      ·
        refine ⟨158559747857849759302090511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105706498571899839534727007 158559747857849759302090511)
        ·
          refine ⟨237839621786774638953135767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158559747857849759302090511 237839621786774638953135767)
          ·
            refine ⟨356759432680161958429703651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237839621786774638953135767 356759432680161958429703651)
            ·
              refine ⟨535139149020242937644555477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356759432680161958429703651 535139149020242937644555477)
              ·
                refine ⟨12542323805161943851044269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 535139149020242937644555477 12542323805161943851044269)
                ·
                  refine ⟨4703371426935728944141601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12542323805161943851044269 4703371426935728944141601)
                  ·
                    refine ⟨3527528570201796708106201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4703371426935728944141601 3527528570201796708106201)
                    ·
                      refine ⟨2645646427651347531079651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527528570201796708106201 2645646427651347531079651)
                      ·
                        rfl

theorem cell23_5152378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_5152378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152378 prefixEnd_5152378 := by exact prefixLift 5152378
  have htrace : WordTrace (prefixWord ++ tailWord_5152378) baseStart_5152378 baseEnd_5152378 := by
    simpa [prefixWord, tailWord_5152378, baseEnd_5152378] using wordTrace_append hprefix tailTrace_5152378
  have hstable : (prefixWord ++ tailWord_5152378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152378).length < 2 ^ (prefixWord ++ tailWord_5152378).sum := by decide
  have hdescent : baseEnd_5152378 < baseStart_5152378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152381 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5152381 : Nat := 118140960795 + 5152381 * 2 ^ 59
def prefixEnd_5152381 : Nat := 4983230072969 + 3 ^ 40 * 5152381 * 2
def baseEnd_5152381 : Nat := 2645647968093311019342137

theorem tailTrace_5152381 : CollatzResearch.WordTrace tailWord_5152381 prefixEnd_5152381 2645647968093311019342137 := by
  unfold tailWord_5152381
  simp only [CollatzResearch.WordTrace]
  refine ⟨187922773546811068462984997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125281849031207378975323331 187922773546811068462984997)
  ·
    refine ⟨35235520040027075336809687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187922773546811068462984997 35235520040027075336809687)
    ·
      refine ⟨52853280060040613005214531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35235520040027075336809687 52853280060040613005214531)
      ·
        refine ⟨79279920090060919507821797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52853280060040613005214531 79279920090060919507821797)
        ·
          refine ⟨14864985016886422407716587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79279920090060919507821797 14864985016886422407716587)
          ·
            refine ⟨22297477525329633611574881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14864985016886422407716587 22297477525329633611574881)
            ·
              refine ⟨16723108143997225208681161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22297477525329633611574881 16723108143997225208681161)
              ·
                refine ⟨12542331107997918906510871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723108143997225208681161 12542331107997918906510871)
                ·
                  refine ⟨18813496661996878359766307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542331107997918906510871 18813496661996878359766307)
                  ·
                    refine ⟨28220244992995317539649461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18813496661996878359766307 28220244992995317539649461)
                    ·
                      refine ⟨2645647968093311019342137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28220244992995317539649461 2645647968093311019342137)
                      ·
                        rfl

theorem cell23_5152381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5152381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152381 prefixEnd_5152381 := by exact prefixLift 5152381
  have htrace : WordTrace (prefixWord ++ tailWord_5152381) baseStart_5152381 baseEnd_5152381 := by
    simpa [prefixWord, tailWord_5152381, baseEnd_5152381] using wordTrace_append hprefix tailTrace_5152381
  have hstable : (prefixWord ++ tailWord_5152381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152381).length < 2 ^ (prefixWord ++ tailWord_5152381).sum := by decide
  have hdescent : baseEnd_5152381 < baseStart_5152381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152384 : List Nat := [2, 1, 1, 2, 1, 4, 4, 8]
def baseStart_5152384 : Nat := 118140960795 + 5152384 * 2 ^ 59
def prefixEnd_5152384 : Nat := 4983230072969 + 3 ^ 40 * 5152384 * 2
def baseEnd_5152384 : Nat := 97987018834639796577949

theorem tailTrace_5152384 : CollatzResearch.WordTrace tailWord_5152384 prefixEnd_5152384 97987018834639796577949 := by
  unfold tailWord_5152384
  simp only [CollatzResearch.WordTrace]
  refine ⟨93961441482900099987672103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125281921977200133316896137 93961441482900099987672103)
  ·
    refine ⟨140942162224350149981508155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93961441482900099987672103 140942162224350149981508155)
    ·
      refine ⟨211413243336525224972262233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140942162224350149981508155 211413243336525224972262233)
      ·
        refine ⟨158559932502393918729196675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211413243336525224972262233 158559932502393918729196675)
        ·
          refine ⟨237839898753590878093795013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158559932502393918729196675 237839898753590878093795013)
          ·
            refine ⟨44594981016298289642586565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237839898753590878093795013 44594981016298289642586565)
            ·
              refine ⟨8361558940555929307984981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44594981016298289642586565 8361558940555929307984981)
              ·
                refine ⟨97987018834639796577949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8361558940555929307984981 97987018834639796577949)
                ·
                  rfl

theorem cell23_5152384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_5152384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152384 prefixEnd_5152384 := by exact prefixLift 5152384
  have htrace : WordTrace (prefixWord ++ tailWord_5152384) baseStart_5152384 baseEnd_5152384 := by
    simpa [prefixWord, tailWord_5152384, baseEnd_5152384] using wordTrace_append hprefix tailTrace_5152384
  have hstable : (prefixWord ++ tailWord_5152384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152384).length < 2 ^ (prefixWord ++ tailWord_5152384).sum := by decide
  have hdescent : baseEnd_5152384 < baseStart_5152384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152392 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_5152392 : Nat := 118140960795 + 5152392 * 2 ^ 59
def prefixEnd_5152392 : Nat := 4983230072969 + 3 ^ 40 * 5152392 * 2
def baseEnd_5152392 : Nat := 881884538793503492101529

theorem tailTrace_5152392 : CollatzResearch.WordTrace tailWord_5152392 prefixEnd_5152392 881884538793503492101529 := by
  unfold tailWord_5152392
  simp only [CollatzResearch.WordTrace]
  refine ⟨93961587374885608670817715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125282116499847478227756953 93961587374885608670817715)
  ·
    refine ⟨140942381062328413006226573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93961587374885608670817715 140942381062328413006226573)
    ·
      refine ⟨52853392898373154877334965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140942381062328413006226573 52853392898373154877334965)
      ·
        refine ⟨4955005584222483269750153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52853392898373154877334965 4955005584222483269750153)
        ·
          refine ⟨3716254188166862452312615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955005584222483269750153 3716254188166862452312615)
          ·
            refine ⟨5574381282250293678468923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716254188166862452312615 5574381282250293678468923)
            ·
              refine ⟨8361571923375440517703385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574381282250293678468923 8361571923375440517703385)
              ·
                refine ⟨6271178942531580388277539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8361571923375440517703385 6271178942531580388277539)
                ·
                  refine ⟨9406768413797370582416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271178942531580388277539 9406768413797370582416309)
                  ·
                    refine ⟨881884538793503492101529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9406768413797370582416309 881884538793503492101529)
                    ·
                      rfl

theorem cell23_5152392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_5152392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152392 prefixEnd_5152392 := by exact prefixLift 5152392
  have htrace : WordTrace (prefixWord ++ tailWord_5152392) baseStart_5152392 baseEnd_5152392 := by
    simpa [prefixWord, tailWord_5152392, baseEnd_5152392] using wordTrace_append hprefix tailTrace_5152392
  have hstable : (prefixWord ++ tailWord_5152392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152392).length < 2 ^ (prefixWord ++ tailWord_5152392).sum := by decide
  have hdescent : baseEnd_5152392 < baseStart_5152392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152398 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5152398 : Nat := 118140960795 + 5152398 * 2 ^ 59
def prefixEnd_5152398 : Nat := 4983230072969 + 3 ^ 40 * 5152398 * 2
def baseEnd_5152398 : Nat := 2645656697264437452829559

theorem tailTrace_5152398 : CollatzResearch.WordTrace tailWord_5152398 prefixEnd_5152398 2645656697264437452829559 := by
  unfold tailWord_5152398
  simp only [CollatzResearch.WordTrace]
  refine ⟨23490424198468685045794231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125282262391832986910902565 23490424198468685045794231)
  ·
    refine ⟨35235636297703027568691347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23490424198468685045794231 35235636297703027568691347)
    ·
      refine ⟨52853454446554541353037021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35235636297703027568691347 52853454446554541353037021)
      ·
        refine ⟨19820045417457953007388883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52853454446554541353037021 19820045417457953007388883)
        ·
          refine ⟨29730068126186929511083325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19820045417457953007388883 29730068126186929511083325)
          ·
            refine ⟨11148775547320098566656247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29730068126186929511083325 11148775547320098566656247)
            ·
              refine ⟨16723163320980147849984371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148775547320098566656247 16723163320980147849984371)
              ·
                refine ⟨25084744981470221774976557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723163320980147849984371 25084744981470221774976557)
                ·
                  refine ⟨9406779368051333165616209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25084744981470221774976557 9406779368051333165616209)
                  ·
                    refine ⟨7055084526038499874212157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9406779368051333165616209 7055084526038499874212157)
                    ·
                      refine ⟨2645656697264437452829559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055084526038499874212157 2645656697264437452829559)
                      ·
                        rfl

theorem cell23_5152398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5152398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152398 prefixEnd_5152398 := by exact prefixLift 5152398
  have htrace : WordTrace (prefixWord ++ tailWord_5152398) baseStart_5152398 baseEnd_5152398 := by
    simpa [prefixWord, tailWord_5152398, baseEnd_5152398] using wordTrace_append hprefix tailTrace_5152398
  have hstable : (prefixWord ++ tailWord_5152398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152398).length < 2 ^ (prefixWord ++ tailWord_5152398).sum := by decide
  have hdescent : baseEnd_5152398 < baseStart_5152398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152415 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5152415 : Nat := 118140960795 + 5152415 * 2 ^ 59
def prefixEnd_5152415 : Nat := 4983230072969 + 3 ^ 40 * 5152415 * 2
def baseEnd_5152415 : Nat := 2645665426435563886316981

theorem tailTrace_5152415 : CollatzResearch.WordTrace tailWord_5152415 prefixEnd_5152415 2645665426435563886316981 := by
  unfold tailWord_5152415
  simp only [CollatzResearch.WordTrace]
  refine ⟨187924013628687892269722699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125282675752458594846481799 187924013628687892269722699)
  ·
    refine ⟨281886020443031838404584049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187924013628687892269722699 281886020443031838404584049)
    ·
      refine ⟨211414515332273878803438037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281886020443031838404584049 211414515332273878803438037)
      ·
        refine ⟨4955027703100169034455579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 211414515332273878803438037 4955027703100169034455579)
        ·
          refine ⟨7432541554650253551683369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955027703100169034455579 7432541554650253551683369)
          ·
            refine ⟨5574406165987690163762527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7432541554650253551683369 5574406165987690163762527)
            ·
              refine ⟨8361609248981535245643791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574406165987690163762527 8361609248981535245643791)
              ·
                refine ⟨12542413873472302868465687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361609248981535245643791 12542413873472302868465687)
                ·
                  refine ⟨18813620810208454302698531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542413873472302868465687 18813620810208454302698531)
                  ·
                    refine ⟨28220431215312681454047797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18813620810208454302698531 28220431215312681454047797)
                    ·
                      refine ⟨2645665426435563886316981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28220431215312681454047797 2645665426435563886316981)
                      ·
                        rfl

theorem cell23_5152415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5152415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152415 prefixEnd_5152415 := by exact prefixLift 5152415
  have htrace : WordTrace (prefixWord ++ tailWord_5152415) baseStart_5152415 baseEnd_5152415 := by
    simpa [prefixWord, tailWord_5152415, baseEnd_5152415] using wordTrace_append hprefix tailTrace_5152415
  have hstable : (prefixWord ++ tailWord_5152415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152415).length < 2 ^ (prefixWord ++ tailWord_5152415).sum := by decide
  have hdescent : baseEnd_5152415 < baseStart_5152415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152418 : List Nat := [3, 3, 1, 4, 2, 10]
def baseStart_5152418 : Nat := 118140960795 + 5152418 * 2 ^ 59
def prefixEnd_5152418 : Nat := 4983230072969 + 3 ^ 40 * 5152418 * 2
def baseEnd_5152418 : Nat := 10887518382212046808969

theorem tailTrace_5152418 : CollatzResearch.WordTrace tailWord_5152418 prefixEnd_5152418 10887518382212046808969 := by
  unfold tailWord_5152418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46981030761919255945520477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125282748698451349188054605 46981030761919255945520477)
  ·
    refine ⟨17617886535719720979570179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46981030761919255945520477 17617886535719720979570179)
    ·
      refine ⟨26426829803579581469355269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617886535719720979570179 26426829803579581469355269)
      ·
        refine ⟨4955030588171171525504113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26426829803579581469355269 4955030588171171525504113)
        ·
          refine ⟨3716272941128378644128085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955030588171171525504113 3716272941128378644128085)
          ·
            refine ⟨10887518382212046808969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3716272941128378644128085 10887518382212046808969)
            ·
              rfl

theorem cell23_5152418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 10].length) (baseStart_5152418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152418 prefixEnd_5152418 := by exact prefixLift 5152418
  have htrace : WordTrace (prefixWord ++ tailWord_5152418) baseStart_5152418 baseEnd_5152418 := by
    simpa [prefixWord, tailWord_5152418, baseEnd_5152418] using wordTrace_append hprefix tailTrace_5152418
  have hstable : (prefixWord ++ tailWord_5152418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152418).length < 2 ^ (prefixWord ++ tailWord_5152418).sum := by decide
  have hdescent : baseEnd_5152418 < baseStart_5152418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152485 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5152485 : Nat := 118140960795 + 5152485 * 2 ^ 59
def prefixEnd_5152485 : Nat := 4983230072969 + 3 ^ 40 * 5152485 * 2
def baseEnd_5152485 : Nat := 2645701370081378612441659

theorem tailTrace_5152485 : CollatzResearch.WordTrace tailWord_5152485 prefixEnd_5152485 2645701370081378612441659 := by
  unfold tailWord_5152485
  simp only [CollatzResearch.WordTrace]
  refine ⟨187926566738434294224770909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125284377825622862816513939 187926566738434294224770909)
  ·
    refine ⟨70472462526912860334289091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187926566738434294224770909 70472462526912860334289091)
    ·
      refine ⟨105708693790369290501433637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70472462526912860334289091 105708693790369290501433637)
      ·
        refine ⟨19820380085694241969018807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105708693790369290501433637 19820380085694241969018807)
        ·
          refine ⟨29730570128541362953528211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19820380085694241969018807 29730570128541362953528211)
          ·
            refine ⟨44595855192812044430292317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29730570128541362953528211 44595855192812044430292317)
            ·
              refine ⟨16723445697304516661359619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44595855192812044430292317 16723445697304516661359619)
              ·
                refine ⟨25085168545956774992039429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723445697304516661359619 25085168545956774992039429)
                ·
                  refine ⟨4703469102366895311007393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25085168545956774992039429 4703469102366895311007393)
                  ·
                    refine ⟨3527601826775171483255545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4703469102366895311007393 3527601826775171483255545)
                    ·
                      refine ⟨2645701370081378612441659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527601826775171483255545 2645701370081378612441659)
                      ·
                        rfl

theorem cell23_5152485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5152485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152485 prefixEnd_5152485 := by exact prefixLift 5152485
  have htrace : WordTrace (prefixWord ++ tailWord_5152485) baseStart_5152485 baseEnd_5152485 := by
    simpa [prefixWord, tailWord_5152485, baseEnd_5152485] using wordTrace_append hprefix tailTrace_5152485
  have hstable : (prefixWord ++ tailWord_5152485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152485).length < 2 ^ (prefixWord ++ tailWord_5152485).sum := by decide
  have hdescent : baseEnd_5152485 < baseStart_5152485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152502 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5152502 : Nat := 118140960795 + 5152502 * 2 ^ 59
def prefixEnd_5152502 : Nat := 4983230072969 + 3 ^ 40 * 5152502 * 2
def baseEnd_5152502 : Nat := 2645710099252505045929081

theorem tailTrace_5152502 : CollatzResearch.WordTrace tailWord_5152502 prefixEnd_5152502 2645710099252505045929081 := by
  unfold tailWord_5152502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11745449173710794133008735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125284791186248470752093173 11745449173710794133008735)
  ·
    refine ⟨17618173760566191199513103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11745449173710794133008735 17618173760566191199513103)
    ·
      refine ⟨26427260640849286799269655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17618173760566191199513103 26427260640849286799269655)
      ·
        refine ⟨39640890961273930198904483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26427260640849286799269655 39640890961273930198904483)
        ·
          refine ⟨59461336441910895298356725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39640890961273930198904483 59461336441910895298356725)
          ·
            refine ⟨5574500291429146434220943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59461336441910895298356725 5574500291429146434220943)
            ·
              refine ⟨8361750437143719651331415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574500291429146434220943 8361750437143719651331415)
              ·
                refine ⟨12542625655715579476997123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361750437143719651331415 12542625655715579476997123)
                ·
                  refine ⟨18813938483573369215495685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542625655715579476997123 18813938483573369215495685)
                  ·
                    refine ⟨3527613465670006727905441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18813938483573369215495685 3527613465670006727905441)
                    ·
                      refine ⟨2645710099252505045929081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527613465670006727905441 2645710099252505045929081)
                      ·
                        rfl

theorem cell23_5152502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5152502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152502 prefixEnd_5152502 := by exact prefixLift 5152502
  have htrace : WordTrace (prefixWord ++ tailWord_5152502) baseStart_5152502 baseEnd_5152502 := by
    simpa [prefixWord, tailWord_5152502, baseEnd_5152502] using wordTrace_append hprefix tailTrace_5152502
  have hstable : (prefixWord ++ tailWord_5152502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152502).length < 2 ^ (prefixWord ++ tailWord_5152502).sum := by decide
  have hdescent : baseEnd_5152502 < baseStart_5152502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152521 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_5152521 : Nat := 118140960795 + 5152521 * 2 ^ 59
def prefixEnd_5152521 : Nat := 4983230072969 + 3 ^ 40 * 5152521 * 2
def baseEnd_5152521 : Nat := 881906618461646823863831

theorem tailTrace_5152521 : CollatzResearch.WordTrace tailWord_5152521 prefixEnd_5152521 881906618461646823863831 := by
  unfold tailWord_5152521
  simp only [CollatzResearch.WordTrace]
  refine ⟨187927879766303872373081417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125285253177535914915387611 187927879766303872373081417)
  ·
    refine ⟨140945909824727904279811063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187927879766303872373081417 140945909824727904279811063)
    ·
      refine ⟨211418864737091856419716595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140945909824727904279811063 211418864737091856419716595)
      ·
        refine ⟨317128297105637784629574893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211418864737091856419716595 317128297105637784629574893)
        ·
          refine ⟨118923111414614169236090585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317128297105637784629574893 118923111414614169236090585)
          ·
            refine ⟨89192333560960626927067939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118923111414614169236090585 89192333560960626927067939)
            ·
              refine ⟨133788500341440940390601909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89192333560960626927067939 133788500341440940390601909)
              ·
                refine ⟨12542671907010088161618929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133788500341440940390601909 12542671907010088161618929)
                ·
                  refine ⟨9407003930257566121214197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542671907010088161618929 9407003930257566121214197)
                  ·
                    refine ⟨881906618461646823863831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9407003930257566121214197 881906618461646823863831)
                    ·
                      rfl

theorem cell23_5152521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_5152521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152521 prefixEnd_5152521 := by exact prefixLift 5152521
  have htrace : WordTrace (prefixWord ++ tailWord_5152521) baseStart_5152521 baseEnd_5152521 := by
    simpa [prefixWord, tailWord_5152521, baseEnd_5152521] using wordTrace_append hprefix tailTrace_5152521
  have hstable : (prefixWord ++ tailWord_5152521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152521).length < 2 ^ (prefixWord ++ tailWord_5152521).sum := by decide
  have hdescent : baseEnd_5152521 < baseStart_5152521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152538 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_5152538 : Nat := 118140960795 + 5152538 * 2 ^ 59
def prefixEnd_5152538 : Nat := 4983230072969 + 3 ^ 40 * 5152538 * 2
def baseEnd_5152538 : Nat := 881909528185355635026305

theorem tailTrace_5152538 : CollatzResearch.WordTrace tailWord_5152538 prefixEnd_5152538 881909528185355635026305 := by
  unfold tailWord_5152538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46982124951810571069112567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125285666538161522850966845 46982124951810571069112567)
  ·
    refine ⟨70473187427715856603668851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46982124951810571069112567 70473187427715856603668851)
    ·
      refine ⟨105709781141573784905503277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70473187427715856603668851 105709781141573784905503277)
      ·
        refine ⟨39641167928090169339563729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105709781141573784905503277 39641167928090169339563729)
        ·
          refine ⟨29730875946067627004672797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39641167928090169339563729 29730875946067627004672797)
          ·
            refine ⟨11149078479775360126752299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29730875946067627004672797 11149078479775360126752299)
            ·
              refine ⟨16723617719663040190128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11149078479775360126752299 16723617719663040190128449)
              ·
                refine ⟨12542713289747280142596337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723617719663040190128449 12542713289747280142596337)
                ·
                  refine ⟨9407034967310460106947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542713289747280142596337 9407034967310460106947253)
                  ·
                    refine ⟨881909528185355635026305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9407034967310460106947253 881909528185355635026305)
                    ·
                      rfl

theorem cell23_5152538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_5152538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152538 prefixEnd_5152538 := by exact prefixLift 5152538
  have htrace : WordTrace (prefixWord ++ tailWord_5152538) baseStart_5152538 baseEnd_5152538 := by
    simpa [prefixWord, tailWord_5152538, baseEnd_5152538] using wordTrace_append hprefix tailTrace_5152538
  have hstable : (prefixWord ++ tailWord_5152538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152538).length < 2 ^ (prefixWord ++ tailWord_5152538).sum := by decide
  have hdescent : baseEnd_5152538 < baseStart_5152538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152548 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5152548 : Nat := 118140960795 + 5152548 * 2 ^ 59
def prefixEnd_5152548 : Nat := 4983230072969 + 3 ^ 40 * 5152548 * 2
def baseEnd_5152548 : Nat := 2645733719362611865953869

theorem tailTrace_5152548 : CollatzResearch.WordTrace tailWord_5152548 prefixEnd_5152548 2645733719362611865953869 := by
  unfold tailWord_5152548
  simp only [CollatzResearch.WordTrace]
  refine ⟨93964432268603027992157149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125285909691470703989542865 93964432268603027992157149)
  ·
    refine ⟨35236662100726135497058931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93964432268603027992157149 35236662100726135497058931)
    ·
      refine ⟨52854993151089203245588397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35236662100726135497058931 52854993151089203245588397)
      ·
        refine ⟨19820622431658451217095649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52854993151089203245588397 19820622431658451217095649)
        ·
          refine ⟨14865466823743838412821737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19820622431658451217095649 14865466823743838412821737)
          ·
            refine ⟨11149100117807878809616303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14865466823743838412821737 11149100117807878809616303)
            ·
              refine ⟨16723650176711818214424455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11149100117807878809616303 16723650176711818214424455)
              ·
                refine ⟨25085475265067727321636683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723650176711818214424455 25085475265067727321636683)
                ·
                  refine ⟨37628212897601590982455025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25085475265067727321636683 37628212897601590982455025)
                  ·
                    refine ⟨28221159673201193236841269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37628212897601590982455025 28221159673201193236841269)
                    ·
                      refine ⟨2645733719362611865953869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28221159673201193236841269 2645733719362611865953869)
                      ·
                        rfl

theorem cell23_5152548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5152548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152548 prefixEnd_5152548 := by exact prefixLift 5152548
  have htrace : WordTrace (prefixWord ++ tailWord_5152548) baseStart_5152548 baseEnd_5152548 := by
    simpa [prefixWord, tailWord_5152548, baseEnd_5152548] using wordTrace_append hprefix tailTrace_5152548
  have hstable : (prefixWord ++ tailWord_5152548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152548).length < 2 ^ (prefixWord ++ tailWord_5152548).sum := by decide
  have hdescent : baseEnd_5152548 < baseStart_5152548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152575 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_5152575 : Nat := 118140960795 + 5152575 * 2 ^ 59
def prefixEnd_5152575 : Nat := 4983230072969 + 3 ^ 40 * 5152575 * 2
def baseEnd_5152575 : Nat := 2645747583340283260316245

theorem tailTrace_5152575 : CollatzResearch.WordTrace tailWord_5152575 prefixEnd_5152575 2645747583340283260316245 := by
  unfold tailWord_5152575
  simp only [CollatzResearch.WordTrace]
  refine ⟨187929849308108239595547179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125286566205405493063698119 187929849308108239595547179)
  ·
    refine ⟨281894773962162359393320769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187929849308108239595547179 281894773962162359393320769)
    ·
      refine ⟨211421080471621769544990577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281894773962162359393320769 211421080471621769544990577)
      ·
        refine ⟨158565810353716327158742933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211421080471621769544990577 158565810353716327158742933)
        ·
          refine ⟨7432772360330452835566075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158565810353716327158742933 7432772360330452835566075)
          ·
            refine ⟨11149158540495679253349113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432772360330452835566075 11149158540495679253349113)
            ·
              refine ⟨8361868905371759440011835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11149158540495679253349113 8361868905371759440011835)
              ·
                refine ⟨12542803358057639160017753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361868905371759440011835 12542803358057639160017753)
                ·
                  refine ⟨9407102518543229370013315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542803358057639160017753 9407102518543229370013315)
                  ·
                    refine ⟨14110653777814844055019973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9407102518543229370013315 14110653777814844055019973)
                    ·
                      refine ⟨2645747583340283260316245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14110653777814844055019973 2645747583340283260316245)
                      ·
                        rfl

theorem cell23_5152575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_5152575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152575 prefixEnd_5152575 := by exact prefixLift 5152575
  have htrace : WordTrace (prefixWord ++ tailWord_5152575) baseStart_5152575 baseEnd_5152575 := by
    simpa [prefixWord, tailWord_5152575, baseEnd_5152575] using wordTrace_append hprefix tailTrace_5152575
  have hstable : (prefixWord ++ tailWord_5152575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152575).length < 2 ^ (prefixWord ++ tailWord_5152575).sum := by decide
  have hdescent : baseEnd_5152575 < baseStart_5152575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152585 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 1, 4]
def baseStart_5152585 : Nat := 118140960795 + 5152585 * 2 ^ 59
def prefixEnd_5152585 : Nat := 4983230072969 + 3 ^ 40 * 5152585 * 2
def baseEnd_5152585 : Nat := 881917572715609407063733

theorem tailTrace_5152585 : CollatzResearch.WordTrace tailWord_5152585 prefixEnd_5152585 881917572715609407063733 := by
  unfold tailWord_5152585
  simp only [CollatzResearch.WordTrace]
  refine ⟨187930214038072011303411209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125286809358714674202274139 187930214038072011303411209)
  ·
    refine ⟨140947660528554008477558407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187930214038072011303411209 140947660528554008477558407)
    ·
      refine ⟨211421490792831012716337611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140947660528554008477558407 211421490792831012716337611)
      ·
        refine ⟨317132236189246519074506417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211421490792831012716337611 317132236189246519074506417)
        ·
          refine ⟨237849177141934889305879813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317132236189246519074506417 237849177141934889305879813)
          ·
            refine ⟨44596720714112791744852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237849177141934889305879813 44596720714112791744852465)
            ·
              refine ⟨33447540535584593808639349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44596720714112791744852465 33447540535584593808639349)
              ·
                refine ⟨3135706925211055669559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33447540535584593808639349 3135706925211055669559939)
                ·
                  refine ⟨4703560387816583504339909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135706925211055669559939 4703560387816583504339909)
                  ·
                    refine ⟨881917572715609407063733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703560387816583504339909 881917572715609407063733)
                    ·
                      rfl

theorem cell23_5152585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_5152585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152585 prefixEnd_5152585 := by exact prefixLift 5152585
  have htrace : WordTrace (prefixWord ++ tailWord_5152585) baseStart_5152585 baseEnd_5152585 := by
    simpa [prefixWord, tailWord_5152585, baseEnd_5152585] using wordTrace_append hprefix tailTrace_5152585
  have hstable : (prefixWord ++ tailWord_5152585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152585).length < 2 ^ (prefixWord ++ tailWord_5152585).sum := by decide
  have hdescent : baseEnd_5152585 < baseStart_5152585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152601 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_5152601 : Nat := 118140960795 + 5152601 * 2 ^ 59
def prefixEnd_5152601 : Nat := 4983230072969 + 3 ^ 40 * 5152601 * 2
def baseEnd_5152601 : Nat := 2645760933837300158591125

theorem tailTrace_5152601 : CollatzResearch.WordTrace tailWord_5152601 prefixEnd_5152601 2645760933837300158591125 := by
  unfold tailWord_5152601
  simp only [CollatzResearch.WordTrace]
  refine ⟨187930797606014046035993657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125287198404009364023995771 187930797606014046035993657)
  ·
    refine ⟨140948098204510534526995243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187930797606014046035993657 140948098204510534526995243)
    ·
      refine ⟨211422147306765801790492865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140948098204510534526995243 211422147306765801790492865)
      ·
        refine ⟨158566610480074351342869649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211422147306765801790492865 158566610480074351342869649)
        ·
          refine ⟨118924957860055763507152237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158566610480074351342869649 118924957860055763507152237)
          ·
            refine ⟨44596859197520911315182089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118924957860055763507152237 44596859197520911315182089)
            ·
              refine ⟨33447644398140683486386567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44596859197520911315182089 33447644398140683486386567)
              ·
                refine ⟨50171466597211025229579851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33447644398140683486386567 50171466597211025229579851)
                ·
                  refine ⟨75257199895816537844369777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50171466597211025229579851 75257199895816537844369777)
                  ·
                    refine ⟨56442899921862403383277333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75257199895816537844369777 56442899921862403383277333)
                    ·
                      refine ⟨2645760933837300158591125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56442899921862403383277333 2645760933837300158591125)
                      ·
                        rfl

theorem cell23_5152601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_5152601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152601 prefixEnd_5152601 := by exact prefixLift 5152601
  have htrace : WordTrace (prefixWord ++ tailWord_5152601) baseStart_5152601 baseEnd_5152601 := by
    simpa [prefixWord, tailWord_5152601, baseEnd_5152601] using wordTrace_append hprefix tailTrace_5152601
  have hstable : (prefixWord ++ tailWord_5152601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152601).length < 2 ^ (prefixWord ++ tailWord_5152601).sum := by decide
  have hdescent : baseEnd_5152601 < baseStart_5152601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152625 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_5152625 : Nat := 118140960795 + 5152625 * 2 ^ 59
def prefixEnd_5152625 : Nat := 4983230072969 + 3 ^ 40 * 5152625 * 2
def baseEnd_5152625 : Nat := 2645773257373008064691015

theorem tailTrace_5152625 : CollatzResearch.WordTrace tailWord_5152625 prefixEnd_5152625 2645773257373008064691015 := by
  unfold tailWord_5152625
  simp only [CollatzResearch.WordTrace]
  refine ⟨187931672957927098134867329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125287781971951398756578219 187931672957927098134867329)
  ·
    refine ⟨140948754718445323601150497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187931672957927098134867329 140948754718445323601150497)
    ·
      refine ⟨105711566038833992700862873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140948754718445323601150497 105711566038833992700862873)
      ·
        refine ⟨79283674529125494525647155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105711566038833992700862873 79283674529125494525647155)
        ·
          refine ⟨118925511793688241788470733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79283674529125494525647155 118925511793688241788470733)
          ·
            refine ⟨44597066922633090670676525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118925511793688241788470733 44597066922633090670676525)
            ·
              refine ⟨16723900095987409001503697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44597066922633090670676525 16723900095987409001503697)
              ·
                refine ⟨12542925071990556751127773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723900095987409001503697 12542925071990556751127773)
                ·
                  refine ⟨4703596901996458781672915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12542925071990556751127773 4703596901996458781672915)
                  ·
                    refine ⟨7055395352994688172509373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703596901996458781672915 7055395352994688172509373)
                    ·
                      refine ⟨2645773257373008064691015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055395352994688172509373 2645773257373008064691015)
                      ·
                        rfl

theorem cell23_5152625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_5152625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152625 prefixEnd_5152625 := by exact prefixLift 5152625
  have htrace : WordTrace (prefixWord ++ tailWord_5152625) baseStart_5152625 baseEnd_5152625 := by
    simpa [prefixWord, tailWord_5152625, baseEnd_5152625] using wordTrace_append hprefix tailTrace_5152625
  have hstable : (prefixWord ++ tailWord_5152625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152625).length < 2 ^ (prefixWord ++ tailWord_5152625).sum := by decide
  have hdescent : baseEnd_5152625 < baseStart_5152625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152702 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_5152702 : Nat := 118140960795 + 5152702 * 2 ^ 59
def prefixEnd_5152702 : Nat := 4983230072969 + 3 ^ 40 * 5152702 * 2
def baseEnd_5152702 : Nat := 2645812795383404263428161

theorem tailTrace_5152702 : CollatzResearch.WordTrace tailWord_5152702 prefixEnd_5152702 2645812795383404263428161 := by
  unfold tailWord_5152702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491810172331017535677545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125289654252432093523613573 23491810172331017535677545)
  ·
    refine ⟨17618857629248263151758159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23491810172331017535677545 17618857629248263151758159)
    ·
      refine ⟨26428286443872394727637239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17618857629248263151758159 26428286443872394727637239)
      ·
        refine ⟨39642429665808592091455859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26428286443872394727637239 39642429665808592091455859)
        ·
          refine ⟨59463644498712888137183789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39642429665808592091455859 59463644498712888137183789)
          ·
            refine ⟨22298866687017333051443921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59463644498712888137183789 22298866687017333051443921)
            ·
              refine ⟨16724150015262999788582941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22298866687017333051443921 16724150015262999788582941)
              ·
                refine ⟨6271556255723624920718603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16724150015262999788582941 6271556255723624920718603)
                ·
                  refine ⟨9407334383585437381077905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271556255723624920718603 9407334383585437381077905)
                  ·
                    refine ⟨7055500787689078035808429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9407334383585437381077905 7055500787689078035808429)
                    ·
                      refine ⟨2645812795383404263428161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055500787689078035808429 2645812795383404263428161)
                      ·
                        rfl

theorem cell23_5152702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_5152702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152702 prefixEnd_5152702 := by exact prefixLift 5152702
  have htrace : WordTrace (prefixWord ++ tailWord_5152702) baseStart_5152702 baseEnd_5152702 := by
    simpa [prefixWord, tailWord_5152702, baseEnd_5152702] using wordTrace_append hprefix tailTrace_5152702
  have hstable : (prefixWord ++ tailWord_5152702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152702).length < 2 ^ (prefixWord ++ tailWord_5152702).sum := by decide
  have hdescent : baseEnd_5152702 < baseStart_5152702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152715 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 3]
def baseStart_5152715 : Nat := 118140960795 + 5152715 * 2 ^ 59
def prefixEnd_5152715 : Nat := 4983230072969 + 3 ^ 40 * 5152715 * 2
def baseEnd_5152715 : Nat := 2645819470631912712565601

theorem tailTrace_5152715 : CollatzResearch.WordTrace tailWord_5152715 prefixEnd_5152715 2645819470631912712565601 := by
  unfold tailWord_5152715
  simp only [CollatzResearch.WordTrace]
  refine ⟨187934955527601043505643599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125289970351734029003762399 187934955527601043505643599)
  ·
    refine ⟨281902433291401565258465399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187934955527601043505643599 281902433291401565258465399)
    ·
      refine ⟨422853649937102347887698099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281902433291401565258465399 422853649937102347887698099)
      ·
        refine ⟨634280474905653521831547149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422853649937102347887698099 634280474905653521831547149)
        ·
          refine ⟨237855178089620070686830181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634280474905653521831547149 237855178089620070686830181)
          ·
            refine ⟨44597845891803763253780659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237855178089620070686830181 44597845891803763253780659)
            ·
              refine ⟨66896768837705644880670989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44597845891803763253780659 66896768837705644880670989)
              ·
                refine ⟨25086288314139616830251621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66896768837705644880670989 25086288314139616830251621)
                ·
                  refine ⟨4703679058901178155672179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25086288314139616830251621 4703679058901178155672179)
                  ·
                    refine ⟨7055518588351767233508269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703679058901178155672179 7055518588351767233508269)
                    ·
                      refine ⟨2645819470631912712565601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055518588351767233508269 2645819470631912712565601)
                      ·
                        rfl

theorem cell23_5152715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 3].length) (baseStart_5152715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152715 prefixEnd_5152715 := by exact prefixLift 5152715
  have htrace : WordTrace (prefixWord ++ tailWord_5152715) baseStart_5152715 baseEnd_5152715 := by
    simpa [prefixWord, tailWord_5152715, baseEnd_5152715] using wordTrace_append hprefix tailTrace_5152715
  have hstable : (prefixWord ++ tailWord_5152715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152715).length < 2 ^ (prefixWord ++ tailWord_5152715).sum := by decide
  have hdescent : baseEnd_5152715 < baseStart_5152715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152718 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_5152718 : Nat := 118140960795 + 5152718 * 2 ^ 59
def prefixEnd_5152718 : Nat := 4983230072969 + 3 ^ 40 * 5152718 * 2
def baseEnd_5152718 : Nat := 881940337024625400276029

theorem tailTrace_5152718 : CollatzResearch.WordTrace tailWord_5152718 prefixEnd_5152718 881940337024625400276029 := by
  unfold tailWord_5152718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491883118323771877250351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125290043297726783345335205 23491883118323771877250351)
  ·
    refine ⟨35237824677485657815875527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23491883118323771877250351 35237824677485657815875527)
    ·
      refine ⟨52856737016228486723813291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35237824677485657815875527 52856737016228486723813291)
      ·
        refine ⟨79285105524342730085719937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52856737016228486723813291 79285105524342730085719937)
        ·
          refine ⟨59463829143257047564289953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79285105524342730085719937 59463829143257047564289953)
          ·
            refine ⟨44597871857442785673217465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59463829143257047564289953 44597871857442785673217465)
            ·
              refine ⟨33448403893082089254913099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44597871857442785673217465 33448403893082089254913099)
              ·
                refine ⟨50172605839623133882369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33448403893082089254913099 50172605839623133882369649)
                ·
                  refine ⟨37629454379717350411777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50172605839623133882369649 37629454379717350411777237)
                  ·
                    refine ⟨881940337024625400276029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37629454379717350411777237 881940337024625400276029)
                    ·
                      rfl

theorem cell23_5152718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_5152718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152718 prefixEnd_5152718 := by exact prefixLift 5152718
  have htrace : WordTrace (prefixWord ++ tailWord_5152718) baseStart_5152718 baseEnd_5152718 := by
    simpa [prefixWord, tailWord_5152718, baseEnd_5152718] using wordTrace_append hprefix tailTrace_5152718
  have hstable : (prefixWord ++ tailWord_5152718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152718).length < 2 ^ (prefixWord ++ tailWord_5152718).sum := by decide
  have hdescent : baseEnd_5152718 < baseStart_5152718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152749 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5152749 : Nat := 118140960795 + 5152749 * 2 ^ 59
def prefixEnd_5152749 : Nat := 4983230072969 + 3 ^ 40 * 5152749 * 2
def baseEnd_5152749 : Nat := 2645836928974165579540445

theorem tailTrace_5152749 : CollatzResearch.WordTrace tailWord_5152749 prefixEnd_5152749 2645836928974165579540445 := by
  unfold tailWord_5152749
  simp only [CollatzResearch.WordTrace]
  refine ⟨187936195609477867312381301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125290797072985244874920867 187936195609477867312381301)
  ·
    refine ⟨17619018338388550060535747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187936195609477867312381301 17619018338388550060535747)
    ·
      refine ⟨26428527507582825090803621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17619018338388550060535747 26428527507582825090803621)
      ·
        refine ⟨4955348907671779704525679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26428527507582825090803621 4955348907671779704525679)
        ·
          refine ⟨7433023361507669556788519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955348907671779704525679 7433023361507669556788519)
          ·
            refine ⟨11149535042261504335182779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433023361507669556788519 11149535042261504335182779)
            ·
              refine ⟨16724302563392256502774169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11149535042261504335182779 16724302563392256502774169)
              ·
                refine ⟨12543226922544192377080627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16724302563392256502774169 12543226922544192377080627)
                ·
                  refine ⟨18814840383816288565620941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12543226922544192377080627 18814840383816288565620941)
                  ·
                    refine ⟨7055565143931108212107853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18814840383816288565620941 7055565143931108212107853)
                    ·
                      refine ⟨2645836928974165579540445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055565143931108212107853 2645836928974165579540445)
                      ·
                        rfl

theorem cell23_5152749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5152749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152749 prefixEnd_5152749 := by exact prefixLift 5152749
  have htrace : WordTrace (prefixWord ++ tailWord_5152749) baseStart_5152749 baseEnd_5152749 := by
    simpa [prefixWord, tailWord_5152749, baseEnd_5152749] using wordTrace_append hprefix tailTrace_5152749
  have hstable : (prefixWord ++ tailWord_5152749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152749).length < 2 ^ (prefixWord ++ tailWord_5152749).sum := by decide
  have hdescent : baseEnd_5152749 < baseStart_5152749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152766 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5152766 : Nat := 118140960795 + 5152766 * 2 ^ 59
def prefixEnd_5152766 : Nat := 4983230072969 + 3 ^ 40 * 5152766 * 2
def baseEnd_5152766 : Nat := 2645845658145292013027867

theorem tailTrace_5152766 : CollatzResearch.WordTrace tailWord_5152766 prefixEnd_5152766 2645845658145292013027867 := by
  unfold tailWord_5152766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492101956302034901968769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125291210433610852810500101 23492101956302034901968769)
  ·
    refine ⟨17619076467226526176476577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23492101956302034901968769 17619076467226526176476577)
    ·
      refine ⟨13214307350419894632357433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17619076467226526176476577 13214307350419894632357433)
      ·
        refine ⟨9910730512814920974268075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13214307350419894632357433 9910730512814920974268075)
        ·
          refine ⟨14866095769222381461402113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910730512814920974268075 14866095769222381461402113)
          ·
            refine ⟨11149571826916786096051585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14866095769222381461402113 11149571826916786096051585)
            ·
              refine ⟨8362178870187589572038689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11149571826916786096051585 8362178870187589572038689)
              ·
                refine ⟨6271634152640692179029017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8362178870187589572038689 6271634152640692179029017)
                ·
                  refine ⟨4703725614480519134271763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6271634152640692179029017 4703725614480519134271763)
                  ·
                    refine ⟨7055588421720778701407645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703725614480519134271763 7055588421720778701407645)
                    ·
                      refine ⟨2645845658145292013027867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055588421720778701407645 2645845658145292013027867)
                      ·
                        rfl

theorem cell23_5152766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5152766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152766 prefixEnd_5152766 := by exact prefixLift 5152766
  have htrace : WordTrace (prefixWord ++ tailWord_5152766) baseStart_5152766 baseEnd_5152766 := by
    simpa [prefixWord, tailWord_5152766, baseEnd_5152766] using wordTrace_append hprefix tailTrace_5152766
  have hstable : (prefixWord ++ tailWord_5152766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152766).length < 2 ^ (prefixWord ++ tailWord_5152766).sum := by decide
  have hdescent : baseEnd_5152766 < baseStart_5152766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152775 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5152775 : Nat := 118140960795 + 5152775 * 2 ^ 59
def prefixEnd_5152775 : Nat := 4983230072969 + 3 ^ 40 * 5152775 * 2
def baseEnd_5152775 : Nat := 2645850279471182477815325

theorem tailTrace_5152775 : CollatzResearch.WordTrace tailWord_5152775 prefixEnd_5152775 2645850279471182477815325 := by
  unfold tailWord_5152775
  simp only [CollatzResearch.WordTrace]
  refine ⟨187937143907383673752827779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125291429271589115835218519 187937143907383673752827779)
  ·
    refine ⟨281905715861075510629241669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187937143907383673752827779 281905715861075510629241669)
    ·
      refine ⟨52857321723951658242982813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281905715861075510629241669 52857321723951658242982813)
      ·
        refine ⟨19821495646481871841118555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52857321723951658242982813 19821495646481871841118555)
        ·
          refine ⟨29732243469722807761677833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19821495646481871841118555 29732243469722807761677833)
          ·
            refine ⟨22299182602292105821258375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29732243469722807761677833 22299182602292105821258375)
            ·
              refine ⟨33448773903438158731887563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22299182602292105821258375 33448773903438158731887563)
              ·
                refine ⟨50173160855157238097831345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33448773903438158731887563 50173160855157238097831345)
                ·
                  refine ⟨37629870641367928573373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50173160855157238097831345 37629870641367928573373509)
                  ·
                    refine ⟨7055600745256486607507533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37629870641367928573373509 7055600745256486607507533)
                    ·
                      refine ⟨2645850279471182477815325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055600745256486607507533 2645850279471182477815325)
                      ·
                        rfl

theorem cell23_5152775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5152775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152775 prefixEnd_5152775 := by exact prefixLift 5152775
  have htrace : WordTrace (prefixWord ++ tailWord_5152775) baseStart_5152775 baseEnd_5152775 := by
    simpa [prefixWord, tailWord_5152775, baseEnd_5152775] using wordTrace_append hprefix tailTrace_5152775
  have hstable : (prefixWord ++ tailWord_5152775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152775).length < 2 ^ (prefixWord ++ tailWord_5152775).sum := by decide
  have hdescent : baseEnd_5152775 < baseStart_5152775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152789 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_5152789 : Nat := 118140960795 + 5152789 * 2 ^ 59
def prefixEnd_5152789 : Nat := 4983230072969 + 3 ^ 40 * 5152789 * 2
def baseEnd_5152789 : Nat := 2645857468200345423040261

theorem tailTrace_5152789 : CollatzResearch.WordTrace tailWord_5152789 prefixEnd_5152789 2645857468200345423040261 := by
  unfold tailWord_5152789
  simp only [CollatzResearch.WordTrace]
  refine ⟨187937654529332954143837421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125291769686221969429224947 187937654529332954143837421)
  ·
    refine ⟨70476620448499857803939033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187937654529332954143837421 70476620448499857803939033)
    ·
      refine ⟨52857465336374893352954275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70476620448499857803939033 52857465336374893352954275)
      ·
        refine ⟨79286198004562340029431413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52857465336374893352954275 79286198004562340029431413)
        ·
          refine ⟨7433081062927719377759195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79286198004562340029431413 7433081062927719377759195)
          ·
            refine ⟨11149621594391579066638793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433081062927719377759195 11149621594391579066638793)
            ·
              refine ⟨8362216195793684299979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11149621594391579066638793 8362216195793684299979095)
              ·
                refine ⟨12543324293690526449968643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8362216195793684299979095 12543324293690526449968643)
                ·
                  refine ⟨18814986440535789674952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12543324293690526449968643 18814986440535789674952965)
                  ·
                    refine ⟨3527809957600460564053681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18814986440535789674952965 3527809957600460564053681)
                    ·
                      refine ⟨2645857468200345423040261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527809957600460564053681 2645857468200345423040261)
                      ·
                        rfl

theorem cell23_5152789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_5152789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152789 prefixEnd_5152789 := by exact prefixLift 5152789
  have htrace : WordTrace (prefixWord ++ tailWord_5152789) baseStart_5152789 baseEnd_5152789 := by
    simpa [prefixWord, tailWord_5152789, baseEnd_5152789] using wordTrace_append hprefix tailTrace_5152789
  have hstable : (prefixWord ++ tailWord_5152789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152789).length < 2 ^ (prefixWord ++ tailWord_5152789).sum := by decide
  have hdescent : baseEnd_5152789 < baseStart_5152789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152815 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 7, 2]
def baseStart_5152815 : Nat := 118140960795 + 5152815 * 2 ^ 59
def prefixEnd_5152815 : Nat := 4983230072969 + 3 ^ 40 * 5152815 * 2
def baseEnd_5152815 : Nat := 2645870818697362321315141

theorem tailTrace_5152815 : CollatzResearch.WordTrace tailWord_5152815 prefixEnd_5152815 2645870818697362321315141 := by
  unfold tailWord_5152815
  simp only [CollatzResearch.WordTrace]
  refine ⟨187938602827238760584283899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125292401884825840389522599 187938602827238760584283899)
  ·
    refine ⟨281907904240858140876425849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187938602827238760584283899 281907904240858140876425849)
    ·
      refine ⟨211430928180643605657319387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281907904240858140876425849 211430928180643605657319387)
      ·
        refine ⟨317146392270965408485979081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211430928180643605657319387 317146392270965408485979081)
        ·
          refine ⟨237859794203224056364484311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317146392270965408485979081 237859794203224056364484311)
          ·
            refine ⟨356789691304836084546726467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237859794203224056364484311 356789691304836084546726467)
            ·
              refine ⟨535184536957254126820089701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356789691304836084546726467 535184536957254126820089701)
              ·
                refine ⟨100347100679485148778766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535184536957254126820089701 100347100679485148778766819)
                ·
                  refine ⟨150520651019227723168150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100347100679485148778766819 150520651019227723168150229)
                  ·
                    refine ⟨3527827758263149761753521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150520651019227723168150229 3527827758263149761753521)
                    ·
                      refine ⟨2645870818697362321315141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527827758263149761753521 2645870818697362321315141)
                      ·
                        rfl

theorem cell23_5152815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7, 2].length) (baseStart_5152815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152815 prefixEnd_5152815 := by exact prefixLift 5152815
  have htrace : WordTrace (prefixWord ++ tailWord_5152815) baseStart_5152815 baseEnd_5152815 := by
    simpa [prefixWord, tailWord_5152815, baseEnd_5152815] using wordTrace_append hprefix tailTrace_5152815
  have hstable : (prefixWord ++ tailWord_5152815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152815).length < 2 ^ (prefixWord ++ tailWord_5152815).sum := by decide
  have hdescent : baseEnd_5152815 < baseStart_5152815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152822 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5152822 : Nat := 118140960795 + 5152822 * 2 ^ 59
def prefixEnd_5152822 : Nat := 4983230072969 + 3 ^ 40 * 5152822 * 2
def baseEnd_5152822 : Nat := 2645874413061943793927609

theorem tailTrace_5152822 : CollatzResearch.WordTrace tailWord_5152822 prefixEnd_5152822 2645874413061943793927609 := by
  unfold tailWord_5152822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746178633638337548736795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125292572092142267186525813 11746178633638337548736795)
  ·
    refine ⟨17619267950457506323105193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11746178633638337548736795 17619267950457506323105193)
    ·
      refine ⟨13214450962843129742328895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17619267950457506323105193 13214450962843129742328895)
      ·
        refine ⟨19821676444264694613493343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13214450962843129742328895 19821676444264694613493343)
        ·
          refine ⟨29732514666397041920240015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19821676444264694613493343 29732514666397041920240015)
          ·
            refine ⟨44598771999595562880360023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29732514666397041920240015 44598771999595562880360023)
            ·
              refine ⟨66898157999393344320540035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44598771999595562880360023 66898157999393344320540035)
              ·
                refine ⟨100347236999090016480810053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66898157999393344320540035 100347236999090016480810053)
                ·
                  refine ⟨18815106937329378090151885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100347236999090016480810053 18815106937329378090151885)
                  ·
                    refine ⟨7055665101498516783806957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18815106937329378090151885 7055665101498516783806957)
                    ·
                      refine ⟨2645874413061943793927609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055665101498516783806957 2645874413061943793927609)
                      ·
                        rfl

theorem cell23_5152822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5152822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152822 prefixEnd_5152822 := by exact prefixLift 5152822
  have htrace : WordTrace (prefixWord ++ tailWord_5152822) baseStart_5152822 baseEnd_5152822 := by
    simpa [prefixWord, tailWord_5152822, baseEnd_5152822] using wordTrace_append hprefix tailTrace_5152822
  have hstable : (prefixWord ++ tailWord_5152822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152822).length < 2 ^ (prefixWord ++ tailWord_5152822).sum := by decide
  have hdescent : baseEnd_5152822 < baseStart_5152822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152882 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5152882 : Nat := 118140960795 + 5152882 * 2 ^ 59
def prefixEnd_5152882 : Nat := 4983230072969 + 3 ^ 40 * 5152882 * 2
def baseEnd_5152882 : Nat := 2645905221901213559177333

theorem tailTrace_5152882 : CollatzResearch.WordTrace tailWord_5152882 prefixEnd_5152882 2645905221901213559177333 := by
  unfold tailWord_5152882
  simp only [CollatzResearch.WordTrace]
  refine ⟨46985261629499007756743225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125294031011997354017981933 46985261629499007756743225)
  ·
    refine ⟨35238946222124255817557419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46985261629499007756743225 35238946222124255817557419)
    ·
      refine ⟨52858419333186383726336129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35238946222124255817557419 52858419333186383726336129)
      ·
        refine ⟨39643814499889787794752097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52858419333186383726336129 39643814499889787794752097)
        ·
          refine ⟨29732860874917340846064073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39643814499889787794752097 29732860874917340846064073)
          ·
            refine ⟨22299645656188005634548055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29732860874917340846064073 22299645656188005634548055)
            ·
              refine ⟨33449468484282008451822083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22299645656188005634548055 33449468484282008451822083)
              ·
                refine ⟨50174202726423012677733125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33449468484282008451822083 50174202726423012677733125)
                ·
                  refine ⟨9407663011204314877074961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50174202726423012677733125 9407663011204314877074961)
                  ·
                    refine ⟨7055747258403236157806221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9407663011204314877074961 7055747258403236157806221)
                    ·
                      refine ⟨2645905221901213559177333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055747258403236157806221 2645905221901213559177333)
                      ·
                        rfl

theorem cell23_5152882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5152882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152882 prefixEnd_5152882 := by exact prefixLift 5152882
  have htrace : WordTrace (prefixWord ++ tailWord_5152882) baseStart_5152882 baseEnd_5152882 := by
    simpa [prefixWord, tailWord_5152882, baseEnd_5152882] using wordTrace_append hprefix tailTrace_5152882
  have hstable : (prefixWord ++ tailWord_5152882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152882).length < 2 ^ (prefixWord ++ tailWord_5152882).sum := by decide
  have hdescent : baseEnd_5152882 < baseStart_5152882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152889 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_5152889 : Nat := 118140960795 + 5152889 * 2 ^ 59
def prefixEnd_5152889 : Nat := 4983230072969 + 3 ^ 40 * 5152889 * 2
def baseEnd_5152889 : Nat := 881969605421931677263267

theorem tailTrace_5152889 : CollatzResearch.WordTrace tailWord_5152889 prefixEnd_5152889 881969605421931677263267 := by
  unfold tailWord_5152889
  simp only [CollatzResearch.WordTrace]
  refine ⟨187941301828970671222477721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125294201219313780814985147 187941301828970671222477721)
  ·
    refine ⟨140955976371728003416858291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187941301828970671222477721 140955976371728003416858291)
    ·
      refine ⟨211433964557592005125287437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140955976371728003416858291 211433964557592005125287437)
      ·
        refine ⟨79287736709097001921982789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211433964557592005125287437 79287736709097001921982789)
        ·
          refine ⟨14866450632955687860371773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79287736709097001921982789 14866450632955687860371773)
          ·
            refine ⟨5574918987358382947639415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14866450632955687860371773 5574918987358382947639415)
            ·
              refine ⟨8362378481037574421459123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574918987358382947639415 8362378481037574421459123)
              ·
                refine ⟨12543567721556361632188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8362378481037574421459123 12543567721556361632188685)
                ·
                  refine ⟨4703837895583635612070757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12543567721556361632188685 4703837895583635612070757)
                  ·
                    refine ⟨881969605421931677263267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703837895583635612070757 881969605421931677263267)
                    ·
                      rfl

theorem cell23_5152889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_5152889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152889 prefixEnd_5152889 := by exact prefixLift 5152889
  have htrace : WordTrace (prefixWord ++ tailWord_5152889) baseStart_5152889 baseEnd_5152889 := by
    simpa [prefixWord, tailWord_5152889, baseEnd_5152889] using wordTrace_append hprefix tailTrace_5152889
  have hstable : (prefixWord ++ tailWord_5152889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152889).length < 2 ^ (prefixWord ++ tailWord_5152889).sum := by decide
  have hdescent : baseEnd_5152889 < baseStart_5152889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152912 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_5152912 : Nat := 118140960795 + 5152912 * 2 ^ 59
def prefixEnd_5152912 : Nat := 4983230072969 + 3 ^ 40 * 5152912 * 2
def baseEnd_5152912 : Nat := 2645920626320848441802195

theorem tailTrace_5152912 : CollatzResearch.WordTrace tailWord_5152912 prefixEnd_5152912 2645920626320848441802195 := by
  unfold tailWord_5152912
  simp only [CollatzResearch.WordTrace]
  refine ⟨93971070353943673075282495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125294760471924897433709993 93971070353943673075282495)
  ·
    refine ⟨140956605530915509612923743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93971070353943673075282495 140956605530915509612923743)
    ·
      refine ⟨211434908296373264419385615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140956605530915509612923743 211434908296373264419385615)
      ·
        refine ⟨317152362444559896629078423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211434908296373264419385615 317152362444559896629078423)
        ·
          refine ⟨475728543666839844943617635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317152362444559896629078423 475728543666839844943617635)
          ·
            refine ⟨713592815500259767415426453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475728543666839844943617635 713592815500259767415426453)
            ·
              refine ⟨33449663226574676597598115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 713592815500259767415426453 33449663226574676597598115)
              ·
                refine ⟨50174494839862014896397173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33449663226574676597598115 50174494839862014896397173)
                ·
                  refine ⟨4703858891237063896537235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50174494839862014896397173 4703858891237063896537235)
                  ·
                    refine ⟨7055788336855595844805853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703858891237063896537235 7055788336855595844805853)
                    ·
                      refine ⟨2645920626320848441802195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055788336855595844805853 2645920626320848441802195)
                      ·
                        rfl

theorem cell23_5152912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_5152912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152912 prefixEnd_5152912 := by exact prefixLift 5152912
  have htrace : WordTrace (prefixWord ++ tailWord_5152912) baseStart_5152912 baseEnd_5152912 := by
    simpa [prefixWord, tailWord_5152912, baseEnd_5152912] using wordTrace_append hprefix tailTrace_5152912
  have hstable : (prefixWord ++ tailWord_5152912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152912).length < 2 ^ (prefixWord ++ tailWord_5152912).sum := by decide
  have hdescent : baseEnd_5152912 < baseStart_5152912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152946 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_5152946 : Nat := 118140960795 + 5152946 * 2 ^ 59
def prefixEnd_5152946 : Nat := 4983230072969 + 3 ^ 40 * 5152946 * 2
def baseEnd_5152946 : Nat := 2645938084663101308777039

theorem tailTrace_5152946 : CollatzResearch.WordTrace tailWord_5152946 prefixEnd_5152946 2645938084663101308777039 := by
  unfold tailWord_5152946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46985845197441042489325673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125295587193176113304868461 46985845197441042489325673)
  ·
    refine ⟨35239383898080781866994255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46985845197441042489325673 35239383898080781866994255)
    ·
      refine ⟨52859075847121172800491383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35239383898080781866994255 52859075847121172800491383)
      ·
        refine ⟨79288613770681759200737075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52859075847121172800491383 79288613770681759200737075)
        ·
          refine ⟨118932920656022638801105613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79288613770681759200737075 118932920656022638801105613)
          ·
            refine ⟨44599845246008489550414605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118932920656022638801105613 44599845246008489550414605)
            ·
              refine ⟨16724941967253183581405477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44599845246008489550414605 16724941967253183581405477)
              ·
                refine ⟨3135926618859971921513527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16724941967253183581405477 3135926618859971921513527)
                ·
                  refine ⟨4703889928289957882270291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135926618859971921513527 4703889928289957882270291)
                  ·
                    refine ⟨7055834892434936823405437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4703889928289957882270291 7055834892434936823405437)
                    ·
                      refine ⟨2645938084663101308777039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7055834892434936823405437 2645938084663101308777039)
                      ·
                        rfl

theorem cell23_5152946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_5152946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152946 prefixEnd_5152946 := by exact prefixLift 5152946
  have htrace : WordTrace (prefixWord ++ tailWord_5152946) baseStart_5152946 baseEnd_5152946 := by
    simpa [prefixWord, tailWord_5152946, baseEnd_5152946] using wordTrace_append hprefix tailTrace_5152946
  have hstable : (prefixWord ++ tailWord_5152946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152946).length < 2 ^ (prefixWord ++ tailWord_5152946).sum := by decide
  have hdescent : baseEnd_5152946 < baseStart_5152946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152955 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_5152955 : Nat := 118140960795 + 5152955 * 2 ^ 59
def prefixEnd_5152955 : Nat := 4983230072969 + 3 ^ 40 * 5152955 * 2
def baseEnd_5152955 : Nat := 2645942705988991773564497

theorem tailTrace_5152955 : CollatzResearch.WordTrace tailWord_5152955 prefixEnd_5152955 2645942705988991773564497 := by
  unfold tailWord_5152955
  simp only [CollatzResearch.WordTrace]
  refine ⟨187943709046731564494380319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125295806031154376329586879 187943709046731564494380319)
  ·
    refine ⟨281915563570097346741570479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187943709046731564494380319 281915563570097346741570479)
    ·
      refine ⟨422873345355146020112355719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281915563570097346741570479 422873345355146020112355719)
      ·
        refine ⟨634310018032719030168533579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422873345355146020112355719 634310018032719030168533579)
        ·
          refine ⟨951465027049078545252800369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634310018032719030168533579 951465027049078545252800369)
          ·
            refine ⟨713598770286808908939600277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951465027049078545252800369 713598770286808908939600277)
            ·
              refine ⟨33449942357194167606543763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 713598770286808908939600277 33449942357194167606543763)
              ·
                refine ⟨50174913535791251409815645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33449942357194167606543763 50174913535791251409815645)
                ·
                  refine ⟨18815592575921719278680867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50174913535791251409815645 18815592575921719278680867)
                  ·
                    refine ⟨28223388863882578918021301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18815592575921719278680867 28223388863882578918021301)
                    ·
                      refine ⟨2645942705988991773564497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28223388863882578918021301 2645942705988991773564497)
                      ·
                        rfl

theorem cell23_5152955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_5152955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152955 prefixEnd_5152955 := by exact prefixLift 5152955
  have htrace : WordTrace (prefixWord ++ tailWord_5152955) baseStart_5152955 baseEnd_5152955 := by
    simpa [prefixWord, tailWord_5152955, baseEnd_5152955] using wordTrace_append hprefix tailTrace_5152955
  have hstable : (prefixWord ++ tailWord_5152955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152955).length < 2 ^ (prefixWord ++ tailWord_5152955).sum := by decide
  have hdescent : baseEnd_5152955 < baseStart_5152955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5152965 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_5152965 : Nat := 118140960795 + 5152965 * 2 ^ 59
def prefixEnd_5152965 : Nat := 4983230072969 + 3 ^ 40 * 5152965 * 2
def baseEnd_5152965 : Nat := 2645947840795536734439451

theorem tailTrace_5152965 : CollatzResearch.WordTrace tailWord_5152965 prefixEnd_5152965 2645947840795536734439451 := by
  unfold tailWord_5152965
  simp only [CollatzResearch.WordTrace]
  refine ⟨187944073776695336202244349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125296049184463557468162899 187944073776695336202244349)
  ·
    refine ⟨70479027666260751075841631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187944073776695336202244349 70479027666260751075841631)
    ·
      refine ⟨105718541499391126613762447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70479027666260751075841631 105718541499391126613762447)
      ·
        refine ⟨158577812249086689920643671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105718541499391126613762447 158577812249086689920643671)
        ·
          refine ⟨237866718373630034880965507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158577812249086689920643671 237866718373630034880965507)
          ·
            refine ⟨356800077560445052321448261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237866718373630034880965507 356800077560445052321448261)
            ·
              refine ⟨66900014542583447310271549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356800077560445052321448261 66900014542583447310271549)
              ·
                refine ⟨25087505453468792741351831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66900014542583447310271549 25087505453468792741351831)
                ·
                  refine ⟨37631258180203189112027747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25087505453468792741351831 37631258180203189112027747)
                  ·
                    refine ⟨56446887270304783668041621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37631258180203189112027747 56446887270304783668041621)
                    ·
                      refine ⟨2645947840795536734439451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56446887270304783668041621 2645947840795536734439451)
                      ·
                        rfl

theorem cell23_5152965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_5152965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5152965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5152965 prefixEnd_5152965 := by exact prefixLift 5152965
  have htrace : WordTrace (prefixWord ++ tailWord_5152965) baseStart_5152965 baseEnd_5152965 := by
    simpa [prefixWord, tailWord_5152965, baseEnd_5152965] using wordTrace_append hprefix tailTrace_5152965
  have hstable : (prefixWord ++ tailWord_5152965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5152965).length < 2 ^ (prefixWord ++ tailWord_5152965).sum := by decide
  have hdescent : baseEnd_5152965 < baseStart_5152965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5152965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153015 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_5153015 : Nat := 118140960795 + 5153015 * 2 ^ 59
def prefixEnd_5153015 : Nat := 4983230072969 + 3 ^ 40 * 5153015 * 2
def baseEnd_5153015 : Nat := 2645973514828261538814221

theorem tailTrace_5153015 : CollatzResearch.WordTrace tailWord_5153015 prefixEnd_5153015 2645973514828261538814221 := by
  unfold tailWord_5153015
  simp only [CollatzResearch.WordTrace]
  refine ⟨187945897426514194741564499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125297264951009463161042999 187945897426514194741564499)
  ·
    refine ⟨281918846139771292112346749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187945897426514194741564499 281918846139771292112346749)
    ·
      refine ⟨105719567302414234542130031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281918846139771292112346749 105719567302414234542130031)
      ·
        refine ⟨158579350953621351813195047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105719567302414234542130031 158579350953621351813195047)
        ·
          refine ⟨237869026430432027719792571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158579350953621351813195047 237869026430432027719792571)
          ·
            refine ⟨356803539645648041579688857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237869026430432027719792571 356803539645648041579688857)
            ·
              refine ⟨267602654734236031184766643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356803539645648041579688857 267602654734236031184766643)
              ·
                refine ⟨401403982101354046777149965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267602654734236031184766643 401403982101354046777149965)
                ·
                  refine ⟨150526493288007767541431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401403982101354046777149965 150526493288007767541431237)
                  ·
                    refine ⟨28223717491501456414018357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150526493288007767541431237 28223717491501456414018357)
                    ·
                      refine ⟨2645973514828261538814221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28223717491501456414018357 2645973514828261538814221)
                      ·
                        rfl

theorem cell23_5153015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_5153015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153015 prefixEnd_5153015 := by exact prefixLift 5153015
  have htrace : WordTrace (prefixWord ++ tailWord_5153015) baseStart_5153015 baseEnd_5153015 := by
    simpa [prefixWord, tailWord_5153015, baseEnd_5153015] using wordTrace_append hprefix tailTrace_5153015
  have hstable : (prefixWord ++ tailWord_5153015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153015).length < 2 ^ (prefixWord ++ tailWord_5153015).sum := by decide
  have hdescent : baseEnd_5153015 < baseStart_5153015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153026 : List Nat := [3, 4, 1, 1, 2, 3, 2, 7]
def baseStart_5153026 : Nat := 118140960795 + 5153026 * 2 ^ 59
def prefixEnd_5153026 : Nat := 4983230072969 + 3 ^ 40 * 5153026 * 2
def baseEnd_5153026 : Nat := 97999228263535592436173

theorem tailTrace_5153026 : CollatzResearch.WordTrace tailWord_5153026 prefixEnd_5153026 97999228263535592436173 := by
  unfold tailWord_5153026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46986574657368585905053733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125297532419649562413476621 46986574657368585905053733)
  ·
    refine ⟨8809982748256609857197575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46986574657368585905053733 8809982748256609857197575)
    ·
      refine ⟨13214974122384914785796363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8809982748256609857197575 13214974122384914785796363)
      ·
        refine ⟨19822461183577372178694545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13214974122384914785796363 19822461183577372178694545)
        ·
          refine ⟨14866845887683029134020909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19822461183577372178694545 14866845887683029134020909)
          ·
            refine ⟨5575067207881135925257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14866845887683029134020909 5575067207881135925257841)
            ·
              refine ⟨4181300405910851943943381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575067207881135925257841 4181300405910851943943381)
              ·
                refine ⟨97999228263535592436173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4181300405910851943943381 97999228263535592436173)
                ·
                  rfl

theorem cell23_5153026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_5153026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153026 prefixEnd_5153026 := by exact prefixLift 5153026
  have htrace : WordTrace (prefixWord ++ tailWord_5153026) baseStart_5153026 baseEnd_5153026 := by
    simpa [prefixWord, tailWord_5153026, baseEnd_5153026] using wordTrace_append hprefix tailTrace_5153026
  have hstable : (prefixWord ++ tailWord_5153026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153026).length < 2 ^ (prefixWord ++ tailWord_5153026).sum := by decide
  have hdescent : baseEnd_5153026 < baseStart_5153026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153032 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_5153032 : Nat := 118140960795 + 5153032 * 2 ^ 59
def prefixEnd_5153032 : Nat := 4983230072969 + 3 ^ 40 * 5153032 * 2
def baseEnd_5153032 : Nat := 2645982243999387972301643

theorem tailTrace_5153032 : CollatzResearch.WordTrace tailWord_5153032 prefixEnd_5153032 2645982243999387972301643 := by
  unfold tailWord_5153032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93973258733726303322466675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125297678311635071096622233 93973258733726303322466675)
  ·
    refine ⟨140959888100589454983700013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93973258733726303322466675 140959888100589454983700013)
    ·
      refine ⟨52859958037721045618887505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140959888100589454983700013 52859958037721045618887505)
      ·
        refine ⟨39644968528290784214165629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52859958037721045618887505 39644968528290784214165629)
        ·
          refine ⟨14866863198109044080312111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39644968528290784214165629 14866863198109044080312111)
          ·
            refine ⟨22300294797163566120468167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866863198109044080312111 22300294797163566120468167)
            ·
              refine ⟨33450442195745349180702251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22300294797163566120468167 33450442195745349180702251)
              ·
                refine ⟨50175663293618023771053377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33450442195745349180702251 50175663293618023771053377)
                ·
                  refine ⟨37631747470213517828290033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50175663293618023771053377 37631747470213517828290033)
                  ·
                    refine ⟨28223810602660138371217525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37631747470213517828290033 28223810602660138371217525)
                    ·
                      refine ⟨2645982243999387972301643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28223810602660138371217525 2645982243999387972301643)
                      ·
                        rfl

theorem cell23_5153032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_5153032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153032 prefixEnd_5153032 := by exact prefixLift 5153032
  have htrace : WordTrace (prefixWord ++ tailWord_5153032) baseStart_5153032 baseEnd_5153032 := by
    simpa [prefixWord, tailWord_5153032, baseEnd_5153032] using wordTrace_append hprefix tailTrace_5153032
  have hstable : (prefixWord ++ tailWord_5153032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153032).length < 2 ^ (prefixWord ++ tailWord_5153032).sum := by decide
  have hdescent : baseEnd_5153032 < baseStart_5153032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153054 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5153054 : Nat := 118140960795 + 5153054 * 2 ^ 59
def prefixEnd_5153054 : Nat := 4983230072969 + 3 ^ 40 * 5153054 * 2
def baseEnd_5153054 : Nat := 2645993540573786886226543

theorem tailTrace_5153054 : CollatzResearch.WordTrace tailWord_5153054 prefixEnd_5153054 2645993540573786886226543 := by
  unfold tailWord_5153054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23493414984171613050279277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125298213248915269601489477 23493414984171613050279277)
  ·
    refine ⟨8810030619064354893854729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23493414984171613050279277 8810030619064354893854729)
    ·
      refine ⟨6607522964298266170391047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8810030619064354893854729 6607522964298266170391047)
      ·
        refine ⟨9911284446447399255586571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607522964298266170391047 9911284446447399255586571)
        ·
          refine ⟨14866926669671098883379857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911284446447399255586571 14866926669671098883379857)
          ·
            refine ⟨11150195002253324162534893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14866926669671098883379857 11150195002253324162534893)
            ·
              refine ⟨4181323125844996560950585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11150195002253324162534893 4181323125844996560950585)
              ·
                refine ⟨3135992344383747420712939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181323125844996560950585 3135992344383747420712939)
                ·
                  refine ⟨4703988516575621131069409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135992344383747420712939 4703988516575621131069409)
                  ·
                    refine ⟨3527991387431715848302057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4703988516575621131069409 3527991387431715848302057)
                    ·
                      refine ⟨2645993540573786886226543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3527991387431715848302057 2645993540573786886226543)
                      ·
                        rfl

theorem cell23_5153054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5153054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153054 prefixEnd_5153054 := by exact prefixLift 5153054
  have htrace : WordTrace (prefixWord ++ tailWord_5153054) baseStart_5153054 baseEnd_5153054 := by
    simpa [prefixWord, tailWord_5153054, baseEnd_5153054] using wordTrace_append hprefix tailTrace_5153054
  have hstable : (prefixWord ++ tailWord_5153054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153054).length < 2 ^ (prefixWord ++ tailWord_5153054).sum := by decide
  have hdescent : baseEnd_5153054 < baseStart_5153054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153070 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5153070 : Nat := 118140960795 + 5153070 * 2 ^ 59
def prefixEnd_5153070 : Nat := 4983230072969 + 3 ^ 40 * 5153070 * 2
def baseEnd_5153070 : Nat := 2646001756264258823626469

theorem tailTrace_5153070 : CollatzResearch.WordTrace tailWord_5153070 prefixEnd_5153070 2646001756264258823626469 := by
  unfold tailWord_5153070
  simp only [CollatzResearch.WordTrace]
  refine ⟨23493487930164367391852083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125298602294209959423211109 23493487930164367391852083)
  ·
    refine ⟨35240231895246551087778125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23493487930164367391852083 35240231895246551087778125)
    ·
      refine ⟨13215086960717456657916797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35240231895246551087778125 13215086960717456657916797)
      ·
        refine ⟨4955657610269046246718799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13215086960717456657916797 4955657610269046246718799)
        ·
          refine ⟨7433486415403569370078199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955657610269046246718799 7433486415403569370078199)
          ·
            refine ⟨11150229623105354055117299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433486415403569370078199 11150229623105354055117299)
            ·
              refine ⟨16725344434658031082675949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11150229623105354055117299 16725344434658031082675949)
              ·
                refine ⟨6272004162996761656003481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16725344434658031082675949 6272004162996761656003481)
                ·
                  refine ⟨4704003122247571242002611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272004162996761656003481 4704003122247571242002611)
                  ·
                    refine ⟨7056004683371356863003917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704003122247571242002611 7056004683371356863003917)
                    ·
                      refine ⟨2646001756264258823626469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056004683371356863003917 2646001756264258823626469)
                      ·
                        rfl

theorem cell23_5153070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5153070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153070 prefixEnd_5153070 := by exact prefixLift 5153070
  have htrace : WordTrace (prefixWord ++ tailWord_5153070) baseStart_5153070 baseEnd_5153070 := by
    simpa [prefixWord, tailWord_5153070, baseEnd_5153070] using wordTrace_append hprefix tailTrace_5153070
  have hstable : (prefixWord ++ tailWord_5153070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153070).length < 2 ^ (prefixWord ++ tailWord_5153070).sum := by decide
  have hdescent : baseEnd_5153070 < baseStart_5153070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153112 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_5153112 : Nat := 118140960795 + 5153112 * 2 ^ 59
def prefixEnd_5153112 : Nat := 4983230072969 + 3 ^ 40 * 5153112 * 2
def baseEnd_5153112 : Nat := 882007774150582553100425

theorem tailTrace_5153112 : CollatzResearch.WordTrace tailWord_5153112 prefixEnd_5153112 882007774150582553100425 := by
  unfold tailWord_5153112
  simp only [CollatzResearch.WordTrace]
  refine ⟨93974717653581390153922795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125299623538108520205230393 93974717653581390153922795)
  ·
    refine ⟨140962076480372085230884193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93974717653581390153922795 140962076480372085230884193)
    ·
      refine ⟨105721557360279063923163145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140962076480372085230884193 105721557360279063923163145)
      ·
        refine ⟨79291168020209297942372359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105721557360279063923163145 79291168020209297942372359)
        ·
          refine ⟨118936752030313946913558539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79291168020209297942372359 118936752030313946913558539)
          ·
            refine ⟨178405128045470920370337809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118936752030313946913558539 178405128045470920370337809)
            ·
              refine ⟨133803846034103190277753357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178405128045470920370337809 133803846034103190277753357)
              ·
                refine ⟨50176442262788696354157509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133803846034103190277753357 50176442262788696354157509)
                ·
                  refine ⟨9408082924272880566404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50176442262788696354157509 9408082924272880566404533)
                  ·
                    refine ⟨882007774150582553100425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9408082924272880566404533 882007774150582553100425)
                    ·
                      rfl

theorem cell23_5153112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_5153112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153112 prefixEnd_5153112 := by exact prefixLift 5153112
  have htrace : WordTrace (prefixWord ++ tailWord_5153112) baseStart_5153112 baseEnd_5153112 := by
    simpa [prefixWord, tailWord_5153112, baseEnd_5153112] using wordTrace_append hprefix tailTrace_5153112
  have hstable : (prefixWord ++ tailWord_5153112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153112).length < 2 ^ (prefixWord ++ tailWord_5153112).sum := by decide
  have hdescent : baseEnd_5153112 < baseStart_5153112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153119 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 5, 2]
def baseStart_5153119 : Nat := 118140960795 + 5153119 * 2 ^ 59
def prefixEnd_5153119 : Nat := 4983230072969 + 3 ^ 40 * 5153119 * 2
def baseEnd_5153119 : Nat := 2646026916816329131913743

theorem tailTrace_5153119 : CollatzResearch.WordTrace tailWord_5153119 prefixEnd_5153119 2646026916816329131913743 := by
  unfold tailWord_5153119
  simp only [CollatzResearch.WordTrace]
  refine ⟨187949690618137420503350411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125299793745424947002233607 187949690618137420503350411)
  ·
    refine ⟨281924535927206130755025617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187949690618137420503350411 281924535927206130755025617)
    ·
      refine ⟨211443401945404598066269213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281924535927206130755025617 211443401945404598066269213)
      ·
        refine ⟨79291275729526724274850955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211443401945404598066269213 79291275729526724274850955)
        ·
          refine ⟨118936913594290086412276433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79291275729526724274850955 118936913594290086412276433)
          ·
            refine ⟨89202685195717564809207325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118936913594290086412276433 89202685195717564809207325)
            ·
              refine ⟨33451006948394086803452747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89202685195717564809207325 33451006948394086803452747)
              ·
                refine ⟨50176510422591130205179121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33451006948394086803452747 50176510422591130205179121)
                ·
                  refine ⟨37632382816943347653884341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50176510422591130205179121 37632382816943347653884341)
                  ·
                    refine ⟨3528035889088438842551657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37632382816943347653884341 3528035889088438842551657)
                    ·
                      refine ⟨2646026916816329131913743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528035889088438842551657 2646026916816329131913743)
                      ·
                        rfl

theorem cell23_5153119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_5153119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153119 prefixEnd_5153119 := by exact prefixLift 5153119
  have htrace : WordTrace (prefixWord ++ tailWord_5153119) baseStart_5153119 baseEnd_5153119 := by
    simpa [prefixWord, tailWord_5153119, baseEnd_5153119] using wordTrace_append hprefix tailTrace_5153119
  have hstable : (prefixWord ++ tailWord_5153119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153119).length < 2 ^ (prefixWord ++ tailWord_5153119).sum := by decide
  have hdescent : baseEnd_5153119 < baseStart_5153119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153149 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5153149 : Nat := 118140960795 + 5153149 * 2 ^ 59
def prefixEnd_5153149 : Nat := 4983230072969 + 3 ^ 40 * 5153149 * 2
def baseEnd_5153149 : Nat := 2646042321235964014538605

theorem tailTrace_5153149 : CollatzResearch.WordTrace tailWord_5153149 prefixEnd_5153149 2646042321235964014538605 := by
  unfold tailWord_5153149
  simp only [CollatzResearch.WordTrace]
  refine ⟨187950784808028735626942501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125300523205352490417961667 187950784808028735626942501)
  ·
    refine ⟨35240772151505387930051719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187950784808028735626942501 35240772151505387930051719)
    ·
      refine ⟨52861158227258081895077579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35240772151505387930051719 52861158227258081895077579)
      ·
        refine ⟨79291737340887122842616369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52861158227258081895077579 79291737340887122842616369)
        ·
          refine ⟨59468803005665342131962277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79291737340887122842616369 59468803005665342131962277)
          ·
            refine ⟨11150400563562251649742927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59468803005665342131962277 11150400563562251649742927)
            ·
              refine ⟨16725600845343377474614391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11150400563562251649742927 16725600845343377474614391)
              ·
                refine ⟨25088401268015066211921587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16725600845343377474614391 25088401268015066211921587)
                ·
                  refine ⟨37632601902022599317882381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25088401268015066211921587 37632601902022599317882381)
                  ·
                    refine ⟨14112225713258474744205893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37632601902022599317882381 14112225713258474744205893)
                    ·
                      refine ⟨2646042321235964014538605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14112225713258474744205893 2646042321235964014538605)
                      ·
                        rfl

theorem cell23_5153149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5153149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153149 prefixEnd_5153149 := by exact prefixLift 5153149
  have htrace : WordTrace (prefixWord ++ tailWord_5153149) baseStart_5153149 baseEnd_5153149 := by
    simpa [prefixWord, tailWord_5153149, baseEnd_5153149] using wordTrace_append hprefix tailTrace_5153149
  have hstable : (prefixWord ++ tailWord_5153149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153149).length < 2 ^ (prefixWord ++ tailWord_5153149).sum := by decide
  have hdescent : baseEnd_5153149 < baseStart_5153149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153159 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 5, 4]
def baseStart_5153159 : Nat := 118140960795 + 5153159 * 2 ^ 59
def prefixEnd_5153159 : Nat := 4983230072969 + 3 ^ 40 * 5153159 * 2
def baseEnd_5153159 : Nat := 882015818680836325137853

theorem tailTrace_5153159 : CollatzResearch.WordTrace tailWord_5153159 prefixEnd_5153159 882015818680836325137853 := by
  unfold tailWord_5153159
  simp only [CollatzResearch.WordTrace]
  refine ⟨187951149537992507334806531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125300766358661671556537687 187951149537992507334806531)
  ·
    refine ⟨281926724306988761002209797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187951149537992507334806531 281926724306988761002209797)
    ·
      refine ⟨52861260807560392687914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281926724306988761002209797 52861260807560392687914337)
      ·
        refine ⟨39645945605670294515935753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52861260807560392687914337 39645945605670294515935753)
        ·
          refine ⟨29734459204252720886951815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39645945605670294515935753 29734459204252720886951815)
          ·
            refine ⟨44601688806379081330427723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29734459204252720886951815 44601688806379081330427723)
            ·
              refine ⟨66902533209568621995641585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44601688806379081330427723 66902533209568621995641585)
              ·
                refine ⟨50176899907176466496731189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66902533209568621995641585 50176899907176466496731189)
                ·
                  refine ⟨4704084366297793734068549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50176899907176466496731189 4704084366297793734068549)
                  ·
                    refine ⟨882015818680836325137853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704084366297793734068549 882015818680836325137853)
                    ·
                      rfl

theorem cell23_5153159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_5153159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153159 prefixEnd_5153159 := by exact prefixLift 5153159
  have htrace : WordTrace (prefixWord ++ tailWord_5153159) baseStart_5153159 baseEnd_5153159 := by
    simpa [prefixWord, tailWord_5153159, baseEnd_5153159] using wordTrace_append hprefix tailTrace_5153159
  have hstable : (prefixWord ++ tailWord_5153159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153159).length < 2 ^ (prefixWord ++ tailWord_5153159).sum := by decide
  have hdescent : baseEnd_5153159 < baseStart_5153159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153176 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_5153176 : Nat := 118140960795 + 5153176 * 2 ^ 59
def prefixEnd_5153176 : Nat := 4983230072969 + 3 ^ 40 * 5153176 * 2
def baseEnd_5153176 : Nat := 882018728404545136300327

theorem tailTrace_5153176 : CollatzResearch.WordTrace tailWord_5153176 prefixEnd_5153176 882018728404545136300327 := by
  unfold tailWord_5153176
  simp only [CollatzResearch.WordTrace]
  refine ⟨93975884789465459619087691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125301179719287279492116921 93975884789465459619087691)
  ·
    refine ⟨140963827184198189428631537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93975884789465459619087691 140963827184198189428631537)
    ·
      refine ⟨105722870388148642071473653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140963827184198189428631537 105722870388148642071473653)
      ·
        refine ⟨9911519098888935194200655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105722870388148642071473653 9911519098888935194200655)
        ·
          refine ⟨14867278648333402791300983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911519098888935194200655 14867278648333402791300983)
          ·
            refine ⟨22300917972500104186951475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14867278648333402791300983 22300917972500104186951475)
            ·
              refine ⟨33451376958750156280427213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22300917972500104186951475 33451376958750156280427213)
              ·
                refine ⟨12544266359531308605160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33451376958750156280427213 12544266359531308605160205)
                ·
                  refine ⟨4704099884824240726935077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12544266359531308605160205 4704099884824240726935077)
                  ·
                    refine ⟨882018728404545136300327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704099884824240726935077 882018728404545136300327)
                    ·
                      rfl

theorem cell23_5153176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_5153176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153176 prefixEnd_5153176 := by exact prefixLift 5153176
  have htrace : WordTrace (prefixWord ++ tailWord_5153176) baseStart_5153176 baseEnd_5153176 := by
    simpa [prefixWord, tailWord_5153176, baseEnd_5153176] using wordTrace_append hprefix tailTrace_5153176
  have hstable : (prefixWord ++ tailWord_5153176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153176).length < 2 ^ (prefixWord ++ tailWord_5153176).sum := by decide
  have hdescent : baseEnd_5153176 < baseStart_5153176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153232 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_5153232 : Nat := 118140960795 + 5153232 * 2 ^ 59
def prefixEnd_5153232 : Nat := 4983230072969 + 3 ^ 40 * 5153232 * 2
def baseEnd_5153232 : Nat := 882028313376762396600241

theorem tailTrace_5153232 : CollatzResearch.WordTrace tailWord_5153232 prefixEnd_5153232 882028313376762396600241 := by
  unfold tailWord_5153232
  simp only [CollatzResearch.WordTrace]
  refine ⟨93976906033364020401106975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125302541377818693868142633 93976906033364020401106975)
  ·
    refine ⟨140965359050046030601660463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93976906033364020401106975 140965359050046030601660463)
    ·
      refine ⟨211448038575069045902490695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140965359050046030601660463 211448038575069045902490695)
      ·
        refine ⟨317172057862603568853736043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211448038575069045902490695 317172057862603568853736043)
        ·
          refine ⟨475758086793905353280604065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317172057862603568853736043 475758086793905353280604065)
          ·
            refine ⟨356818565095429014960453049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475758086793905353280604065 356818565095429014960453049)
            ·
              refine ⟨267613923821571761220339787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356818565095429014960453049 267613923821571761220339787)
              ·
                refine ⟨401420885732357641830509681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267613923821571761220339787 401420885732357641830509681)
                ·
                  refine ⟨301065664299268231372882261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401420885732357641830509681 301065664299268231372882261)
                  ·
                    refine ⟨882028313376762396600241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 301065664299268231372882261 882028313376762396600241)
                    ·
                      rfl

theorem cell23_5153232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_5153232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153232 prefixEnd_5153232 := by exact prefixLift 5153232
  have htrace : WordTrace (prefixWord ++ tailWord_5153232) baseStart_5153232 baseEnd_5153232 := by
    simpa [prefixWord, tailWord_5153232, baseEnd_5153232] using wordTrace_append hprefix tailTrace_5153232
  have hstable : (prefixWord ++ tailWord_5153232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153232).length < 2 ^ (prefixWord ++ tailWord_5153232).sum := by decide
  have hdescent : baseEnd_5153232 < baseStart_5153232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_5153233 : Nat := 118140960795 + 5153233 * 2 ^ 59
def prefixEnd_5153233 : Nat := 4983230072969 + 3 ^ 40 * 5153233 * 2
def baseEnd_5153233 : Nat := 2646085453610941685888219

theorem tailTrace_5153233 : CollatzResearch.WordTrace tailWord_5153233 prefixEnd_5153233 2646085453610941685888219 := by
  unfold tailWord_5153233
  simp only [CollatzResearch.WordTrace]
  refine ⟨187953848539724417973000353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125302565693149611982000235 187953848539724417973000353)
  ·
    refine ⟨140965386404793313479750265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187953848539724417973000353 140965386404793313479750265)
    ·
      refine ⟨105724039803594985109812699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140965386404793313479750265 105724039803594985109812699)
      ·
        refine ⟨158586059705392477664719049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105724039803594985109812699 158586059705392477664719049)
        ·
          refine ⟨118939544779044358248539287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158586059705392477664719049 118939544779044358248539287)
          ·
            refine ⟨178409317168566537372808931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118939544779044358248539287 178409317168566537372808931)
            ·
              refine ⟨267613975752849806059213397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178409317168566537372808931 267613975752849806059213397)
              ·
                refine ⟨3136101278353708664756407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 267613975752849806059213397 3136101278353708664756407)
                ·
                  refine ⟨4704151917530562997134611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136101278353708664756407 4704151917530562997134611)
                  ·
                    refine ⟨7056227876295844495701917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704151917530562997134611 7056227876295844495701917)
                    ·
                      refine ⟨2646085453610941685888219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056227876295844495701917 2646085453610941685888219)
                      ·
                        rfl

theorem cell23_5153233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_5153233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153233 prefixEnd_5153233 := by exact prefixLift 5153233
  have htrace : WordTrace (prefixWord ++ tailWord_5153233) baseStart_5153233 baseEnd_5153233 := by
    simpa [prefixWord, tailWord_5153233, baseEnd_5153233] using wordTrace_append hprefix tailTrace_5153233
  have hstable : (prefixWord ++ tailWord_5153233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153233).length < 2 ^ (prefixWord ++ tailWord_5153233).sum := by decide
  have hdescent : baseEnd_5153233 < baseStart_5153233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153249 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_5153249 : Nat := 118140960795 + 5153249 * 2 ^ 59
def prefixEnd_5153249 : Nat := 4983230072969 + 3 ^ 40 * 5153249 * 2
def baseEnd_5153249 : Nat := 882031223100471207762715

theorem tailTrace_5153249 : CollatzResearch.WordTrace tailWord_5153249 prefixEnd_5153249 882031223100471207762715 := by
  unfold tailWord_5153249
  simp only [CollatzResearch.WordTrace]
  refine ⟨187954432107666452705582801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125302954738444301803721867 187954432107666452705582801)
  ·
    refine ⟨140965824080749839529187101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187954432107666452705582801 140965824080749839529187101)
    ·
      refine ⟨52862184030281189823445163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140965824080749839529187101 52862184030281189823445163)
      ·
        refine ⟨79293276045421784735167745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52862184030281189823445163 79293276045421784735167745)
        ·
          refine ⟨59469957034066338551375809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79293276045421784735167745 59469957034066338551375809)
          ·
            refine ⟨44602467775549753913531857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59469957034066338551375809 44602467775549753913531857)
            ·
              refine ⟨33451850831662315435148893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44602467775549753913531857 33451850831662315435148893)
              ·
                refine ⟨12544444061873368288180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33451850831662315435148893 12544444061873368288180835)
                ·
                  refine ⟨18816666092810052432271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12544444061873368288180835 18816666092810052432271253)
                  ·
                    refine ⟨882031223100471207762715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18816666092810052432271253 882031223100471207762715)
                    ·
                      rfl

theorem cell23_5153249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_5153249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153249 prefixEnd_5153249 := by exact prefixLift 5153249
  have htrace : WordTrace (prefixWord ++ tailWord_5153249) baseStart_5153249 baseEnd_5153249 := by
    simpa [prefixWord, tailWord_5153249, baseEnd_5153249] using wordTrace_append hprefix tailTrace_5153249
  have hstable : (prefixWord ++ tailWord_5153249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153249).length < 2 ^ (prefixWord ++ tailWord_5153249).sum := by decide
  have hdescent : baseEnd_5153249 < baseStart_5153249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153256 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5153256 : Nat := 118140960795 + 5153256 * 2 ^ 59
def prefixEnd_5153256 : Nat := 4983230072969 + 3 ^ 40 * 5153256 * 2
def baseEnd_5153256 : Nat := 2646097263665995095900613

theorem tailTrace_5153256 : CollatzResearch.WordTrace tailWord_5153256 prefixEnd_5153256 2646097263665995095900613 := by
  unfold tailWord_5153256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93977343709320546450543811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125303124945760728600725081 93977343709320546450543811)
  ·
    refine ⟨140966015563980819675815717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93977343709320546450543811 140966015563980819675815717)
    ·
      refine ⟨26431127918246403689215447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140966015563980819675815717 26431127918246403689215447)
      ·
        refine ⟨39646691877369605533823171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26431127918246403689215447 39646691877369605533823171)
        ·
          refine ⟨59470037816054408300734757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39646691877369605533823171 59470037816054408300734757)
          ·
            refine ⟨11150632090510201556387767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59470037816054408300734757 11150632090510201556387767)
            ·
              refine ⟨16725948135765302334581651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11150632090510201556387767 16725948135765302334581651)
              ·
                refine ⟨25088922203647953501872477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16725948135765302334581651 25088922203647953501872477)
                ·
                  refine ⟨9408345826367982563202179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25088922203647953501872477 9408345826367982563202179)
                  ·
                    refine ⟨14112518739551973844803269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9408345826367982563202179 14112518739551973844803269)
                    ·
                      refine ⟨2646097263665995095900613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14112518739551973844803269 2646097263665995095900613)
                      ·
                        rfl

theorem cell23_5153256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5153256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153256 prefixEnd_5153256 := by exact prefixLift 5153256
  have htrace : WordTrace (prefixWord ++ tailWord_5153256) baseStart_5153256 baseEnd_5153256 := by
    simpa [prefixWord, tailWord_5153256, baseEnd_5153256] using wordTrace_append hprefix tailTrace_5153256
  have hstable : (prefixWord ++ tailWord_5153256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153256).length < 2 ^ (prefixWord ++ tailWord_5153256).sum := by decide
  have hdescent : baseEnd_5153256 < baseStart_5153256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153284 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5153284 : Nat := 118140960795 + 5153284 * 2 ^ 59
def prefixEnd_5153284 : Nat := 4983230072969 + 3 ^ 40 * 5153284 * 2
def baseEnd_5153284 : Nat := 2646111641124320986350485

theorem tailTrace_5153284 : CollatzResearch.WordTrace tailWord_5153284 prefixEnd_5153284 2646111641124320986350485 := by
  unfold tailWord_5153284
  simp only [CollatzResearch.WordTrace]
  refine ⟨93977854331269826841553453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125303805775026435788737937 93977854331269826841553453)
  ·
    refine ⟨35241695374226185065582545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93977854331269826841553453 35241695374226185065582545)
    ·
      refine ⟨26431271530669638799186909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35241695374226185065582545 26431271530669638799186909)
      ·
        refine ⟨9911726824001114549695091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26431271530669638799186909 9911726824001114549695091)
        ·
          refine ⟨14867590236001671824542637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911726824001114549695091 14867590236001671824542637)
          ·
            refine ⟨5575346338500626934203489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14867590236001671824542637 5575346338500626934203489)
            ·
              refine ⟨4181509753875470200652617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575346338500626934203489 4181509753875470200652617)
              ·
                refine ⟨3136132315406602650489463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181509753875470200652617 3136132315406602650489463)
                ·
                  refine ⟨4704198473109903975734195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136132315406602650489463 4704198473109903975734195)
                  ·
                    refine ⟨7056297709664855963601293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704198473109903975734195 7056297709664855963601293)
                    ·
                      refine ⟨2646111641124320986350485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056297709664855963601293 2646111641124320986350485)
                      ·
                        rfl

theorem cell23_5153284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5153284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153284 prefixEnd_5153284 := by exact prefixLift 5153284
  have htrace : WordTrace (prefixWord ++ tailWord_5153284) baseStart_5153284 baseEnd_5153284 := by
    simpa [prefixWord, tailWord_5153284, baseEnd_5153284] using wordTrace_append hprefix tailTrace_5153284
  have hstable : (prefixWord ++ tailWord_5153284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153284).length < 2 ^ (prefixWord ++ tailWord_5153284).sum := by decide
  have hdescent : baseEnd_5153284 < baseStart_5153284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153300 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5153300 : Nat := 118140960795 + 5153300 * 2 ^ 59
def prefixEnd_5153300 : Nat := 4983230072969 + 3 ^ 40 * 5153300 * 2
def baseEnd_5153300 : Nat := 882039952271597641250137

theorem tailTrace_5153300 : CollatzResearch.WordTrace tailWord_5153300 prefixEnd_5153300 882039952271597641250137 := by
  unfold tailWord_5153300
  simp only [CollatzResearch.WordTrace]
  refine ⟨93978146115240844207844677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125304194820321125610459569 93978146115240844207844677)
  ·
    refine ⟨17620902396607658288970877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93978146115240844207844677 17620902396607658288970877)
    ·
      refine ⟨6607838398727871858364079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17620902396607658288970877 6607838398727871858364079)
      ·
        refine ⟨9911757598091807787546119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607838398727871858364079 9911757598091807787546119)
        ·
          refine ⟨14867636397137711681319179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911757598091807787546119 14867636397137711681319179)
          ·
            refine ⟨22301454595706567521978769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14867636397137711681319179 22301454595706567521978769)
            ·
              refine ⟨16726090946779925641484077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22301454595706567521978769 16726090946779925641484077)
              ·
                refine ⟨6272284105042472115556529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16726090946779925641484077 6272284105042472115556529)
                ·
                  refine ⟨4704213078781854086667397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272284105042472115556529 4704213078781854086667397)
                  ·
                    refine ⟨882039952271597641250137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704213078781854086667397 882039952271597641250137)
                    ·
                      rfl

theorem cell23_5153300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5153300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153300 prefixEnd_5153300 := by exact prefixLift 5153300
  have htrace : WordTrace (prefixWord ++ tailWord_5153300) baseStart_5153300 baseEnd_5153300 := by
    simpa [prefixWord, tailWord_5153300, baseEnd_5153300] using wordTrace_append hprefix tailTrace_5153300
  have hstable : (prefixWord ++ tailWord_5153300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153300).length < 2 ^ (prefixWord ++ tailWord_5153300).sum := by decide
  have hdescent : baseEnd_5153300 < baseStart_5153300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153306 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_5153306 : Nat := 118140960795 + 5153306 * 2 ^ 59
def prefixEnd_5153306 : Nat := 4983230072969 + 3 ^ 40 * 5153306 * 2
def baseEnd_5153306 : Nat := 2646122937698719900275383

theorem tailTrace_5153306 : CollatzResearch.WordTrace tailWord_5153306 prefixEnd_5153306 2646122937698719900275383 := by
  unfold tailWord_5153306
  simp only [CollatzResearch.WordTrace]
  refine ⟨46989127767114987860101943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125304340712306634293605181 46989127767114987860101943)
  ·
    refine ⟨70483691650672481790152915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46989127767114987860101943 70483691650672481790152915)
    ·
      refine ⟨105725537476008722685229373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70483691650672481790152915 105725537476008722685229373)
      ·
        refine ⟨39647076553503271006961015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105725537476008722685229373 39647076553503271006961015)
        ·
          refine ⟨59470614830254906510441523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39647076553503271006961015 59470614830254906510441523)
          ·
            refine ⟨89205922245382359765662285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59470614830254906510441523 89205922245382359765662285)
            ·
              refine ⟨33452220842018384912123357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89205922245382359765662285 33452220842018384912123357)
              ·
                refine ⟨12544582815756894342046259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33452220842018384912123357 12544582815756894342046259)
                ·
                  refine ⟨18816874223635341513069389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12544582815756894342046259 18816874223635341513069389)
                  ·
                    refine ⟨7056327833863253067401021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18816874223635341513069389 7056327833863253067401021)
                    ·
                      refine ⟨2646122937698719900275383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056327833863253067401021 2646122937698719900275383)
                      ·
                        rfl

theorem cell23_5153306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_5153306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153306 prefixEnd_5153306 := by exact prefixLift 5153306
  have htrace : WordTrace (prefixWord ++ tailWord_5153306) baseStart_5153306 baseEnd_5153306 := by
    simpa [prefixWord, tailWord_5153306, baseEnd_5153306] using wordTrace_append hprefix tailTrace_5153306
  have hstable : (prefixWord ++ tailWord_5153306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153306).length < 2 ^ (prefixWord ++ tailWord_5153306).sum := by decide
  have hdescent : baseEnd_5153306 < baseStart_5153306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153340 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_5153340 : Nat := 118140960795 + 5153340 * 2 ^ 59
def prefixEnd_5153340 : Nat := 4983230072969 + 3 ^ 40 * 5153340 * 2
def baseEnd_5153340 : Nat := 2646140396040972767250227

theorem tailTrace_5153340 : CollatzResearch.WordTrace tailWord_5153340 prefixEnd_5153340 2646140396040972767250227 := by
  unfold tailWord_5153340
  simp only [CollatzResearch.WordTrace]
  refine ⟨93978875575168387623572737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125305167433557850164763649 93978875575168387623572737)
  ·
    refine ⟨70484156681376290717679553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93978875575168387623572737 70484156681376290717679553)
    ·
      refine ⟨52863117511032218038259665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70484156681376290717679553 52863117511032218038259665)
      ·
        refine ⟨39647338133274163528694749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52863117511032218038259665 39647338133274163528694749)
        ·
          refine ⟨14867751799977811323260531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39647338133274163528694749 14867751799977811323260531)
          ·
            refine ⟨22301627699966716984890797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14867751799977811323260531 22301627699966716984890797)
            ·
              refine ⟨8363110387487518869334049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22301627699966716984890797 8363110387487518869334049)
              ·
                refine ⟨6272332790615639152000537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8363110387487518869334049 6272332790615639152000537)
                ·
                  refine ⟨4704249592961729364000403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272332790615639152000537 4704249592961729364000403)
                  ·
                    refine ⟨7056374389442594046000605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704249592961729364000403 7056374389442594046000605)
                    ·
                      refine ⟨2646140396040972767250227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056374389442594046000605 2646140396040972767250227)
                      ·
                        rfl

theorem cell23_5153340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_5153340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153340 prefixEnd_5153340 := by exact prefixLift 5153340
  have htrace : WordTrace (prefixWord ++ tailWord_5153340) baseStart_5153340 baseEnd_5153340 := by
    simpa [prefixWord, tailWord_5153340, baseEnd_5153340] using wordTrace_append hprefix tailTrace_5153340
  have hstable : (prefixWord ++ tailWord_5153340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153340).length < 2 ^ (prefixWord ++ tailWord_5153340).sum := by decide
  have hdescent : baseEnd_5153340 < baseStart_5153340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153454 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_5153454 : Nat := 118140960795 + 5153454 * 2 ^ 59
def prefixEnd_5153454 : Nat := 4983230072969 + 3 ^ 40 * 5153454 * 2
def baseEnd_5153454 : Nat := 294022103648398369024967

theorem tailTrace_5153454 : CollatzResearch.WordTrace tailWord_5153454 prefixEnd_5153454 294022103648398369024967 := by
  unfold tailWord_5153454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495238633990471589599427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125307939381282515144530277 23495238633990471589599427)
  ·
    refine ⟨35242857950985707384399141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23495238633990471589599427 35242857950985707384399141)
    ·
      refine ⟨6608035865809820134574839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35242857950985707384399141 6608035865809820134574839)
      ·
        refine ⟨9912053798714730201862259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608035865809820134574839 9912053798714730201862259)
        ·
          refine ⟨14868080698072095302793389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9912053798714730201862259 14868080698072095302793389)
          ·
            refine ⟨5575530261777035738547521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14868080698072095302793389 5575530261777035738547521)
            ·
              refine ⟨4181647696332776803910641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575530261777035738547521 4181647696332776803910641)
              ·
                refine ⟨3136235772249582602932981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181647696332776803910641 3136235772249582602932981)
                ·
                  refine ⟨294022103648398369024967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3136235772249582602932981 294022103648398369024967)
                  ·
                    rfl

theorem cell23_5153454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_5153454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153454 prefixEnd_5153454 := by exact prefixLift 5153454
  have htrace : WordTrace (prefixWord ++ tailWord_5153454) baseStart_5153454 baseEnd_5153454 := by
    simpa [prefixWord, tailWord_5153454, baseEnd_5153454] using wordTrace_append hprefix tailTrace_5153454
  have hstable : (prefixWord ++ tailWord_5153454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153454).length < 2 ^ (prefixWord ++ tailWord_5153454).sum := by decide
  have hdescent : baseEnd_5153454 < baseStart_5153454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153456 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_5153456 : Nat := 118140960795 + 5153456 * 2 ^ 59
def prefixEnd_5153456 : Nat := 4983230072969 + 3 ^ 40 * 5153456 * 2
def baseEnd_5153456 : Nat := 2646199959796894313399693

theorem tailTrace_5153456 : CollatzResearch.WordTrace tailWord_5153456 prefixEnd_5153456 2646199959796894313399693 := by
  unfold tailWord_5153456
  simp only [CollatzResearch.WordTrace]
  refine ⟨93980991008958263529184111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125307988011944351372245481 93980991008958263529184111)
  ·
    refine ⟨140971486513437395293776167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93980991008958263529184111 140971486513437395293776167)
    ·
      refine ⟨211457229770156092940664251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140971486513437395293776167 211457229770156092940664251)
      ·
        refine ⟨317185844655234139410996377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211457229770156092940664251 317185844655234139410996377)
        ·
          refine ⟨237889383491425604558247283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317185844655234139410996377 237889383491425604558247283)
          ·
            refine ⟨356834075237138406837370925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237889383491425604558247283 356834075237138406837370925)
            ·
              refine ⟨133812778213926902564014097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356834075237138406837370925 133812778213926902564014097)
              ·
                refine ⟨100359583660445176923010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133812778213926902564014097 100359583660445176923010573)
                ·
                  refine ⟨37634843872666941346128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100359583660445176923010573 37634843872666941346128965)
                  ·
                    refine ⟨7056533226125051502399181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37634843872666941346128965 7056533226125051502399181)
                    ·
                      refine ⟨2646199959796894313399693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056533226125051502399181 2646199959796894313399693)
                      ·
                        rfl

theorem cell23_5153456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_5153456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153456 prefixEnd_5153456 := by exact prefixLift 5153456
  have htrace : WordTrace (prefixWord ++ tailWord_5153456) baseStart_5153456 baseEnd_5153456 := by
    simpa [prefixWord, tailWord_5153456, baseEnd_5153456] using wordTrace_append hprefix tailTrace_5153456
  have hstable : (prefixWord ++ tailWord_5153456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153456).length < 2 ^ (prefixWord ++ tailWord_5153456).sum := by decide
  have hdescent : baseEnd_5153456 < baseStart_5153456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153470 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_5153470 : Nat := 118140960795 + 5153470 * 2 ^ 59
def prefixEnd_5153470 : Nat := 4983230072969 + 3 ^ 40 * 5153470 * 2
def baseEnd_5153470 : Nat := 2646207148526057258624629

theorem tailTrace_5153470 : CollatzResearch.WordTrace tailWord_5153470 prefixEnd_5153470 2646207148526057258624629 := by
  unfold tailWord_5153470
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495311579983225931172233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125308328426577204966251909 23495311579983225931172233)
  ·
    refine ⟨17621483684987419448379175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23495311579983225931172233 17621483684987419448379175)
    ·
      refine ⟨26432225527481129172568763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621483684987419448379175 26432225527481129172568763)
      ·
        refine ⟨39648338291221693758853145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26432225527481129172568763 39648338291221693758853145)
        ·
          refine ⟨29736253718416270319139859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39648338291221693758853145 29736253718416270319139859)
          ·
            refine ⟨44604380577624405478709789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29736253718416270319139859 44604380577624405478709789)
            ·
              refine ⟨16726642716609152054516171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44604380577624405478709789 16726642716609152054516171)
              ·
                refine ⟨25089964074913728081774257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726642716609152054516171 25089964074913728081774257)
                ·
                  refine ⟨18817473056185296061330693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25089964074913728081774257 18817473056185296061330693)
                  ·
                    refine ⟨3528276198034743011499505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18817473056185296061330693 3528276198034743011499505)
                    ·
                      refine ⟨2646207148526057258624629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528276198034743011499505 2646207148526057258624629)
                      ·
                        rfl

theorem cell23_5153470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_5153470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153470 prefixEnd_5153470 := by exact prefixLift 5153470
  have htrace : WordTrace (prefixWord ++ tailWord_5153470) baseStart_5153470 baseEnd_5153470 := by
    simpa [prefixWord, tailWord_5153470, baseEnd_5153470] using wordTrace_append hprefix tailTrace_5153470
  have hstable : (prefixWord ++ tailWord_5153470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153470).length < 2 ^ (prefixWord ++ tailWord_5153470).sum := by decide
  have hdescent : baseEnd_5153470 < baseStart_5153470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153490 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5153490 : Nat := 118140960795 + 5153490 * 2 ^ 59
def prefixEnd_5153490 : Nat := 4983230072969 + 3 ^ 40 * 5153490 * 2
def baseEnd_5153490 : Nat := 2646217418139147180374537

theorem tailTrace_5153490 : CollatzResearch.WordTrace tailWord_5153490 prefixEnd_5153490 2646217418139147180374537 := by
  unfold tailWord_5153490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46990805524948337716276481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125308814733195567243403949 46990805524948337716276481)
  ·
    refine ⟨35243104143711253287207361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46990805524948337716276481 35243104143711253287207361)
    ·
      refine ⟨26432328107783439965405521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35243104143711253287207361 26432328107783439965405521)
      ·
        refine ⟨19824246080837579974054141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26432328107783439965405521 19824246080837579974054141)
        ·
          refine ⟨7434092280314092490270303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19824246080837579974054141 7434092280314092490270303)
          ·
            refine ⟨11151138420471138735405455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434092280314092490270303 11151138420471138735405455)
            ·
              refine ⟨16726707630706708103108183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151138420471138735405455 16726707630706708103108183)
              ·
                refine ⟨25090061446060062154662275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726707630706708103108183 25090061446060062154662275)
                ·
                  refine ⟨37635092169090093231993413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25090061446060062154662275 37635092169090093231993413)
                  ·
                    refine ⟨7056579781704392480998765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37635092169090093231993413 7056579781704392480998765)
                    ·
                      refine ⟨2646217418139147180374537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056579781704392480998765 2646217418139147180374537)
                      ·
                        rfl

theorem cell23_5153490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5153490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153490 prefixEnd_5153490 := by exact prefixLift 5153490
  have htrace : WordTrace (prefixWord ++ tailWord_5153490) baseStart_5153490 baseEnd_5153490 := by
    simpa [prefixWord, tailWord_5153490, baseEnd_5153490] using wordTrace_append hprefix tailTrace_5153490
  have hstable : (prefixWord ++ tailWord_5153490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153490).length < 2 ^ (prefixWord ++ tailWord_5153490).sum := by decide
  have hdescent : baseEnd_5153490 < baseStart_5153490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153520 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_5153520 : Nat := 118140960795 + 5153520 * 2 ^ 59
def prefixEnd_5153520 : Nat := 4983230072969 + 3 ^ 40 * 5153520 * 2
def baseEnd_5153520 : Nat := 2646232822558782062999399

theorem tailTrace_5153520 : CollatzResearch.WordTrace tailWord_5153520 prefixEnd_5153520 2646232822558782062999399 := by
  unfold tailWord_5153520
  simp only [CollatzResearch.WordTrace]
  refine ⟨93982158144842332994349007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125309544193123110659132009 93982158144842332994349007)
  ·
    refine ⟨140973237217263499491523511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93982158144842332994349007 140973237217263499491523511)
    ·
      refine ⟨211459855825895249237285267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140973237217263499491523511 211459855825895249237285267)
      ·
        refine ⟨317189783738842873855927901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211459855825895249237285267 317189783738842873855927901)
        ·
          refine ⟨118946168902066077695972963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317189783738842873855927901 118946168902066077695972963)
          ·
            refine ⟨178419253353099116543959445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118946168902066077695972963 178419253353099116543959445)
            ·
              refine ⟨8363402500926521087998099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 178419253353099116543959445 8363402500926521087998099)
              ·
                refine ⟨12545103751389781631997149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363402500926521087998099 12545103751389781631997149)
                ·
                  refine ⟨4704413906771168111998931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12545103751389781631997149 4704413906771168111998931)
                  ·
                    refine ⟨7056620860156752167998397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704413906771168111998931 7056620860156752167998397)
                    ·
                      refine ⟨2646232822558782062999399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056620860156752167998397 2646232822558782062999399)
                      ·
                        rfl

theorem cell23_5153520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_5153520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153520 prefixEnd_5153520 := by exact prefixLift 5153520
  have htrace : WordTrace (prefixWord ++ tailWord_5153520) baseStart_5153520 baseEnd_5153520 := by
    simpa [prefixWord, tailWord_5153520, baseEnd_5153520] using wordTrace_append hprefix tailTrace_5153520
  have hstable : (prefixWord ++ tailWord_5153520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153520).length < 2 ^ (prefixWord ++ tailWord_5153520).sum := by decide
  have hdescent : baseEnd_5153520 < baseStart_5153520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153540 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5153540 : Nat := 118140960795 + 5153540 * 2 ^ 59
def prefixEnd_5153540 : Nat := 4983230072969 + 3 ^ 40 * 5153540 * 2
def baseEnd_5153540 : Nat := 882081030723957328249769

theorem tailTrace_5153540 : CollatzResearch.WordTrace tailWord_5153540 prefixEnd_5153540 882081030723957328249769 := by
  unfold tailWord_5153540
  simp only [CollatzResearch.WordTrace]
  refine ⟨93982522874806104702213037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125310030499741472936284049 93982522874806104702213037)
  ·
    refine ⟨35243446078052289263329889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93982522874806104702213037 35243446078052289263329889)
    ·
      refine ⟨26432584558539216947497417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35243446078052289263329889 26432584558539216947497417)
      ·
        refine ⟨19824438418904412710623063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26432584558539216947497417 19824438418904412710623063)
        ·
          refine ⟨29736657628356619065934595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19824438418904412710623063 29736657628356619065934595)
          ·
            refine ⟨44604986442534928598901893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29736657628356619065934595 44604986442534928598901893)
            ·
              refine ⟨8363434957975299112294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44604986442534928598901893 8363434957975299112294105)
              ·
                refine ⟨6272576218481474334220579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8363434957975299112294105 6272576218481474334220579)
                ·
                  refine ⟨9408864327722211501330869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272576218481474334220579 9408864327722211501330869)
                  ·
                    refine ⟨882081030723957328249769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9408864327722211501330869 882081030723957328249769)
                    ·
                      rfl

theorem cell23_5153540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5153540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153540 prefixEnd_5153540 := by exact prefixLift 5153540
  have htrace : WordTrace (prefixWord ++ tailWord_5153540) baseStart_5153540 baseEnd_5153540 := by
    simpa [prefixWord, tailWord_5153540, baseEnd_5153540] using wordTrace_append hprefix tailTrace_5153540
  have hstable : (prefixWord ++ tailWord_5153540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153540).length < 2 ^ (prefixWord ++ tailWord_5153540).sum := by decide
  have hdescent : baseEnd_5153540 < baseStart_5153540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153553 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_5153553 : Nat := 118140960795 + 5153553 * 2 ^ 59
def prefixEnd_5153553 : Nat := 4983230072969 + 3 ^ 40 * 5153553 * 2
def baseEnd_5153553 : Nat := 882083255806793477962249

theorem tailTrace_5153553 : CollatzResearch.WordTrace tailWord_5153553 prefixEnd_5153553 882083255806793477962249 := by
  unfold tailWord_5153553
  simp only [CollatzResearch.WordTrace]
  refine ⟨187965519898565112624649313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125310346599043408416432875 187965519898565112624649313)
  ·
    refine ⟨140974139923923834468486985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187965519898565112624649313 140974139923923834468486985)
    ·
      refine ⟨105730604942942875851365239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140974139923923834468486985 105730604942942875851365239)
      ·
        refine ⟨158595907414414313777047859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105730604942942875851365239 158595907414414313777047859)
        ·
          refine ⟨237893861121621470665571789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158595907414414313777047859 237893861121621470665571789)
          ·
            refine ⟨89210197920608051499589421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237893861121621470665571789 89210197920608051499589421)
            ·
              refine ⟨33453824220228019312346033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89210197920608051499589421 33453824220228019312346033)
              ·
                refine ⟨25090368165171014484259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33453824220228019312346033 25090368165171014484259525)
                ·
                  refine ⟨4704444030969565215798661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25090368165171014484259525 4704444030969565215798661)
                  ·
                    refine ⟨882083255806793477962249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704444030969565215798661 882083255806793477962249)
                    ·
                      rfl

theorem cell23_5153553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_5153553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153553 prefixEnd_5153553 := by exact prefixLift 5153553
  have htrace : WordTrace (prefixWord ++ tailWord_5153553) baseStart_5153553 baseEnd_5153553 := by
    simpa [prefixWord, tailWord_5153553, baseEnd_5153553] using wordTrace_append hprefix tailTrace_5153553
  have hstable : (prefixWord ++ tailWord_5153553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153553).length < 2 ^ (prefixWord ++ tailWord_5153553).sum := by decide
  have hdescent : baseEnd_5153553 < baseStart_5153553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153570 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5153570 : Nat := 118140960795 + 5153570 * 2 ^ 59
def prefixEnd_5153570 : Nat := 4983230072969 + 3 ^ 40 * 5153570 * 2
def baseEnd_5153570 : Nat := 882086165530502289124723

theorem tailTrace_5153570 : CollatzResearch.WordTrace tailWord_5153570 prefixEnd_5153570 882086165530502289124723 := by
  unfold tailWord_5153570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46991534984875881132004541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125310759959669016352012109 46991534984875881132004541)
  ·
    refine ⟨17621825619328455424501703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46991534984875881132004541 17621825619328455424501703)
    ·
      refine ⟨26432738428992683136752555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621825619328455424501703 26432738428992683136752555)
      ·
        refine ⟨39649107643489024705128833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26432738428992683136752555 39649107643489024705128833)
        ·
          refine ⟨29736830732616768528846625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39649107643489024705128833 29736830732616768528846625)
          ·
            refine ⟨22302623049462576396634969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29736830732616768528846625 22302623049462576396634969)
            ·
              refine ⟨16726967287096932297476227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22302623049462576396634969 16726967287096932297476227)
              ·
                refine ⟨25090450930645398446214341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726967287096932297476227 25090450930645398446214341)
                ·
                  refine ⟨4704459549496012208665189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25090450930645398446214341 4704459549496012208665189)
                  ·
                    refine ⟨882086165530502289124723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704459549496012208665189 882086165530502289124723)
                    ·
                      rfl

theorem cell23_5153570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5153570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153570 prefixEnd_5153570 := by exact prefixLift 5153570
  have htrace : WordTrace (prefixWord ++ tailWord_5153570) baseStart_5153570 baseEnd_5153570 := by
    simpa [prefixWord, tailWord_5153570, baseEnd_5153570] using wordTrace_append hprefix tailTrace_5153570
  have hstable : (prefixWord ++ tailWord_5153570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153570).length < 2 ^ (prefixWord ++ tailWord_5153570).sum := by decide
  have hdescent : baseEnd_5153570 < baseStart_5153570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153587 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 2, 4]
def baseStart_5153587 : Nat := 118140960795 + 5153587 * 2 ^ 59
def prefixEnd_5153587 : Nat := 4983230072969 + 3 ^ 40 * 5153587 * 2
def baseEnd_5153587 : Nat := 882089075254211100287197

theorem tailTrace_5153587 : CollatzResearch.WordTrace tailWord_5153587 prefixEnd_5153587 882089075254211100287197 := by
  unfold tailWord_5153587
  simp only [CollatzResearch.WordTrace]
  refine ⟨187966759980441936431387015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125311173320294624287591343 187966759980441936431387015)
  ·
    refine ⟨281950139970662904647080523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187966759980441936431387015 281950139970662904647080523)
    ·
      refine ⟨422925209955994356970620785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281950139970662904647080523 422925209955994356970620785)
      ·
        refine ⟨317193907466995767727965589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422925209955994356970620785 317193907466995767727965589)
        ·
          refine ⟨14868464412515426612248387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 317193907466995767727965589 14868464412515426612248387)
          ·
            refine ⟨22302696618773139918372581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868464412515426612248387 22302696618773139918372581)
            ·
              refine ⟨4181755616019963734694859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22302696618773139918372581 4181755616019963734694859)
              ·
                refine ⟨6272633424029945602042289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181755616019963734694859 6272633424029945602042289)
                ·
                  refine ⟨4704475068022459201531717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272633424029945602042289 4704475068022459201531717)
                  ·
                    refine ⟨882089075254211100287197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704475068022459201531717 882089075254211100287197)
                    ·
                      rfl

theorem cell23_5153587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 4].length) (baseStart_5153587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153587 prefixEnd_5153587 := by exact prefixLift 5153587
  have htrace : WordTrace (prefixWord ++ tailWord_5153587) baseStart_5153587 baseEnd_5153587 := by
    simpa [prefixWord, tailWord_5153587, baseEnd_5153587] using wordTrace_append hprefix tailTrace_5153587
  have hstable : (prefixWord ++ tailWord_5153587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153587).length < 2 ^ (prefixWord ++ tailWord_5153587).sum := by decide
  have hdescent : baseEnd_5153587 < baseStart_5153587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153594 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_5153594 : Nat := 118140960795 + 5153594 * 2 ^ 59
def prefixEnd_5153594 : Nat := 4983230072969 + 3 ^ 40 * 5153594 * 2
def baseEnd_5153594 : Nat := 2646270820127214773474059

theorem tailTrace_5153594 : CollatzResearch.WordTrace tailWord_5153594 prefixEnd_5153594 2646270820127214773474059 := by
  unfold tailWord_5153594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46991753822854144156722959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125311343527611051084594557 46991753822854144156722959)
  ·
    refine ⟨70487630734281216235084439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46991753822854144156722959 70487630734281216235084439)
    ·
      refine ⟨105731446101421824352626659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70487630734281216235084439 105731446101421824352626659)
      ·
        refine ⟨158597169152132736528939989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105731446101421824352626659 158597169152132736528939989)
        ·
          refine ⟨3717121152003111012397031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 158597169152132736528939989 3717121152003111012397031)
          ·
            refine ⟨5575681728004666518595547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717121152003111012397031 5575681728004666518595547)
            ·
              refine ⟨8363522592006999777893321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575681728004666518595547 8363522592006999777893321)
              ·
                refine ⟨6272641944005249833419991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8363522592006999777893321 6272641944005249833419991)
                ·
                  refine ⟨9408962916007874750129987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272641944005249833419991 9408962916007874750129987)
                  ·
                    refine ⟨14113444374011812125194981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9408962916007874750129987 14113444374011812125194981)
                    ·
                      refine ⟨2646270820127214773474059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14113444374011812125194981 2646270820127214773474059)
                      ·
                        rfl

theorem cell23_5153594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_5153594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153594 prefixEnd_5153594 := by exact prefixLift 5153594
  have htrace : WordTrace (prefixWord ++ tailWord_5153594) baseStart_5153594 baseEnd_5153594 := by
    simpa [prefixWord, tailWord_5153594, baseEnd_5153594] using wordTrace_append hprefix tailTrace_5153594
  have hstable : (prefixWord ++ tailWord_5153594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153594).length < 2 ^ (prefixWord ++ tailWord_5153594).sum := by decide
  have hdescent : baseEnd_5153594 < baseStart_5153594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153597 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5153597 : Nat := 118140960795 + 5153597 * 2 ^ 59
def prefixEnd_5153597 : Nat := 4983230072969 + 3 ^ 40 * 5153597 * 2
def baseEnd_5153597 : Nat := 2646272360569178261736545

theorem tailTrace_5153597 : CollatzResearch.WordTrace tailWord_5153597 prefixEnd_5153597 2646272360569178261736545 := by
  unfold tailWord_5153597
  simp only [CollatzResearch.WordTrace]
  refine ⟨187967124710405708139251045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125311416473603805426167363 187967124710405708139251045)
  ·
    refine ⟨35243835883201070276109571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187967124710405708139251045 35243835883201070276109571)
    ·
      refine ⟨52865753824801605414164357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35243835883201070276109571 52865753824801605414164357)
      ·
        refine ⟨9912328842150301015155817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52865753824801605414164357 9912328842150301015155817)
        ·
          refine ⟨7434246631612725761366863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9912328842150301015155817 7434246631612725761366863)
          ·
            refine ⟨11151369947419088642050295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434246631612725761366863 11151369947419088642050295)
            ·
              refine ⟨16727054921128632963075443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151369947419088642050295 16727054921128632963075443)
              ·
                refine ⟨25090582381692949444613165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16727054921128632963075443 25090582381692949444613165)
                ·
                  refine ⟨9408968393134856041729937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25090582381692949444613165 9408968393134856041729937)
                  ·
                    refine ⟨7056726294851142031297453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9408968393134856041729937 7056726294851142031297453)
                    ·
                      refine ⟨2646272360569178261736545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056726294851142031297453 2646272360569178261736545)
                      ·
                        rfl

theorem cell23_5153597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5153597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153597 prefixEnd_5153597 := by exact prefixLift 5153597
  have htrace : WordTrace (prefixWord ++ tailWord_5153597) baseStart_5153597 baseEnd_5153597 := by
    simpa [prefixWord, tailWord_5153597, baseEnd_5153597] using wordTrace_append hprefix tailTrace_5153597
  have hstable : (prefixWord ++ tailWord_5153597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153597).length < 2 ^ (prefixWord ++ tailWord_5153597).sum := by decide
  have hdescent : baseEnd_5153597 < baseStart_5153597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153610 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_5153610 : Nat := 118140960795 + 5153610 * 2 ^ 59
def prefixEnd_5153610 : Nat := 4983230072969 + 3 ^ 40 * 5153610 * 2
def baseEnd_5153610 : Nat := 2646279035817686710873985

theorem tailTrace_5153610 : CollatzResearch.WordTrace tailWord_5153610 prefixEnd_5153610 2646279035817686710873985 := by
  unfold tailWord_5153610
  simp only [CollatzResearch.WordTrace]
  refine ⟨46991899714839652839868571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125311732572905740906316189 46991899714839652839868571)
  ·
    refine ⟨70487849572259479259802857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46991899714839652839868571 70487849572259479259802857)
    ·
      refine ⟨52865887179194609444852143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70487849572259479259802857 52865887179194609444852143)
      ·
        refine ⟨79298830768791914167278215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52865887179194609444852143 79298830768791914167278215)
        ·
          refine ⟨118948246153187871250917323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79298830768791914167278215 118948246153187871250917323)
          ·
            refine ⟨178422369229781806876375985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118948246153187871250917323 178422369229781806876375985)
            ·
              refine ⟨133816776922336355157281989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178422369229781806876375985 133816776922336355157281989)
              ·
                refine ⟨25090645672938066591990373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133816776922336355157281989 25090645672938066591990373)
                ·
                  refine ⟨4704496063675887485998195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25090645672938066591990373 4704496063675887485998195)
                  ·
                    refine ⟨7056744095513831228997293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704496063675887485998195 7056744095513831228997293)
                    ·
                      refine ⟨2646279035817686710873985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056744095513831228997293 2646279035817686710873985)
                      ·
                        rfl

theorem cell23_5153610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_5153610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153610 prefixEnd_5153610 := by exact prefixLift 5153610
  have htrace : WordTrace (prefixWord ++ tailWord_5153610) baseStart_5153610 baseEnd_5153610 := by
    simpa [prefixWord, tailWord_5153610, baseEnd_5153610] using wordTrace_append hprefix tailTrace_5153610
  have hstable : (prefixWord ++ tailWord_5153610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153610).length < 2 ^ (prefixWord ++ tailWord_5153610).sum := by decide
  have hdescent : baseEnd_5153610 < baseStart_5153610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153628 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5153628 : Nat := 118140960795 + 5153628 * 2 ^ 59
def prefixEnd_5153628 : Nat := 4983230072969 + 3 ^ 40 * 5153628 * 2
def baseEnd_5153628 : Nat := 2646288278469467640448903

theorem tailTrace_5153628 : CollatzResearch.WordTrace tailWord_5153628 prefixEnd_5153628 2646288278469467640448903 := by
  unfold tailWord_5153628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93984127686646700216814769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125312170248862266955753025 93984127686646700216814769)
  ·
    refine ⟨70488095764985025162611077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93984127686646700216814769 70488095764985025162611077)
    ·
      refine ⟨13216517955934692217989577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70488095764985025162611077 13216517955934692217989577)
      ·
        refine ⟨9912388466951019163492183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13216517955934692217989577 9912388466951019163492183)
        ·
          refine ⟨14868582700426528745238275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9912388466951019163492183 14868582700426528745238275)
          ·
            refine ⟨22302874050639793117857413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868582700426528745238275 22302874050639793117857413)
            ·
              refine ⟨4181788884494961209598265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22302874050639793117857413 4181788884494961209598265)
              ·
                refine ⟨3136341663371220907198699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181788884494961209598265 3136341663371220907198699)
                ·
                  refine ⟨4704512495056831360798049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136341663371220907198699 4704512495056831360798049)
                  ·
                    refine ⟨3528384371292623520598537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704512495056831360798049 3528384371292623520598537)
                    ·
                      refine ⟨2646288278469467640448903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528384371292623520598537 2646288278469467640448903)
                      ·
                        rfl

theorem cell23_5153628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5153628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153628 prefixEnd_5153628 := by exact prefixLift 5153628
  have htrace : WordTrace (prefixWord ++ tailWord_5153628) baseStart_5153628 baseEnd_5153628 := by
    simpa [prefixWord, tailWord_5153628, baseEnd_5153628] using wordTrace_append hprefix tailTrace_5153628
  have hstable : (prefixWord ++ tailWord_5153628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153628).length < 2 ^ (prefixWord ++ tailWord_5153628).sum := by decide
  have hdescent : baseEnd_5153628 < baseStart_5153628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153654 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5153654 : Nat := 118140960795 + 5153654 * 2 ^ 59
def prefixEnd_5153654 : Nat := 4983230072969 + 3 ^ 40 * 5153654 * 2
def baseEnd_5153654 : Nat := 2646301628966484538723783

theorem tailTrace_5153654 : CollatzResearch.WordTrace tailWord_5153654 prefixEnd_5153654 2646301628966484538723783 := by
  unfold tailWord_5153654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748075229449950429629751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125312802447466137916050677 11748075229449950429629751)
  ·
    refine ⟨17622112844174925644444627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11748075229449950429629751 17622112844174925644444627)
    ·
      refine ⟨26433169266262388466666941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622112844174925644444627 26433169266262388466666941)
      ·
        refine ⟨9912438474848395675000103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26433169266262388466666941 9912438474848395675000103)
        ·
          refine ⟨14868657712272593512500155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9912438474848395675000103 14868657712272593512500155)
          ·
            refine ⟨22302986568408890268750233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868657712272593512500155 22302986568408890268750233)
            ·
              refine ⟨16727239926306667701562675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22302986568408890268750233 16727239926306667701562675)
              ·
                refine ⟨25090859889460001552344013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16727239926306667701562675 25090859889460001552344013)
                ·
                  refine ⟨9409072458547500582129005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25090859889460001552344013 9409072458547500582129005)
                  ·
                    refine ⟨3528402171955312718298377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9409072458547500582129005 3528402171955312718298377)
                    ·
                      refine ⟨2646301628966484538723783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528402171955312718298377 2646301628966484538723783)
                      ·
                        rfl

theorem cell23_5153654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5153654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153654 prefixEnd_5153654 := by exact prefixLift 5153654
  have htrace : WordTrace (prefixWord ++ tailWord_5153654) baseStart_5153654 baseEnd_5153654 := by
    simpa [prefixWord, tailWord_5153654, baseEnd_5153654] using wordTrace_append hprefix tailTrace_5153654
  have hstable : (prefixWord ++ tailWord_5153654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153654).length < 2 ^ (prefixWord ++ tailWord_5153654).sum := by decide
  have hdescent : baseEnd_5153654 < baseStart_5153654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153667 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 4, 2, 2]
def baseStart_5153667 : Nat := 118140960795 + 5153667 * 2 ^ 59
def prefixEnd_5153667 : Nat := 4983230072969 + 3 ^ 40 * 5153667 * 2
def baseEnd_5153667 : Nat := 2646308304214992987861223

theorem tailTrace_5153667 : CollatzResearch.WordTrace tailWord_5153667 prefixEnd_5153667 2646308304214992987861223 := by
  unfold tailWord_5153667
  simp only [CollatzResearch.WordTrace]
  refine ⟨187969677820152110094299255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125313118546768073396199503 187969677820152110094299255)
  ·
    refine ⟨281954516730228165141448883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187969677820152110094299255 281954516730228165141448883)
    ·
      refine ⟨422931775095342247712173325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281954516730228165141448883 422931775095342247712173325)
      ·
        refine ⟨158599415660753342892064997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 422931775095342247712173325 158599415660753342892064997)
        ·
          refine ⟨29737390436391251792262187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158599415660753342892064997 29737390436391251792262187)
          ·
            refine ⟨44606085654586877688393281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29737390436391251792262187 44606085654586877688393281)
            ·
              refine ⟨33454564240940158266294961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44606085654586877688393281 33454564240940158266294961)
              ·
                refine ⟨25090923180705118699721221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33454564240940158266294961 25090923180705118699721221)
                ·
                  refine ⟨4704548096382209756197729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25090923180705118699721221 4704548096382209756197729)
                  ·
                    refine ⟨3528411072286657317148297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704548096382209756197729 3528411072286657317148297)
                    ·
                      refine ⟨2646308304214992987861223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528411072286657317148297 2646308304214992987861223)
                      ·
                        rfl

theorem cell23_5153667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_5153667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153667 prefixEnd_5153667 := by exact prefixLift 5153667
  have htrace : WordTrace (prefixWord ++ tailWord_5153667) baseStart_5153667 baseEnd_5153667 := by
    simpa [prefixWord, tailWord_5153667, baseEnd_5153667] using wordTrace_append hprefix tailTrace_5153667
  have hstable : (prefixWord ++ tailWord_5153667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153667).length < 2 ^ (prefixWord ++ tailWord_5153667).sum := by decide
  have hdescent : baseEnd_5153667 < baseStart_5153667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153671 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_5153671 : Nat := 118140960795 + 5153671 * 2 ^ 59
def prefixEnd_5153671 : Nat := 4983230072969 + 3 ^ 40 * 5153671 * 2
def baseEnd_5153671 : Nat := 2646310358137610972211205

theorem tailTrace_5153671 : CollatzResearch.WordTrace tailWord_5153671 prefixEnd_5153671 2646310358137610972211205 := by
  unfold tailWord_5153671
  simp only [CollatzResearch.WordTrace]
  refine ⟨187969823712137618777444867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125313215808091745851629911 187969823712137618777444867)
  ·
    refine ⟨281954735568206428166167301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187969823712137618777444867 281954735568206428166167301)
    ·
      refine ⟨52866512919038705281156369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281954735568206428166167301 52866512919038705281156369)
      ·
        refine ⟨39649884689279028960867277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52866512919038705281156369 39649884689279028960867277)
        ·
          refine ⟨14868706758479635860325229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39649884689279028960867277 14868706758479635860325229)
          ·
            refine ⟨5575765034429863447621961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14868706758479635860325229 5575765034429863447621961)
            ·
              refine ⟨4181823775822397585716471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575765034429863447621961 4181823775822397585716471)
              ·
                refine ⟨6272735663733596378574707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181823775822397585716471 6272735663733596378574707)
                ·
                  refine ⟨9409103495600394567862061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272735663733596378574707 9409103495600394567862061)
                  ·
                    refine ⟨3528413810850147962948273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9409103495600394567862061 3528413810850147962948273)
                    ·
                      refine ⟨2646310358137610972211205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528413810850147962948273 2646310358137610972211205)
                      ·
                        rfl

theorem cell23_5153671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_5153671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153671 prefixEnd_5153671 := by exact prefixLift 5153671
  have htrace : WordTrace (prefixWord ++ tailWord_5153671) baseStart_5153671 baseEnd_5153671 := by
    simpa [prefixWord, tailWord_5153671, baseEnd_5153671] using wordTrace_append hprefix tailTrace_5153671
  have hstable : (prefixWord ++ tailWord_5153671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153671).length < 2 ^ (prefixWord ++ tailWord_5153671).sum := by decide
  have hdescent : baseEnd_5153671 < baseStart_5153671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153684 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5153684 : Nat := 118140960795 + 5153684 * 2 ^ 59
def prefixEnd_5153684 : Nat := 4983230072969 + 3 ^ 40 * 5153684 * 2
def baseEnd_5153684 : Nat := 2646317033386119421348645

theorem tailTrace_5153684 : CollatzResearch.WordTrace tailWord_5153684 prefixEnd_5153684 2646317033386119421348645 := by
  unfold tailWord_5153684
  simp only [CollatzResearch.WordTrace]
  refine ⟨93985148930545260998834053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125313531907393681331778737 93985148930545260998834053)
  ·
    refine ⟨17622215424477236437281385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93985148930545260998834053 17622215424477236437281385)
    ·
      refine ⟨13216661568357927327961039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17622215424477236437281385 13216661568357927327961039)
      ·
        refine ⟨19824992352536890991941559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13216661568357927327961039 19824992352536890991941559)
        ·
          refine ⟨29737488528805336487912339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19824992352536890991941559 29737488528805336487912339)
          ·
            refine ⟨44606232793208004731868509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29737488528805336487912339 44606232793208004731868509)
            ·
              refine ⟨16727337297453001774450691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44606232793208004731868509 16727337297453001774450691)
              ·
                refine ⟨25091005946179502661676037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16727337297453001774450691 25091005946179502661676037)
                ·
                  refine ⟨4704563614908656749064257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25091005946179502661676037 4704563614908656749064257)
                  ·
                    refine ⟨3528422711181492561798193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704563614908656749064257 3528422711181492561798193)
                    ·
                      refine ⟨2646317033386119421348645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528422711181492561798193 2646317033386119421348645)
                      ·
                        rfl

theorem cell23_5153684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5153684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153684 prefixEnd_5153684 := by exact prefixLift 5153684
  have htrace : WordTrace (prefixWord ++ tailWord_5153684) baseStart_5153684 baseEnd_5153684 := by
    simpa [prefixWord, tailWord_5153684, baseEnd_5153684] using wordTrace_append hprefix tailTrace_5153684
  have hstable : (prefixWord ++ tailWord_5153684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153684).length < 2 ^ (prefixWord ++ tailWord_5153684).sum := by decide
  have hdescent : baseEnd_5153684 < baseStart_5153684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153700 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_5153700 : Nat := 118140960795 + 5153700 * 2 ^ 59
def prefixEnd_5153700 : Nat := 4983230072969 + 3 ^ 40 * 5153700 * 2
def baseEnd_5153700 : Nat := 2646325249076591358748571

theorem tailTrace_5153700 : CollatzResearch.WordTrace tailWord_5153700 prefixEnd_5153700 2646325249076591358748571 := by
  unfold tailWord_5153700
  simp only [CollatzResearch.WordTrace]
  refine ⟨93985440714516278365125277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125313920952688371153500369 93985440714516278365125277)
  ·
    refine ⟨35244540267943604386921979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93985440714516278365125277 35244540267943604386921979)
    ·
      refine ⟨52866810401915406580382969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35244540267943604386921979 52866810401915406580382969)
      ·
        refine ⟨39650107801436554935287227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52866810401915406580382969 39650107801436554935287227)
        ·
          refine ⟨59475161702154832402930841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39650107801436554935287227 59475161702154832402930841)
          ·
            refine ⟨44606371276616124302198131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59475161702154832402930841 44606371276616124302198131)
            ·
              refine ⟨66909556914924186453297197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44606371276616124302198131 66909556914924186453297197)
              ·
                refine ⟨25091083843096569919986449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66909556914924186453297197 25091083843096569919986449)
                ·
                  refine ⟨18818312882322427439989837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25091083843096569919986449 18818312882322427439989837)
                  ·
                    refine ⟨7056867330870910289996189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18818312882322427439989837 7056867330870910289996189)
                    ·
                      refine ⟨2646325249076591358748571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056867330870910289996189 2646325249076591358748571)
                      ·
                        rfl

theorem cell23_5153700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_5153700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153700 prefixEnd_5153700 := by exact prefixLift 5153700
  have htrace : WordTrace (prefixWord ++ tailWord_5153700) baseStart_5153700 baseEnd_5153700 := by
    simpa [prefixWord, tailWord_5153700, baseEnd_5153700] using wordTrace_append hprefix tailTrace_5153700
  have hstable : (prefixWord ++ tailWord_5153700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153700).length < 2 ^ (prefixWord ++ tailWord_5153700).sum := by decide
  have hdescent : baseEnd_5153700 < baseStart_5153700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_5153723 : Nat := 118140960795 + 5153723 * 2 ^ 59
def prefixEnd_5153723 : Nat := 4983230072969 + 3 ^ 40 * 5153723 * 2
def baseEnd_5153723 : Nat := 2646337059131644768760965

theorem tailTrace_5153723 : CollatzResearch.WordTrace tailWord_5153723 prefixEnd_5153723 2646337059131644768760965 := by
  unfold tailWord_5153723
  simp only [CollatzResearch.WordTrace]
  refine ⟨187971720307949231658337823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125314480205299487772225215 187971720307949231658337823)
  ·
    refine ⟨281957580461923847487506735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187971720307949231658337823 281957580461923847487506735)
    ·
      refine ⟨422936370692885771231260103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281957580461923847487506735 422936370692885771231260103)
      ·
        refine ⟨634404556039328656846890155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422936370692885771231260103 634404556039328656846890155)
        ·
          refine ⟨951606834058992985270335233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634404556039328656846890155 951606834058992985270335233)
          ·
            refine ⟨713705125544244738952751425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951606834058992985270335233 713705125544244738952751425)
            ·
              refine ⟨535278844158183554214563569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713705125544244738952751425 535278844158183554214563569)
              ·
                refine ⟨401459133118637665660922677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535278844158183554214563569 401459133118637665660922677)
                ·
                  refine ⟨37636793729872281155711501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401459133118637665660922677 37636793729872281155711501)
                  ·
                    refine ⟨14113797648702105433391813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37636793729872281155711501 14113797648702105433391813)
                    ·
                      refine ⟨2646337059131644768760965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14113797648702105433391813 2646337059131644768760965)
                      ·
                        rfl

theorem cell23_5153723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_5153723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153723 prefixEnd_5153723 := by exact prefixLift 5153723
  have htrace : WordTrace (prefixWord ++ tailWord_5153723) baseStart_5153723 baseEnd_5153723 := by
    simpa [prefixWord, tailWord_5153723, baseEnd_5153723] using wordTrace_append hprefix tailTrace_5153723
  have hstable : (prefixWord ++ tailWord_5153723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153723).length < 2 ^ (prefixWord ++ tailWord_5153723).sum := by decide
  have hdescent : baseEnd_5153723 < baseStart_5153723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153774 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_5153774 : Nat := 118140960795 + 5153774 * 2 ^ 59
def prefixEnd_5153774 : Nat := 4983230072969 + 3 ^ 40 * 5153774 * 2
def baseEnd_5153774 : Nat := 2646363246645024069223231

theorem tailTrace_5153774 : CollatzResearch.WordTrace tailWord_5153774 prefixEnd_5153774 2646363246645024069223231 := by
  unfold tailWord_5153774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496697553845558421055547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125315720287176311578962917 23496697553845558421055547)
  ·
    refine ⟨35245046330768337631583321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23496697553845558421055547 35245046330768337631583321)
    ·
      refine ⟨26433784748076253223687491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35245046330768337631583321 26433784748076253223687491)
      ·
        refine ⟨39650677122114379835531237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26433784748076253223687491 39650677122114379835531237)
        ·
          refine ⟨7434501960396446219162107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39650677122114379835531237 7434501960396446219162107)
          ·
            refine ⟨11151752940594669328743161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434501960396446219162107 11151752940594669328743161)
            ·
              refine ⟨8363814705446001996557371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11151752940594669328743161 8363814705446001996557371)
              ·
                refine ⟨12545722058169002994836057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363814705446001996557371 12545722058169002994836057)
                ·
                  refine ⟨9409291543626752246127043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12545722058169002994836057 9409291543626752246127043)
                  ·
                    refine ⟨14113937315440128369190565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9409291543626752246127043 14113937315440128369190565)
                    ·
                      refine ⟨2646363246645024069223231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14113937315440128369190565 2646363246645024069223231)
                      ·
                        rfl

theorem cell23_5153774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_5153774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153774 prefixEnd_5153774 := by exact prefixLift 5153774
  have htrace : WordTrace (prefixWord ++ tailWord_5153774) baseStart_5153774 baseEnd_5153774 := by
    simpa [prefixWord, tailWord_5153774, baseEnd_5153774] using wordTrace_append hprefix tailTrace_5153774
  have hstable : (prefixWord ++ tailWord_5153774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153774).length < 2 ^ (prefixWord ++ tailWord_5153774).sum := by decide
  have hdescent : baseEnd_5153774 < baseStart_5153774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153777 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_5153777 : Nat := 118140960795 + 5153777 * 2 ^ 59
def prefixEnd_5153777 : Nat := 4983230072969 + 3 ^ 40 * 5153777 * 2
def baseEnd_5153777 : Nat := 2646364787086987557485717

theorem tailTrace_5153777 : CollatzResearch.WordTrace tailWord_5153777 prefixEnd_5153777 2646364787086987557485717 := by
  unfold tailWord_5153777
  simp only [CollatzResearch.WordTrace]
  refine ⟨187973689849753598880803585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125315793233169065920535723 187973689849753598880803585)
  ·
    refine ⟨140980267387315199160602689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187973689849753598880803585 140980267387315199160602689)
    ·
      refine ⟨105735200540486399370452017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140980267387315199160602689 105735200540486399370452017)
      ·
        refine ⟨79301400405364799527839013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105735200540486399370452017 79301400405364799527839013)
        ·
          refine ⟨14869012576005899911469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79301400405364799527839013 14869012576005899911469815)
          ·
            refine ⟨22303518864008849867204723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14869012576005899911469815 22303518864008849867204723)
            ·
              refine ⟨33455278296013274800807085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22303518864008849867204723 33455278296013274800807085)
              ·
                refine ⟨12545729361004978050302657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33455278296013274800807085 12545729361004978050302657)
                ·
                  refine ⟨9409297020753733537726993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12545729361004978050302657 9409297020753733537726993)
                  ·
                    refine ⟨7056972765565300153295245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9409297020753733537726993 7056972765565300153295245)
                    ·
                      refine ⟨2646364787086987557485717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7056972765565300153295245 2646364787086987557485717)
                      ·
                        rfl

theorem cell23_5153777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_5153777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153777 prefixEnd_5153777 := by exact prefixLift 5153777
  have htrace : WordTrace (prefixWord ++ tailWord_5153777) baseStart_5153777 baseEnd_5153777 := by
    simpa [prefixWord, tailWord_5153777, baseEnd_5153777] using wordTrace_append hprefix tailTrace_5153777
  have hstable : (prefixWord ++ tailWord_5153777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153777).length < 2 ^ (prefixWord ++ tailWord_5153777).sum := by decide
  have hdescent : baseEnd_5153777 < baseStart_5153777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153817 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 4, 3, 2]
def baseStart_5153817 : Nat := 118140960795 + 5153817 * 2 ^ 59
def prefixEnd_5153817 : Nat := 4983230072969 + 3 ^ 40 * 5153817 * 2
def baseEnd_5153817 : Nat := 2646385326313167400985533

theorem tailTrace_5153817 : CollatzResearch.WordTrace tailWord_5153817 prefixEnd_5153817 2646385326313167400985533 := by
  unfold tailWord_5153817
  simp only [CollatzResearch.WordTrace]
  refine ⟨187975148769608685712259705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125316765846405790474839803 187975148769608685712259705)
  ·
    refine ⟨140981361577206514284194779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187975148769608685712259705 140981361577206514284194779)
    ·
      refine ⟨211472042365809771426292169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140981361577206514284194779 211472042365809771426292169)
      ·
        refine ⟨158604031774357328569719127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211472042365809771426292169 158604031774357328569719127)
        ·
          refine ⟨237906047661535992854578691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158604031774357328569719127 237906047661535992854578691)
          ·
            refine ⟨356859071492303989281868037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237906047661535992854578691 356859071492303989281868037)
            ·
              refine ⟨66911075904806997990350257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356859071492303989281868037 66911075904806997990350257)
              ·
                refine ⟨50183306928605248492762693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66911075904806997990350257 50183306928605248492762693)
                ·
                  refine ⟨9409370049113484092393005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50183306928605248492762693 9409370049113484092393005)
                  ·
                    refine ⟨3528513768417556534647377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9409370049113484092393005 3528513768417556534647377)
                    ·
                      refine ⟨2646385326313167400985533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528513768417556534647377 2646385326313167400985533)
                      ·
                        rfl

theorem cell23_5153817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_5153817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153817 prefixEnd_5153817 := by exact prefixLift 5153817
  have htrace : WordTrace (prefixWord ++ tailWord_5153817) baseStart_5153817 baseEnd_5153817 := by
    simpa [prefixWord, tailWord_5153817, baseEnd_5153817] using wordTrace_append hprefix tailTrace_5153817
  have hstable : (prefixWord ++ tailWord_5153817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153817).length < 2 ^ (prefixWord ++ tailWord_5153817).sum := by decide
  have hdescent : baseEnd_5153817 < baseStart_5153817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153840 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_5153840 : Nat := 118140960795 + 5153840 * 2 ^ 59
def prefixEnd_5153840 : Nat := 4983230072969 + 3 ^ 40 * 5153840 * 2
def baseEnd_5153840 : Nat := 882132378789406936999309

theorem tailTrace_5153840 : CollatzResearch.WordTrace tailWord_5153840 prefixEnd_5153840 882132378789406936999309 := by
  unfold tailWord_5153840
  simp only [CollatzResearch.WordTrace]
  refine ⟨93987993824262680320173487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125317325099016907093564649 93987993824262680320173487)
  ·
    refine ⟨140981990736394020480260231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93987993824262680320173487 140981990736394020480260231)
    ·
      refine ⟨211472986104591030720390347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140981990736394020480260231 211472986104591030720390347)
      ·
        refine ⟨317209479156886546080585521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211472986104591030720390347 317209479156886546080585521)
        ·
          refine ⟨237907109367664909560439141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317209479156886546080585521 237907109367664909560439141)
          ·
            refine ⟨44607583006437170542582339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237907109367664909560439141 44607583006437170542582339)
            ·
              refine ⟨66911374509655755813873509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44607583006437170542582339 66911374509655755813873509)
              ·
                refine ⟨12545882720560454215101283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66911374509655755813873509 12545882720560454215101283)
                ·
                  refine ⟨18818824080840681322651925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545882720560454215101283 18818824080840681322651925)
                  ·
                    refine ⟨882132378789406936999309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18818824080840681322651925 882132378789406936999309)
                    ·
                      rfl

theorem cell23_5153840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_5153840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153840 prefixEnd_5153840 := by exact prefixLift 5153840
  have htrace : WordTrace (prefixWord ++ tailWord_5153840) baseStart_5153840 baseEnd_5153840 := by
    simpa [prefixWord, tailWord_5153840, baseEnd_5153840] using wordTrace_append hprefix tailTrace_5153840
  have hstable : (prefixWord ++ tailWord_5153840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153840).length < 2 ^ (prefixWord ++ tailWord_5153840).sum := by decide
  have hdescent : baseEnd_5153840 < baseStart_5153840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153841 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_5153841 : Nat := 118140960795 + 5153841 * 2 ^ 59
def prefixEnd_5153841 : Nat := 4983230072969 + 3 ^ 40 * 5153841 * 2
def baseEnd_5153841 : Nat := 2646397649848875307085423

theorem tailTrace_5153841 : CollatzResearch.WordTrace tailWord_5153841 prefixEnd_5153841 2646397649848875307085423 := by
  unfold tailWord_5153841
  simp only [CollatzResearch.WordTrace]
  refine ⟨187976024121521737811133377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125317349414347825207422251 187976024121521737811133377)
  ·
    refine ⟨140982018091141303358350033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187976024121521737811133377 140982018091141303358350033)
    ·
      refine ⟨105736513568355977518762525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140982018091141303358350033 105736513568355977518762525)
      ·
        refine ⟨39651192588133491569535947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105736513568355977518762525 39651192588133491569535947)
        ·
          refine ⟨59476788882200237354303921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39651192588133491569535947 59476788882200237354303921)
          ·
            refine ⟨44607591661650178015727941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59476788882200237354303921 44607591661650178015727941)
            ·
              refine ⟨8363923436559408377948989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44607591661650178015727941 8363923436559408377948989)
              ·
                refine ⟨3136471288709778141730871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8363923436559408377948989 3136471288709778141730871)
                ·
                  refine ⟨4704706933064667212596307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136471288709778141730871 4704706933064667212596307)
                  ·
                    refine ⟨7057060399597000818894461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704706933064667212596307 7057060399597000818894461)
                    ·
                      refine ⟨2646397649848875307085423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7057060399597000818894461 2646397649848875307085423)
                      ·
                        rfl

theorem cell23_5153841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_5153841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153841 prefixEnd_5153841 := by exact prefixLift 5153841
  have htrace : WordTrace (prefixWord ++ tailWord_5153841) baseStart_5153841 baseEnd_5153841 := by
    simpa [prefixWord, tailWord_5153841, baseEnd_5153841] using wordTrace_append hprefix tailTrace_5153841
  have hstable : (prefixWord ++ tailWord_5153841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153841).length < 2 ^ (prefixWord ++ tailWord_5153841).sum := by decide
  have hdescent : baseEnd_5153841 < baseStart_5153841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153870 : List Nat := [4, 1, 1, 1, 1, 3, 2, 10]
def baseStart_5153870 : Nat := 118140960795 + 5153870 * 2 ^ 59
def prefixEnd_5153870 : Nat := 4983230072969 + 3 ^ 40 * 5153870 * 2
def baseEnd_5153870 : Nat := 98015279288439099763807

theorem tailTrace_5153870 : CollatzResearch.WordTrace tailWord_5153870 prefixEnd_5153870 98015279288439099763807 := by
  unfold tailWord_5153870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497135229802084470492383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125318054558944450509292709 23497135229802084470492383)
  ·
    refine ⟨35245702844703126705738575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23497135229802084470492383 35245702844703126705738575)
    ·
      refine ⟨52868554267054690058607863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35245702844703126705738575 52868554267054690058607863)
      ·
        refine ⟨79302831400582035087911795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52868554267054690058607863 79302831400582035087911795)
        ·
          refine ⟨118954247100873052631867693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79302831400582035087911795 118954247100873052631867693)
          ·
            refine ⟨44607842662827394736950385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118954247100873052631867693 44607842662827394736950385)
            ·
              refine ⟨33455881997120546052712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44607842662827394736950385 33455881997120546052712789)
              ·
                refine ⟨98015279288439099763807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33455881997120546052712789 98015279288439099763807)
                ·
                  rfl

theorem cell23_5153870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_5153870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153870 prefixEnd_5153870 := by exact prefixLift 5153870
  have htrace : WordTrace (prefixWord ++ tailWord_5153870) baseStart_5153870 baseEnd_5153870 := by
    simpa [prefixWord, tailWord_5153870, baseEnd_5153870] using wordTrace_append hprefix tailTrace_5153870
  have hstable : (prefixWord ++ tailWord_5153870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153870).length < 2 ^ (prefixWord ++ tailWord_5153870).sum := by decide
  have hdescent : baseEnd_5153870 < baseStart_5153870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153874 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_5153874 : Nat := 118140960795 + 5153874 * 2 ^ 59
def prefixEnd_5153874 : Nat := 4983230072969 + 3 ^ 40 * 5153874 * 2
def baseEnd_5153874 : Nat := 882138198236824559324257

theorem tailTrace_5153874 : CollatzResearch.WordTrace tailWord_5153874 prefixEnd_5153874 882138198236824559324257 := by
  unfold tailWord_5153874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46994306932600546111771169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125318151820268122964723117 46994306932600546111771169)
  ·
    refine ⟨35245730199450409583828377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46994306932600546111771169 35245730199450409583828377)
    ·
      refine ⟨26434297649587807187871283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35245730199450409583828377 26434297649587807187871283)
      ·
        refine ⟨39651446474381710781806925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26434297649587807187871283 39651446474381710781806925)
        ·
          refine ⟨14869292427893141543177597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39651446474381710781806925 14869292427893141543177597)
          ·
            refine ⟨5575984660459928078691599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14869292427893141543177597 5575984660459928078691599)
            ·
              refine ⟨8363976990689892118037399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575984660459928078691599 8363976990689892118037399)
              ·
                refine ⟨12545965486034838177056099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363976990689892118037399 12545965486034838177056099)
                ·
                  refine ⟨18818948229052257265584149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545965486034838177056099 18818948229052257265584149)
                  ·
                    refine ⟨882138198236824559324257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18818948229052257265584149 882138198236824559324257)
                    ·
                      rfl

theorem cell23_5153874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_5153874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153874 prefixEnd_5153874 := by exact prefixLift 5153874
  have htrace : WordTrace (prefixWord ++ tailWord_5153874) baseStart_5153874 baseEnd_5153874 := by
    simpa [prefixWord, tailWord_5153874, baseEnd_5153874] using wordTrace_append hprefix tailTrace_5153874
  have hstable : (prefixWord ++ tailWord_5153874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153874).length < 2 ^ (prefixWord ++ tailWord_5153874).sum := by decide
  have hdescent : baseEnd_5153874 < baseStart_5153874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153878 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5153878 : Nat := 118140960795 + 5153878 * 2 ^ 59
def prefixEnd_5153878 : Nat := 4983230072969 + 3 ^ 40 * 5153878 * 2
def baseEnd_5153878 : Nat := 882138882877697220774251

theorem tailTrace_5153878 : CollatzResearch.WordTrace tailWord_5153878 prefixEnd_5153878 882138882877697220774251 := by
  unfold tailWord_5153878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748585851399230820639393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125318249081591795420153525 11748585851399230820639393)
  ·
    refine ⟨8811439388549423115479545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11748585851399230820639393 8811439388549423115479545)
    ·
      refine ⟨6608579541412067336609659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811439388549423115479545 6608579541412067336609659)
      ·
        refine ⟨9912869312118101004914489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608579541412067336609659 9912869312118101004914489)
        ·
          refine ⟨7434651984088575753685867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9912869312118101004914489 7434651984088575753685867)
          ·
            refine ⟨11151977976132863630528801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434651984088575753685867 11151977976132863630528801)
            ·
              refine ⟨8363983482099647722896601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11151977976132863630528801 8363983482099647722896601)
              ·
                refine ⟨6272987611574735792172451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8363983482099647722896601 6272987611574735792172451)
                ·
                  refine ⟨9409481417362103688258677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6272987611574735792172451 9409481417362103688258677)
                  ·
                    refine ⟨882138882877697220774251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9409481417362103688258677 882138882877697220774251)
                    ·
                      rfl

theorem cell23_5153878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5153878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153878 prefixEnd_5153878 := by exact prefixLift 5153878
  have htrace : WordTrace (prefixWord ++ tailWord_5153878) baseStart_5153878 baseEnd_5153878 := by
    simpa [prefixWord, tailWord_5153878, baseEnd_5153878] using wordTrace_append hprefix tailTrace_5153878
  have hstable : (prefixWord ++ tailWord_5153878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153878).length < 2 ^ (prefixWord ++ tailWord_5153878).sum := by decide
  have hdescent : baseEnd_5153878 < baseStart_5153878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153957 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_5153957 : Nat := 118140960795 + 5153957 * 2 ^ 59
def prefixEnd_5153957 : Nat := 4983230072969 + 3 ^ 40 * 5153957 * 2
def baseEnd_5153957 : Nat := 2646457213604796853234889

theorem tailTrace_5153957 : CollatzResearch.WordTrace tailWord_5153957 prefixEnd_5153957 2646457213604796853234889 := by
  unfold tailWord_5153957
  simp only [CollatzResearch.WordTrace]
  refine ⟨187980254989101489622356125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125320169992734326414904083 187980254989101489622356125)
  ·
    refine ⟨70492595620913058608383547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187980254989101489622356125 70492595620913058608383547)
    ·
      refine ⟨105738893431369587912575321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70492595620913058608383547 105738893431369587912575321)
      ·
        refine ⟨79304170073527190934431491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105738893431369587912575321 79304170073527190934431491)
        ·
          refine ⟨118956255110290786401647237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79304170073527190934431491 118956255110290786401647237)
          ·
            refine ⟨22304297833179522450308857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118956255110290786401647237 22304297833179522450308857)
            ·
              refine ⟨16728223374884641837731643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22304297833179522450308857 16728223374884641837731643)
              ·
                refine ⟨25092335062326962756597465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16728223374884641837731643 25092335062326962756597465)
                ·
                  refine ⟨18819251296745222067448099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25092335062326962756597465 18819251296745222067448099)
                  ·
                    refine ⟨28228876945117833101172149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18819251296745222067448099 28228876945117833101172149)
                    ·
                      refine ⟨2646457213604796853234889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28228876945117833101172149 2646457213604796853234889)
                      ·
                        rfl

theorem cell23_5153957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_5153957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153957 prefixEnd_5153957 := by exact prefixLift 5153957
  have htrace : WordTrace (prefixWord ++ tailWord_5153957) baseStart_5153957 baseEnd_5153957 := by
    simpa [prefixWord, tailWord_5153957, baseEnd_5153957] using wordTrace_append hprefix tailTrace_5153957
  have hstable : (prefixWord ++ tailWord_5153957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153957).length < 2 ^ (prefixWord ++ tailWord_5153957).sum := by decide
  have hdescent : baseEnd_5153957 < baseStart_5153957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153971 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 2, 2, 2]
def baseStart_5153971 : Nat := 118140960795 + 5153971 * 2 ^ 59
def prefixEnd_5153971 : Nat := 4983230072969 + 3 ^ 40 * 5153971 * 2
def baseEnd_5153971 : Nat := 2646464402333959798459825

theorem tailTrace_5153971 : CollatzResearch.WordTrace tailWord_5153971 prefixEnd_5153971 2646464402333959798459825 := by
  unfold tailWord_5153971
  simp only [CollatzResearch.WordTrace]
  refine ⟨187980765611050770013365767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125320510407367180008910511 187980765611050770013365767)
  ·
    refine ⟨281971148416576155020048651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187980765611050770013365767 281971148416576155020048651)
    ·
      refine ⟨422956722624864232530072977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281971148416576155020048651 422956722624864232530072977)
      ·
        refine ⟨317217541968648174397554733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422956722624864232530072977 317217541968648174397554733)
        ·
          refine ⟨118956578238243065399083025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317217541968648174397554733 118956578238243065399083025)
          ·
            refine ⟨89217433678682299049312269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118956578238243065399083025 89217433678682299049312269)
            ·
              refine ⟨33456537629505862143492101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89217433678682299049312269 33456537629505862143492101)
              ·
                refine ⟨6273100805532349151904769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33456537629505862143492101 6273100805532349151904769)
                ·
                  refine ⟨4704825604149261863928577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6273100805532349151904769 4704825604149261863928577)
                  ·
                    refine ⟨3528619203111946397946433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704825604149261863928577 3528619203111946397946433)
                    ·
                      refine ⟨2646464402333959798459825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528619203111946397946433 2646464402333959798459825)
                      ·
                        rfl

theorem cell23_5153971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2, 2].length) (baseStart_5153971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153971 prefixEnd_5153971 := by exact prefixLift 5153971
  have htrace : WordTrace (prefixWord ++ tailWord_5153971) baseStart_5153971 baseEnd_5153971 := by
    simpa [prefixWord, tailWord_5153971, baseEnd_5153971] using wordTrace_append hprefix tailTrace_5153971
  have hstable : (prefixWord ++ tailWord_5153971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153971).length < 2 ^ (prefixWord ++ tailWord_5153971).sum := by decide
  have hdescent : baseEnd_5153971 < baseStart_5153971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153984 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_5153984 : Nat := 118140960795 + 5153984 * 2 ^ 59
def prefixEnd_5153984 : Nat := 4983230072969 + 3 ^ 40 * 5153984 * 2
def baseEnd_5153984 : Nat := 2646471077582468247597265

theorem tailTrace_5153984 : CollatzResearch.WordTrace tailWord_5153984 prefixEnd_5153984 2646471077582468247597265 := by
  unfold tailWord_5153984
  simp only [CollatzResearch.WordTrace]
  refine ⟨93990619880001836616794503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125320826506669115489059337 93990619880001836616794503)
  ·
    refine ⟨140985929820002754925191755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93990619880001836616794503 140985929820002754925191755)
    ·
      refine ⟨211478894730004132387787633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140985929820002754925191755 211478894730004132387787633)
      ·
        refine ⟨158609171047503099290840725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211478894730004132387787633 158609171047503099290840725)
        ·
          refine ⟨7434804892851707779258159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158609171047503099290840725 7434804892851707779258159)
          ·
            refine ⟨11152207339277561668887239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434804892851707779258159 11152207339277561668887239)
            ·
              refine ⟨16728311008916342503330859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11152207339277561668887239 16728311008916342503330859)
              ·
                refine ⟨25092466513374513754996289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16728311008916342503330859 25092466513374513754996289)
                ·
                  refine ⟨18819349885030885316247217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25092466513374513754996289 18819349885030885316247217)
                  ·
                    refine ⟨14114512413773163987185413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18819349885030885316247217 14114512413773163987185413)
                    ·
                      refine ⟨2646471077582468247597265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14114512413773163987185413 2646471077582468247597265)
                      ·
                        rfl

theorem cell23_5153984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_5153984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153984 prefixEnd_5153984 := by exact prefixLift 5153984
  have htrace : WordTrace (prefixWord ++ tailWord_5153984) baseStart_5153984 baseEnd_5153984 := by
    simpa [prefixWord, tailWord_5153984, baseEnd_5153984] using wordTrace_append hprefix tailTrace_5153984
  have hstable : (prefixWord ++ tailWord_5153984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153984).length < 2 ^ (prefixWord ++ tailWord_5153984).sum := by decide
  have hdescent : baseEnd_5153984 < baseStart_5153984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153988 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5153988 : Nat := 118140960795 + 5153988 * 2 ^ 59
def prefixEnd_5153988 : Nat := 4983230072969 + 3 ^ 40 * 5153988 * 2
def baseEnd_5153988 : Nat := 2646473131505086231947247

theorem tailTrace_5153988 : CollatzResearch.WordTrace tailWord_5153988 prefixEnd_5153988 2646473131505086231947247 := by
  unfold tailWord_5153988
  simp only [CollatzResearch.WordTrace]
  refine ⟨93990692825994590958367309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125320923767992787944489745 93990692825994590958367309)
  ·
    refine ⟨35246509809747971609387741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93990692825994590958367309 35246509809747971609387741)
    ·
      refine ⟨13217441178655489353520403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35246509809747971609387741 13217441178655489353520403)
      ·
        refine ⟨19826161767983234030280605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13217441178655489353520403 19826161767983234030280605)
        ·
          refine ⟨7434810662993712761355227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19826161767983234030280605 7434810662993712761355227)
          ·
            refine ⟨11152215994490569142032841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434810662993712761355227 11152215994490569142032841)
            ·
              refine ⟨8364161995867926856524631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11152215994490569142032841 8364161995867926856524631)
              ·
                refine ⟨12546242993801890284786947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364161995867926856524631 12546242993801890284786947)
                ·
                  refine ⟨18819364490702835427180421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12546242993801890284786947 18819364490702835427180421)
                  ·
                    refine ⟨3528630842006781642596329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18819364490702835427180421 3528630842006781642596329)
                    ·
                      refine ⟨2646473131505086231947247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528630842006781642596329 2646473131505086231947247)
                      ·
                        rfl

theorem cell23_5153988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5153988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5153988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5153988 prefixEnd_5153988 := by exact prefixLift 5153988
  have htrace : WordTrace (prefixWord ++ tailWord_5153988) baseStart_5153988 baseEnd_5153988 := by
    simpa [prefixWord, tailWord_5153988, baseEnd_5153988] using wordTrace_append hprefix tailTrace_5153988
  have hstable : (prefixWord ++ tailWord_5153988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153988).length < 2 ^ (prefixWord ++ tailWord_5153988).sum := by decide
  have hdescent : baseEnd_5153988 < baseStart_5153988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154057 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_5154057 : Nat := 118140960795 + 5154057 * 2 ^ 59
def prefixEnd_5154057 : Nat := 4983230072969 + 3 ^ 40 * 5154057 * 2
def baseEnd_5154057 : Nat := 2646508561670246461984429

theorem tailTrace_5154057 : CollatzResearch.WordTrace tailWord_5154057 prefixEnd_5154057 2646508561670246461984429 := by
  unfold tailWord_5154057
  simp only [CollatzResearch.WordTrace]
  refine ⟨187983902288739206700996425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125322601525826137800664283 187983902288739206700996425)
  ·
    refine ⟨140987926716554405025747319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187983902288739206700996425 140987926716554405025747319)
    ·
      refine ⟨211481890074831607538620979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140987926716554405025747319 211481890074831607538620979)
      ·
        refine ⟨317222835112247411307931469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211481890074831607538620979 317222835112247411307931469)
        ·
          refine ⟨118958563167092779240474301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317222835112247411307931469 118958563167092779240474301)
          ·
            refine ⟨44609461187659792215177863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118958563167092779240474301 44609461187659792215177863)
            ·
              refine ⟨66914191781489688322766795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44609461187659792215177863 66914191781489688322766795)
              ·
                refine ⟨100371287672234532484150193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66914191781489688322766795 100371287672234532484150193)
                ·
                  refine ⟨75278465754175899363112645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100371287672234532484150193 75278465754175899363112645)
                  ·
                    refine ⟨14114712328907981130583621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75278465754175899363112645 14114712328907981130583621)
                    ·
                      refine ⟨2646508561670246461984429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14114712328907981130583621 2646508561670246461984429)
                      ·
                        rfl

theorem cell23_5154057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_5154057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154057 prefixEnd_5154057 := by exact prefixLift 5154057
  have htrace : WordTrace (prefixWord ++ tailWord_5154057) baseStart_5154057 baseEnd_5154057 := by
    simpa [prefixWord, tailWord_5154057, baseEnd_5154057] using wordTrace_append hprefix tailTrace_5154057
  have hstable : (prefixWord ++ tailWord_5154057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154057).length < 2 ^ (prefixWord ++ tailWord_5154057).sum := by decide
  have hdescent : baseEnd_5154057 < baseStart_5154057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154084 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 6]
def baseStart_5154084 : Nat := 118140960795 + 5154084 * 2 ^ 59
def prefixEnd_5154084 : Nat := 4983230072969 + 3 ^ 40 * 5154084 * 2
def baseEnd_5154084 : Nat := 294058047294213095149645

theorem tailTrace_5154084 : CollatzResearch.WordTrace tailWord_5154084 prefixEnd_5154084 294058047294213095149645 := by
  unfold tailWord_5154084
  simp only [CollatzResearch.WordTrace]
  refine ⟨93992443529820695156114653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125323258039760926874819537 93992443529820695156114653)
  ·
    refine ⟨35247166323682760683542995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93992443529820695156114653 35247166323682760683542995)
    ·
      refine ⟨52870749485524141025314493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35247166323682760683542995 52870749485524141025314493)
      ·
        refine ⟨19826531057071552884492935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52870749485524141025314493 19826531057071552884492935)
        ·
          refine ⟨29739796585607329326739403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19826531057071552884492935 29739796585607329326739403)
          ·
            refine ⟨44609694878410993990109105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29739796585607329326739403 44609694878410993990109105)
            ·
              refine ⟨33457271158808245492581829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44609694878410993990109105 33457271158808245492581829)
              ·
                refine ⟨6273238342276546029859093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33457271158808245492581829 6273238342276546029859093)
                ·
                  refine ⟨294058047294213095149645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6273238342276546029859093 294058047294213095149645)
                  ·
                    rfl

theorem cell23_5154084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_5154084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154084 prefixEnd_5154084 := by exact prefixLift 5154084
  have htrace : WordTrace (prefixWord ++ tailWord_5154084) baseStart_5154084 baseEnd_5154084 := by
    simpa [prefixWord, tailWord_5154084, baseEnd_5154084] using wordTrace_append hprefix tailTrace_5154084
  have hstable : (prefixWord ++ tailWord_5154084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154084).length < 2 ^ (prefixWord ++ tailWord_5154084).sum := by decide
  have hdescent : baseEnd_5154084 < baseStart_5154084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154088 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5154088 : Nat := 118140960795 + 5154088 * 2 ^ 59
def prefixEnd_5154088 : Nat := 4983230072969 + 3 ^ 40 * 5154088 * 2
def baseEnd_5154088 : Nat := 882174826523511946898929

theorem tailTrace_5154088 : CollatzResearch.WordTrace tailWord_5154088 prefixEnd_5154088 882174826523511946898929 := by
  unfold tailWord_5154088
  simp only [CollatzResearch.WordTrace]
  refine ⟨93992516475813449497687459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125323355301084599330249945 93992516475813449497687459)
  ·
    refine ⟨140988774713720174246531189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93992516475813449497687459 140988774713720174246531189)
    ·
      refine ⟨13217697629411266335612299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140988774713720174246531189 13217697629411266335612299)
      ·
        refine ⟨19826546444116899503418449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13217697629411266335612299 19826546444116899503418449)
        ·
          refine ⟨14869909833087674627563837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19826546444116899503418449 14869909833087674627563837)
          ·
            refine ⟨5576216187407877985336439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14869909833087674627563837 5576216187407877985336439)
            ·
              refine ⟨8364324281111816978004659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576216187407877985336439 8364324281111816978004659)
              ·
                refine ⟨12546486421667725467006989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364324281111816978004659 12546486421667725467006989)
                ·
                  refine ⟨4704932408125397050127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12546486421667725467006989 4704932408125397050127621)
                  ·
                    refine ⟨882174826523511946898929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704932408125397050127621 882174826523511946898929)
                    ·
                      rfl

theorem cell23_5154088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5154088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154088 prefixEnd_5154088 := by exact prefixLift 5154088
  have htrace : WordTrace (prefixWord ++ tailWord_5154088) baseStart_5154088 baseEnd_5154088 := by
    simpa [prefixWord, tailWord_5154088, baseEnd_5154088] using wordTrace_append hprefix tailTrace_5154088
  have hstable : (prefixWord ++ tailWord_5154088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154088).length < 2 ^ (prefixWord ++ tailWord_5154088).sum := by decide
  have hdescent : baseEnd_5154088 < baseStart_5154088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154101 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 6]
def baseStart_5154101 : Nat := 118140960795 + 5154101 * 2 ^ 59
def prefixEnd_5154101 : Nat := 4983230072969 + 3 ^ 40 * 5154101 * 2
def baseEnd_5154101 : Nat := 294059017202116032203803

theorem tailTrace_5154101 : CollatzResearch.WordTrace tailWord_5154101 prefixEnd_5154101 294059017202116032203803 := by
  unfold tailWord_5154101
  simp only [CollatzResearch.WordTrace]
  refine ⟨187985507100579802215598157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125323671400386534810398771 187985507100579802215598157)
  ·
    refine ⟨70494565162717425830849309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187985507100579802215598157 70494565162717425830849309)
    ·
      refine ⟨26435461936019034686568491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70494565162717425830849309 26435461936019034686568491)
      ·
        refine ⟨39653192904028552029852737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26435461936019034686568491 39653192904028552029852737)
        ·
          refine ⟨29739894678021414022389553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39653192904028552029852737 29739894678021414022389553)
          ·
            refine ⟨22304921008516060516792165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29739894678021414022389553 22304921008516060516792165)
            ·
              refine ⟨4182172689096761346898531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22304921008516060516792165 4182172689096761346898531)
              ·
                refine ⟨6273259033645142020347797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182172689096761346898531 6273259033645142020347797)
                ·
                  refine ⟨294059017202116032203803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6273259033645142020347797 294059017202116032203803)
                  ·
                    rfl

theorem cell23_5154101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_5154101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154101 prefixEnd_5154101 := by exact prefixLift 5154101
  have htrace : WordTrace (prefixWord ++ tailWord_5154101) baseStart_5154101 baseEnd_5154101 := by
    simpa [prefixWord, tailWord_5154101, baseEnd_5154101] using wordTrace_append hprefix tailTrace_5154101
  have hstable : (prefixWord ++ tailWord_5154101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154101).length < 2 ^ (prefixWord ++ tailWord_5154101).sum := by decide
  have hdescent : baseEnd_5154101 < baseStart_5154101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154121 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 2, 3, 2]
def baseStart_5154121 : Nat := 118140960795 + 5154121 * 2 ^ 59
def prefixEnd_5154121 : Nat := 4983230072969 + 3 ^ 40 * 5154121 * 2
def baseEnd_5154121 : Nat := 2646541424432134211584135

theorem tailTrace_5154121 : CollatzResearch.WordTrace tailWord_5154121 prefixEnd_5154121 2646541424432134211584135 := by
  unfold tailWord_5154121
  simp only [CollatzResearch.WordTrace]
  refine ⟨187986236560507345631326217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125324157707004897087550811 187986236560507345631326217)
  ·
    refine ⟨140989677420380509223494663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187986236560507345631326217 140989677420380509223494663)
    ·
      refine ⟨211484516130570763835241995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140989677420380509223494663 211484516130570763835241995)
      ·
        refine ⟨317226774195856145752862993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211484516130570763835241995 317226774195856145752862993)
        ·
          refine ⟨237920080646892109314647245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317226774195856145752862993 237920080646892109314647245)
          ·
            refine ⟨89220030242584540992992717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237920080646892109314647245 89220030242584540992992717)
            ·
              refine ⟨33457511340969202872372269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89220030242584540992992717 33457511340969202872372269)
              ·
                refine ⟨12546566752863451077139601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33457511340969202872372269 12546566752863451077139601)
                ·
                  refine ⟨9409925064647588307854701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12546566752863451077139601 9409925064647588307854701)
                  ·
                    refine ⟨3528721899242845615445513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9409925064647588307854701 3528721899242845615445513)
                    ·
                      refine ⟨2646541424432134211584135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528721899242845615445513 2646541424432134211584135)
                      ·
                        rfl

theorem cell23_5154121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3, 2].length) (baseStart_5154121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154121 prefixEnd_5154121 := by exact prefixLift 5154121
  have htrace : WordTrace (prefixWord ++ tailWord_5154121) baseStart_5154121 baseEnd_5154121 := by
    simpa [prefixWord, tailWord_5154121, baseEnd_5154121] using wordTrace_append hprefix tailTrace_5154121
  have hstable : (prefixWord ++ tailWord_5154121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154121).length < 2 ^ (prefixWord ++ tailWord_5154121).sum := by decide
  have hdescent : baseEnd_5154121 < baseStart_5154121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154128 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 1, 1, 3]
def baseStart_5154128 : Nat := 118140960795 + 5154128 * 2 ^ 59
def prefixEnd_5154128 : Nat := 4983230072969 + 3 ^ 40 * 5154128 * 2
def baseEnd_5154128 : Nat := 2646545018796715684196603

theorem tailTrace_5154128 : CollatzResearch.WordTrace tailWord_5154128 prefixEnd_5154128 2646545018796715684196603 := by
  unfold tailWord_5154128
  simp only [CollatzResearch.WordTrace]
  refine ⟨93993245935740992913415519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125324327914321323884554025 93993245935740992913415519)
  ·
    refine ⟨140989868903611489370123279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93993245935740992913415519 140989868903611489370123279)
    ·
      refine ⟨211484803355417234055184919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140989868903611489370123279 211484803355417234055184919)
      ·
        refine ⟨317227205033125851082777379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211484803355417234055184919 317227205033125851082777379)
        ·
          refine ⟨475840807549688776624166069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317227205033125851082777379 475840807549688776624166069)
          ·
            refine ⟨44610075707783322808515569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 475840807549688776624166069 44610075707783322808515569)
            ·
              refine ⟨33457556780837492106386677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44610075707783322808515569 33457556780837492106386677)
              ·
                refine ⟨3136645948203514884973751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33457556780837492106386677 3136645948203514884973751)
                ·
                  refine ⟨4704968922305272327460627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136645948203514884973751 4704968922305272327460627)
                  ·
                    refine ⟨7057453383457908491190941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704968922305272327460627 7057453383457908491190941)
                    ·
                      refine ⟨2646545018796715684196603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7057453383457908491190941 2646545018796715684196603)
                      ·
                        rfl

theorem cell23_5154128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 1, 3].length) (baseStart_5154128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154128 prefixEnd_5154128 := by exact prefixLift 5154128
  have htrace : WordTrace (prefixWord ++ tailWord_5154128) baseStart_5154128 baseEnd_5154128 := by
    simpa [prefixWord, tailWord_5154128, baseEnd_5154128] using wordTrace_append hprefix tailTrace_5154128
  have hstable : (prefixWord ++ tailWord_5154128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154128).length < 2 ^ (prefixWord ++ tailWord_5154128).sum := by decide
  have hdescent : baseEnd_5154128 < baseStart_5154128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154131 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 1, 5]
def baseStart_5154131 : Nat := 118140960795 + 5154131 * 2 ^ 59
def prefixEnd_5154131 : Nat := 4983230072969 + 3 ^ 40 * 5154131 * 2
def baseEnd_5154131 : Nat := 882182186412893057486363

theorem tailTrace_5154131 : CollatzResearch.WordTrace tailWord_5154131 prefixEnd_5154131 882182186412893057486363 := by
  unfold tailWord_5154131
  simp only [CollatzResearch.WordTrace]
  refine ⟨187986601290471117339190247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125324400860314078226126831 187986601290471117339190247)
  ·
    refine ⟨281979901935706676008785371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187986601290471117339190247 281979901935706676008785371)
    ·
      refine ⟨422969852903560014013178057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281979901935706676008785371 422969852903560014013178057)
      ·
        refine ⟨317227389677670010509883543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422969852903560014013178057 317227389677670010509883543)
        ·
          refine ⟨475841084516505015764825315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317227389677670010509883543 475841084516505015764825315)
          ·
            refine ⟨713761626774757523647237973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475841084516505015764825315 713761626774757523647237973)
            ·
              refine ⟨4182197031883344865120535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 713761626774757523647237973 4182197031883344865120535)
              ·
                refine ⟨6273295547825017297680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182197031883344865120535 6273295547825017297680803)
                ·
                  refine ⟨9409943321737525946521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273295547825017297680803 9409943321737525946521205)
                  ·
                    refine ⟨882182186412893057486363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9409943321737525946521205 882182186412893057486363)
                    ·
                      rfl

theorem cell23_5154131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 5].length) (baseStart_5154131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154131 prefixEnd_5154131 := by exact prefixLift 5154131
  have htrace : WordTrace (prefixWord ++ tailWord_5154131) baseStart_5154131 baseEnd_5154131 := by
    simpa [prefixWord, tailWord_5154131, baseEnd_5154131] using wordTrace_append hprefix tailTrace_5154131
  have hstable : (prefixWord ++ tailWord_5154131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154131).length < 2 ^ (prefixWord ++ tailWord_5154131).sum := by decide
  have hdescent : baseEnd_5154131 < baseStart_5154131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154161 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_5154161 : Nat := 118140960795 + 5154161 * 2 ^ 59
def prefixEnd_5154161 : Nat := 4983230072969 + 3 ^ 40 * 5154161 * 2
def baseEnd_5154161 : Nat := 882187321219438018361317

theorem tailTrace_5154161 : CollatzResearch.WordTrace tailWord_5154161 prefixEnd_5154161 882187321219438018361317 := by
  unfold tailWord_5154161
  simp only [CollatzResearch.WordTrace]
  refine ⟨187987695480362432462782337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125325130320241621641854891 187987695480362432462782337)
  ·
    refine ⟨140990771610271824347086753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187987695480362432462782337 140990771610271824347086753)
    ·
      refine ⟨105743078707703868260315065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140990771610271824347086753 105743078707703868260315065)
      ·
        refine ⟨79307309030777901195236299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105743078707703868260315065 79307309030777901195236299)
        ·
          refine ⟨118960963546166851792854449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79307309030777901195236299 118960963546166851792854449)
          ·
            refine ⟨89220722659625138844640837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118960963546166851792854449 89220722659625138844640837)
            ·
              refine ⟨16728885498679713533370157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89220722659625138844640837 16728885498679713533370157)
              ·
                refine ⟨6273332062004892575013809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16728885498679713533370157 6273332062004892575013809)
                ·
                  refine ⟨4704999046503669431260357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6273332062004892575013809 4704999046503669431260357)
                  ·
                    refine ⟨882187321219438018361317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704999046503669431260357 882187321219438018361317)
                    ·
                      rfl

theorem cell23_5154161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_5154161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154161 prefixEnd_5154161 := by exact prefixLift 5154161
  have htrace : WordTrace (prefixWord ++ tailWord_5154161) baseStart_5154161 baseEnd_5154161 := by
    simpa [prefixWord, tailWord_5154161, baseEnd_5154161] using wordTrace_append hprefix tailTrace_5154161
  have hstable : (prefixWord ++ tailWord_5154161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154161).length < 2 ^ (prefixWord ++ tailWord_5154161).sum := by decide
  have hdescent : baseEnd_5154161 < baseStart_5154161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154171 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 3]
def baseStart_5154171 : Nat := 118140960795 + 5154171 * 2 ^ 59
def prefixEnd_5154171 : Nat := 4983230072969 + 3 ^ 40 * 5154171 * 2
def baseEnd_5154171 : Nat := 2646567098464859015958905

theorem tailTrace_5154171 : CollatzResearch.WordTrace tailWord_5154171 prefixEnd_5154171 2646567098464859015958905 := by
  unfold tailWord_5154171
  simp only [CollatzResearch.WordTrace]
  refine ⟨187988060210326204170646367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125325373473550802780430911 187988060210326204170646367)
  ·
    refine ⟨281982090315489306255969551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187988060210326204170646367 281982090315489306255969551)
    ·
      refine ⟨422973135473233959383954327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281982090315489306255969551 422973135473233959383954327)
      ·
        refine ⟨634459703209850939075931491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422973135473233959383954327 634459703209850939075931491)
        ·
          refine ⟨951689554814776408613897237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634459703209850939075931491 951689554814776408613897237)
          ·
            refine ⟨44610447881942644153776433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 951689554814776408613897237 44610447881942644153776433)
            ·
              refine ⟨33457835911456983115332325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44610447881942644153776433 33457835911456983115332325)
              ·
                refine ⟨6273344233398184334124811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33457835911456983115332325 6273344233398184334124811)
                ·
                  refine ⟨9410016350097276501187217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273344233398184334124811 9410016350097276501187217)
                  ·
                    refine ⟨7057512262572957375890413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9410016350097276501187217 7057512262572957375890413)
                    ·
                      refine ⟨2646567098464859015958905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7057512262572957375890413 2646567098464859015958905)
                      ·
                        rfl

theorem cell23_5154171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 3].length) (baseStart_5154171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154171 prefixEnd_5154171 := by exact prefixLift 5154171
  have htrace : WordTrace (prefixWord ++ tailWord_5154171) baseStart_5154171 baseEnd_5154171 := by
    simpa [prefixWord, tailWord_5154171, baseEnd_5154171] using wordTrace_append hprefix tailTrace_5154171
  have hstable : (prefixWord ++ tailWord_5154171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154171).length < 2 ^ (prefixWord ++ tailWord_5154171).sum := by decide
  have hdescent : baseEnd_5154171 < baseStart_5154171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154178 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5154178 : Nat := 118140960795 + 5154178 * 2 ^ 59
def prefixEnd_5154178 : Nat := 4983230072969 + 3 ^ 40 * 5154178 * 2
def baseEnd_5154178 : Nat := 882190230943146829523791

theorem tailTrace_5154178 : CollatzResearch.WordTrace tailWord_5154178 prefixEnd_5154178 882190230943146829523791 := by
  unfold tailWord_5154178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46997078880325211091537797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125325543680867229577434125 46997078880325211091537797)
  ·
    refine ⟨8811952290060977079663337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46997078880325211091537797 8811952290060977079663337)
    ·
      refine ⟨6608964217545732809747503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811952290060977079663337 6608964217545732809747503)
      ·
        refine ⟨9913446326318599214621255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608964217545732809747503 9913446326318599214621255)
        ·
          refine ⟨14870169489477898821931883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9913446326318599214621255 14870169489477898821931883)
          ·
            refine ⟨22305254234216848232897825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14870169489477898821931883 22305254234216848232897825)
            ·
              refine ⟨16728940675662636174673369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22305254234216848232897825 16728940675662636174673369)
              ·
                refine ⟨12546705506746977131005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16728940675662636174673369 12546705506746977131005027)
                ·
                  refine ⟨18820058260120465696507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12546705506746977131005027 18820058260120465696507541)
                  ·
                    refine ⟨882190230943146829523791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18820058260120465696507541 882190230943146829523791)
                    ·
                      rfl

theorem cell23_5154178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5154178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154178 prefixEnd_5154178 := by exact prefixLift 5154178
  have htrace : WordTrace (prefixWord ++ tailWord_5154178) baseStart_5154178 baseEnd_5154178 := by
    simpa [prefixWord, tailWord_5154178, baseEnd_5154178] using wordTrace_append hprefix tailTrace_5154178
  have hstable : (prefixWord ++ tailWord_5154178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154178).length < 2 ^ (prefixWord ++ tailWord_5154178).sum := by decide
  have hdescent : baseEnd_5154178 < baseStart_5154178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154185 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 1, 1, 4]
def baseStart_5154185 : Nat := 118140960795 + 5154185 * 2 ^ 59
def prefixEnd_5154185 : Nat := 4983230072969 + 3 ^ 40 * 5154185 * 2
def baseEnd_5154185 : Nat := 2646574287194021961183841

theorem tailTrace_5154185 : CollatzResearch.WordTrace tailWord_5154185 prefixEnd_5154185 2646574287194021961183841 := by
  unfold tailWord_5154185
  simp only [CollatzResearch.WordTrace]
  refine ⟨187988570832275484561656009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125325713888183656374437339 187988570832275484561656009)
  ·
    refine ⟨140991428124206613421242007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187988570832275484561656009 140991428124206613421242007)
    ·
      refine ⟨211487142186309920131863011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140991428124206613421242007 211487142186309920131863011)
      ·
        refine ⟨317230713279464880197794517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211487142186309920131863011 317230713279464880197794517)
        ·
          refine ⟨7435094842487458129635809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 317230713279464880197794517 7435094842487458129635809)
          ·
            refine ⟨5576321131865593597226857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7435094842487458129635809 5576321131865593597226857)
            ·
              refine ⟨4182240848899195197920143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576321131865593597226857 4182240848899195197920143)
              ·
                refine ⟨6273361273348792796880215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182240848899195197920143 6273361273348792796880215)
                ·
                  refine ⟨9410041910023189195320323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273361273348792796880215 9410041910023189195320323)
                  ·
                    refine ⟨14115062865034783792980485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9410041910023189195320323 14115062865034783792980485)
                    ·
                      refine ⟨2646574287194021961183841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14115062865034783792980485 2646574287194021961183841)
                      ·
                        rfl

theorem cell23_5154185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 1, 4].length) (baseStart_5154185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154185 prefixEnd_5154185 := by exact prefixLift 5154185
  have htrace : WordTrace (prefixWord ++ tailWord_5154185) baseStart_5154185 baseEnd_5154185 := by
    simpa [prefixWord, tailWord_5154185, baseEnd_5154185] using wordTrace_append hprefix tailTrace_5154185
  have hstable : (prefixWord ++ tailWord_5154185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154185).length < 2 ^ (prefixWord ++ tailWord_5154185).sum := by decide
  have hdescent : baseEnd_5154185 < baseStart_5154185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154236 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5154236 : Nat := 118140960795 + 5154236 * 2 ^ 59
def prefixEnd_5154236 : Nat := 4983230072969 + 3 ^ 40 * 5154236 * 2
def baseEnd_5154236 : Nat := 2646600474707401261646107

theorem tailTrace_5154236 : CollatzResearch.WordTrace tailWord_5154236 prefixEnd_5154236 2646600474707401261646107 := by
  unfold tailWord_5154236
  simp only [CollatzResearch.WordTrace]
  refine ⟨93995215477545360135881281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125326953970060480181175041 93995215477545360135881281)
  ·
    refine ⟨70496411608159020101910961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93995215477545360135881281 70496411608159020101910961)
    ·
      refine ⟨52872308706119265076433221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70496411608159020101910961 52872308706119265076433221)
      ·
        refine ⟨9913557882397362201831229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52872308706119265076433221 9913557882397362201831229)
        ·
          refine ⟨3717584205899010825686711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9913557882397362201831229 3717584205899010825686711)
          ·
            refine ⟨5576376308848516238530067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717584205899010825686711 5576376308848516238530067)
            ·
              refine ⟨8364564463272774357795101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576376308848516238530067 8364564463272774357795101)
              ·
                refine ⟨3136711673727290384173163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8364564463272774357795101 3136711673727290384173163)
                ·
                  refine ⟨4705067510590935576259745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136711673727290384173163 4705067510590935576259745)
                  ·
                    refine ⟨3528800632943201682194809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4705067510590935576259745 3528800632943201682194809)
                    ·
                      refine ⟨2646600474707401261646107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528800632943201682194809 2646600474707401261646107)
                      ·
                        rfl

theorem cell23_5154236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5154236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154236 prefixEnd_5154236 := by exact prefixLift 5154236
  have htrace : WordTrace (prefixWord ++ tailWord_5154236) baseStart_5154236 baseEnd_5154236 := by
    simpa [prefixWord, tailWord_5154236, baseEnd_5154236] using wordTrace_append hprefix tailTrace_5154236
  have hstable : (prefixWord ++ tailWord_5154236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154236).length < 2 ^ (prefixWord ++ tailWord_5154236).sum := by decide
  have hdescent : baseEnd_5154236 < baseStart_5154236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154242 : List Nat := [3, 5, 2, 1, 1, 2, 9]
def baseStart_5154242 : Nat := 118140960795 + 5154242 * 2 ^ 59
def prefixEnd_5154242 : Nat := 4983230072969 + 3 ^ 40 * 5154242 * 2
def baseEnd_5154242 : Nat := 32674117970263311582359

theorem tailTrace_5154242 : CollatzResearch.WordTrace tailWord_5154242 prefixEnd_5154242 32674117970263311582359 := by
  unfold tailWord_5154242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46997662448267245824120245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125327099862045988864320653 46997662448267245824120245)
  ·
    refine ⟨4406030854525054296011273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46997662448267245824120245 4406030854525054296011273)
    ·
      refine ⟨3304523140893790722008455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4406030854525054296011273 3304523140893790722008455)
      ·
        refine ⟨4956784711340686083012683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304523140893790722008455 4956784711340686083012683)
        ·
          refine ⟨7435177067011029124519025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956784711340686083012683 7435177067011029124519025)
          ·
            refine ⟨5576382800258271843389269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7435177067011029124519025 5576382800258271843389269)
            ·
              refine ⟨32674117970263311582359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5576382800258271843389269 32674117970263311582359)
              ·
                rfl

theorem cell23_5154242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 9].length) (baseStart_5154242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154242 prefixEnd_5154242 := by exact prefixLift 5154242
  have htrace : WordTrace (prefixWord ++ tailWord_5154242) baseStart_5154242 baseEnd_5154242 := by
    simpa [prefixWord, tailWord_5154242, baseEnd_5154242] using wordTrace_append hprefix tailTrace_5154242
  have hstable : (prefixWord ++ tailWord_5154242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154242).length < 2 ^ (prefixWord ++ tailWord_5154242).sum := by decide
  have hdescent : baseEnd_5154242 < baseStart_5154242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154261 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5154261 : Nat := 118140960795 + 5154261 * 2 ^ 59
def prefixEnd_5154261 : Nat := 4983230072969 + 3 ^ 40 * 5154261 * 2
def baseEnd_5154261 : Nat := 2646613311723763663833491

theorem tailTrace_5154261 : CollatzResearch.WordTrace tailWord_5154261 prefixEnd_5154261 2646613311723763663833491 := by
  unfold tailWord_5154261
  simp only [CollatzResearch.WordTrace]
  refine ⟨187991342780000149541422637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125327561853333433027615091 187991342780000149541422637)
  ·
    refine ⟨70496753542500056078033489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187991342780000149541422637 70496753542500056078033489)
    ·
      refine ⟨52872565156875042058525117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70496753542500056078033489 52872565156875042058525117)
      ·
        refine ⟨19827211933828140771946919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52872565156875042058525117 19827211933828140771946919)
        ·
          refine ⟨29740817900742211157920379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827211933828140771946919 29740817900742211157920379)
          ·
            refine ⟨44611226851113316736880569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29740817900742211157920379 44611226851113316736880569)
            ·
              refine ⟨33458420138334987552660427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44611226851113316736880569 33458420138334987552660427)
              ·
                refine ⟨50187630207502481328990641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33458420138334987552660427 50187630207502481328990641)
                ·
                  refine ⟨37640722655626860996742981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50187630207502481328990641 37640722655626860996742981)
                  ·
                    refine ⟨7057635497930036436889309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37640722655626860996742981 7057635497930036436889309)
                    ·
                      refine ⟨2646613311723763663833491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7057635497930036436889309 2646613311723763663833491)
                      ·
                        rfl

theorem cell23_5154261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5154261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154261 prefixEnd_5154261 := by exact prefixLift 5154261
  have htrace : WordTrace (prefixWord ++ tailWord_5154261) baseStart_5154261 baseEnd_5154261 := by
    simpa [prefixWord, tailWord_5154261, baseEnd_5154261] using wordTrace_append hprefix tailTrace_5154261
  have hstable : (prefixWord ++ tailWord_5154261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154261).length < 2 ^ (prefixWord ++ tailWord_5154261).sum := by decide
  have hdescent : baseEnd_5154261 < baseStart_5154261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154361 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5154361 : Nat := 118140960795 + 5154361 * 2 ^ 59
def prefixEnd_5154361 : Nat := 4983230072969 + 3 ^ 40 * 5154361 * 2
def baseEnd_5154361 : Nat := 2646664659789213272583031

theorem tailTrace_5154361 : CollatzResearch.WordTrace tailWord_5154361 prefixEnd_5154361 2646664659789213272583031 := by
  unfold tailWord_5154361
  simp only [CollatzResearch.WordTrace]
  refine ⟨187994990079637866620062937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125329993386425244413375291 187994990079637866620062937)
  ·
    refine ⟨140996242559728399965047203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187994990079637866620062937 140996242559728399965047203)
    ·
      refine ⟨211494363839592599947570805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140996242559728399965047203 211494363839592599947570805)
      ·
        refine ⟨19827596609961806245084763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211494363839592599947570805 19827596609961806245084763)
        ·
          refine ⟨29741394914942709367627145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827596609961806245084763 29741394914942709367627145)
          ·
            refine ⟨22306046186207032025720359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29741394914942709367627145 22306046186207032025720359)
            ·
              refine ⟨33459069279310548038580539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22306046186207032025720359 33459069279310548038580539)
              ·
                refine ⟨50188603918965822057870809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33459069279310548038580539 50188603918965822057870809)
                ·
                  refine ⟨37641452939224366543403107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50188603918965822057870809 37641452939224366543403107)
                  ·
                    refine ⟨56462179408836549815104661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37641452939224366543403107 56462179408836549815104661)
                    ·
                      refine ⟨2646664659789213272583031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56462179408836549815104661 2646664659789213272583031)
                      ·
                        rfl

theorem cell23_5154361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5154361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154361 prefixEnd_5154361 := by exact prefixLift 5154361
  have htrace : WordTrace (prefixWord ++ tailWord_5154361) baseStart_5154361 baseEnd_5154361 := by
    simpa [prefixWord, tailWord_5154361, baseEnd_5154361] using wordTrace_append hprefix tailTrace_5154361
  have hstable : (prefixWord ++ tailWord_5154361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154361).length < 2 ^ (prefixWord ++ tailWord_5154361).sum := by decide
  have hdescent : baseEnd_5154361 < baseStart_5154361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154375 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 3, 4]
def baseStart_5154375 : Nat := 118140960795 + 5154375 * 2 ^ 59
def prefixEnd_5154375 : Nat := 4983230072969 + 3 ^ 40 * 5154375 * 2
def baseEnd_5154375 : Nat := 882223949506125405935989

theorem tailTrace_5154375 : CollatzResearch.WordTrace tailWord_5154375 prefixEnd_5154375 882223949506125405935989 := by
  unfold tailWord_5154375
  simp only [CollatzResearch.WordTrace]
  refine ⟨187995500701587147011072579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125330333801058098007381719 187995500701587147011072579)
  ·
    refine ⟨281993251052380720516608869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187995500701587147011072579 281993251052380720516608869)
    ·
      refine ⟨52873734572321385096864163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281993251052380720516608869 52873734572321385096864163)
      ·
        refine ⟨79310601858482077645296245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52873734572321385096864163 79310601858482077645296245)
        ·
          refine ⟨7435368924232694779246523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79310601858482077645296245 7435368924232694779246523)
          ·
            refine ⟨11153053386349042168869785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435368924232694779246523 11153053386349042168869785)
            ·
              refine ⟨8364790039761781626652339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11153053386349042168869785 8364790039761781626652339)
              ·
                refine ⟨12547185059642672439978509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364790039761781626652339 12547185059642672439978509)
                ·
                  refine ⟨4705194397366002164991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12547185059642672439978509 4705194397366002164991941)
                  ·
                    refine ⟨882223949506125405935989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705194397366002164991941 882223949506125405935989)
                    ·
                      rfl

theorem cell23_5154375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_5154375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154375 prefixEnd_5154375 := by exact prefixLift 5154375
  have htrace : WordTrace (prefixWord ++ tailWord_5154375) baseStart_5154375 baseEnd_5154375 := by
    simpa [prefixWord, tailWord_5154375, baseEnd_5154375] using wordTrace_append hprefix tailTrace_5154375
  have hstable : (prefixWord ++ tailWord_5154375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154375).length < 2 ^ (prefixWord ++ tailWord_5154375).sum := by decide
  have hdescent : baseEnd_5154375 < baseStart_5154375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154425 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 2, 3, 2]
def baseStart_5154425 : Nat := 118140960795 + 5154425 * 2 ^ 59
def prefixEnd_5154425 : Nat := 4983230072969 + 3 ^ 40 * 5154425 * 2
def baseEnd_5154425 : Nat := 2646697522551101022182737

theorem tailTrace_5154425 : CollatzResearch.WordTrace tailWord_5154425 prefixEnd_5154425 2646697522551101022182737 := by
  unfold tailWord_5154425
  simp only [CollatzResearch.WordTrace]
  refine ⟨187997324351406005550392729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125331549567604003700261819 187997324351406005550392729)
  ·
    refine ⟨140997993263554504162794547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187997324351406005550392729 140997993263554504162794547)
    ·
      refine ⟨211496989895331756244191821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140997993263554504162794547 211496989895331756244191821)
      ·
        refine ⟨79311371210749408591571933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211496989895331756244191821 79311371210749408591571933)
        ·
          refine ⟨29741764204031028221839475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79311371210749408591571933 29741764204031028221839475)
          ·
            refine ⟨44612646306046542332759213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29741764204031028221839475 44612646306046542332759213)
            ·
              refine ⟨16729742364767453374784705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44612646306046542332759213 16729742364767453374784705)
              ·
                refine ⟨12547306773575590031088529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16729742364767453374784705 12547306773575590031088529)
                ·
                  refine ⟨9410480080181692523316397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12547306773575590031088529 9410480080181692523316397)
                  ·
                    refine ⟨3528930030068134696243649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9410480080181692523316397 3528930030068134696243649)
                    ·
                      refine ⟨2646697522551101022182737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3528930030068134696243649 2646697522551101022182737)
                      ·
                        rfl

theorem cell23_5154425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_5154425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154425 prefixEnd_5154425 := by exact prefixLift 5154425
  have htrace : WordTrace (prefixWord ++ tailWord_5154425) baseStart_5154425 baseEnd_5154425 := by
    simpa [prefixWord, tailWord_5154425, baseEnd_5154425] using wordTrace_append hprefix tailTrace_5154425
  have hstable : (prefixWord ++ tailWord_5154425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154425).length < 2 ^ (prefixWord ++ tailWord_5154425).sum := by decide
  have hdescent : baseEnd_5154425 < baseStart_5154425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154455 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_5154455 : Nat := 118140960795 + 5154455 * 2 ^ 59
def prefixEnd_5154455 : Nat := 4983230072969 + 3 ^ 40 * 5154455 * 2
def baseEnd_5154455 : Nat := 2646712926970735904807599

theorem tailTrace_5154455 : CollatzResearch.WordTrace tailWord_5154455 prefixEnd_5154455 2646712926970735904807599 := by
  unfold tailWord_5154455
  simp only [CollatzResearch.WordTrace]
  refine ⟨187998418541297320673984819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125332279027531547115989879 187998418541297320673984819)
  ·
    refine ⟨281997627811945981010977229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187998418541297320673984819 281997627811945981010977229)
    ·
      refine ⟨105749110429479742879116461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281997627811945981010977229 105749110429479742879116461)
      ·
        refine ⟨39655916411054903579668673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105749110429479742879116461 39655916411054903579668673)
        ·
          refine ⟨29741937308291177684751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39655916411054903579668673 29741937308291177684751505)
          ·
            refine ⟨22306452981218383263563629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29741937308291177684751505 22306452981218383263563629)
            ·
              refine ⟨8364919867956893723836361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22306452981218383263563629 8364919867956893723836361)
              ·
                refine ⟨6273689900967670292877271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8364919867956893723836361 6273689900967670292877271)
                ·
                  refine ⟨9410534851451505439315907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273689900967670292877271 9410534851451505439315907)
                  ·
                    refine ⟨14115802277177258158973861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9410534851451505439315907 14115802277177258158973861)
                    ·
                      refine ⟨2646712926970735904807599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14115802277177258158973861 2646712926970735904807599)
                      ·
                        rfl

theorem cell23_5154455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_5154455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154455 prefixEnd_5154455 := by exact prefixLift 5154455
  have htrace : WordTrace (prefixWord ++ tailWord_5154455) baseStart_5154455 baseEnd_5154455 := by
    simpa [prefixWord, tailWord_5154455, baseEnd_5154455] using wordTrace_append hprefix tailTrace_5154455
  have hstable : (prefixWord ++ tailWord_5154455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154455).length < 2 ^ (prefixWord ++ tailWord_5154455).sum := by decide
  have hdescent : baseEnd_5154455 < baseStart_5154455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5154468 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_5154468 : Nat := 118140960795 + 5154468 * 2 ^ 59
def prefixEnd_5154468 : Nat := 4983230072969 + 3 ^ 40 * 5154468 * 2
def baseEnd_5154468 : Nat := 2646719602219244353945039

theorem tailTrace_5154468 : CollatzResearch.WordTrace tailWord_5154468 prefixEnd_5154468 2646719602219244353945039 := by
  unfold tailWord_5154468
  simp only [CollatzResearch.WordTrace]
  refine ⟨93999446345125111947104029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125332595126833482596138705 93999446345125111947104029)
  ·
    refine ⟨35249792379421916980164011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93999446345125111947104029 35249792379421916980164011)
    ·
      refine ⟨52874688569132875470246017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35249792379421916980164011 52874688569132875470246017)
      ·
        refine ⟨39656016426849656602684513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52874688569132875470246017 39656016426849656602684513)
        ·
          refine ⟨29742012320137242452013385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39656016426849656602684513 29742012320137242452013385)
          ·
            refine ⟨22306509240102931839010039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29742012320137242452013385 22306509240102931839010039)
            ·
              refine ⟨33459763860154397758515059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22306509240102931839010039 33459763860154397758515059)
              ·
                refine ⟨50189645790231596637772589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33459763860154397758515059 50189645790231596637772589)
                ·
                  refine ⟨18821117171336848739164721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50189645790231596637772589 18821117171336848739164721)
                  ·
                    refine ⟨14115837878502636554373541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18821117171336848739164721 14115837878502636554373541)
                    ·
                      refine ⟨2646719602219244353945039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14115837878502636554373541 2646719602219244353945039)
                      ·
                        rfl

theorem cell23_5154468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_5154468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5154468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5154468 prefixEnd_5154468 := by exact prefixLift 5154468
  have htrace : WordTrace (prefixWord ++ tailWord_5154468) baseStart_5154468 baseEnd_5154468 := by
    simpa [prefixWord, tailWord_5154468, baseEnd_5154468] using wordTrace_append hprefix tailTrace_5154468
  have hstable : (prefixWord ++ tailWord_5154468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5154468).length < 2 ^ (prefixWord ++ tailWord_5154468).sum := by decide
  have hdescent : baseEnd_5154468 < baseStart_5154468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5154468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
