import V185TrunkScan23Chunk1219

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7229008 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_7229008 : Nat := 118140960795 + 7229008 * 2 ^ 59
def prefixEnd_7229008 : Nat := 4983230072969 + 3 ^ 40 * 7229008 * 2
def baseEnd_7229008 : Nat := 3711955759197557706654403

theorem tailTrace_7229008 : CollatzResearch.WordTrace tailWord_7229008 prefixEnd_7229008 3711955759197557706654403 := by
  unfold tailWord_7229008
  simp only [CollatzResearch.WordTrace]
  refine ⟨131831791297273053559343839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175775721729697404745791785 131831791297273053559343839)
  ·
    refine ⟨197747686945909580339015759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131831791297273053559343839 197747686945909580339015759)
    ·
      refine ⟨296621530418864370508523639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197747686945909580339015759 296621530418864370508523639)
      ·
        refine ⟨444932295628296555762785459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296621530418864370508523639 444932295628296555762785459)
        ·
          refine ⟨667398443442444833644178189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444932295628296555762785459 667398443442444833644178189)
          ·
            refine ⟨250274416290916812616566821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667398443442444833644178189 250274416290916812616566821)
            ·
              refine ⟨46926453054546902365606279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250274416290916812616566821 46926453054546902365606279)
              ·
                refine ⟨70389679581820353548409419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46926453054546902365606279 70389679581820353548409419)
                ·
                  refine ⟨105584519372730530322614129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70389679581820353548409419 105584519372730530322614129)
                  ·
                    refine ⟨79188389529547897741960597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105584519372730530322614129 79188389529547897741960597)
                    ·
                      refine ⟨3711955759197557706654403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79188389529547897741960597 3711955759197557706654403)
                      ·
                        rfl

theorem cell23_7229008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_7229008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229008 prefixEnd_7229008 := by exact prefixLift 7229008
  have htrace : WordTrace (prefixWord ++ tailWord_7229008) baseStart_7229008 baseEnd_7229008 := by
    simpa [prefixWord, tailWord_7229008, baseEnd_7229008] using wordTrace_append hprefix tailTrace_7229008
  have hstable : (prefixWord ++ tailWord_7229008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229008).length < 2 ^ (prefixWord ++ tailWord_7229008).sum := by decide
  have hdescent : baseEnd_7229008 < baseStart_7229008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229066 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7229066 : Nat := 118140960795 + 7229066 * 2 ^ 59
def prefixEnd_7229066 : Nat := 4983230072969 + 3 ^ 40 * 7229066 * 2
def baseEnd_7229066 : Nat := 3711985541075518479729137

theorem tailTrace_7229066 : CollatzResearch.WordTrace tailWord_7229066 prefixEnd_7229066 3711985541075518479729137 := by
  unfold tailWord_7229066
  simp only [CollatzResearch.WordTrace]
  refine ⟨65916424507083995756074763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175777132018890655349532701 65916424507083995756074763)
  ·
    refine ⟨98874636760625993634112145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65916424507083995756074763 98874636760625993634112145)
    ·
      refine ⟨74155977570469495225584109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98874636760625993634112145 74155977570469495225584109)
      ·
        refine ⟨27808491588926060709594041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74155977570469495225584109 27808491588926060709594041)
        ·
          refine ⟨20856368691694545532195531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27808491588926060709594041 20856368691694545532195531)
          ·
            refine ⟨31284553037541818298293297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856368691694545532195531 31284553037541818298293297)
            ·
              refine ⟨23463414778156363723719973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31284553037541818298293297 23463414778156363723719973)
              ·
                refine ⟨4399390270904318198197495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23463414778156363723719973 4399390270904318198197495)
                ·
                  refine ⟨6599085406356477297296243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399390270904318198197495 6599085406356477297296243)
                  ·
                    refine ⟨9898628109534715945944365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6599085406356477297296243 9898628109534715945944365)
                    ·
                      refine ⟨3711985541075518479729137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898628109534715945944365 3711985541075518479729137)
                      ·
                        rfl

theorem cell23_7229066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7229066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229066 prefixEnd_7229066 := by exact prefixLift 7229066
  have htrace : WordTrace (prefixWord ++ tailWord_7229066) baseStart_7229066 baseEnd_7229066 := by
    simpa [prefixWord, tailWord_7229066, baseEnd_7229066] using wordTrace_append hprefix tailTrace_7229066
  have hstable : (prefixWord ++ tailWord_7229066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229066).length < 2 ^ (prefixWord ++ tailWord_7229066).sum := by decide
  have hdescent : baseEnd_7229066 < baseStart_7229066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229089 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7229089 : Nat := 118140960795 + 7229089 * 2 ^ 59
def prefixEnd_7229089 : Nat := 4983230072969 + 3 ^ 40 * 7229089 * 2
def baseEnd_7229089 : Nat := 3711997351130571889741531

theorem tailTrace_7229089 : CollatzResearch.WordTrace tailWord_7229089 prefixEnd_7229089 3711997351130571889741531 := by
  unfold tailWord_7229089
  simp only [CollatzResearch.WordTrace]
  refine ⟨263666536907252657952386321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175777691271501771968257547 263666536907252657952386321)
  ·
    refine ⟨197749902680439493464289741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263666536907252657952386321 197749902680439493464289741)
    ·
      refine ⟨74156213505164810049108653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197749902680439493464289741 74156213505164810049108653)
      ·
        refine ⟨27808580064436803768415745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74156213505164810049108653 27808580064436803768415745)
        ·
          refine ⟨20856435048327602826311809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27808580064436803768415745 20856435048327602826311809)
          ·
            refine ⟨15642326286245702119733857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20856435048327602826311809 15642326286245702119733857)
            ·
              refine ⟨11731744714684276589800393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15642326286245702119733857 11731744714684276589800393)
              ·
                refine ⟨8798808536013207442350295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11731744714684276589800393 8798808536013207442350295)
                ·
                  refine ⟨13198212804019811163525443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798808536013207442350295 13198212804019811163525443)
                  ·
                    refine ⟨19797319206029716745288165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13198212804019811163525443 19797319206029716745288165)
                    ·
                      refine ⟨3711997351130571889741531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19797319206029716745288165 3711997351130571889741531)
                      ·
                        rfl

theorem cell23_7229089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7229089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229089 prefixEnd_7229089 := by exact prefixLift 7229089
  have htrace : WordTrace (prefixWord ++ tailWord_7229089) baseStart_7229089 baseEnd_7229089 := by
    simpa [prefixWord, tailWord_7229089, baseEnd_7229089] using wordTrace_append hprefix tailTrace_7229089
  have hstable : (prefixWord ++ tailWord_7229089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229089).length < 2 ^ (prefixWord ++ tailWord_7229089).sum := by decide
  have hdescent : baseEnd_7229089 < baseStart_7229089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229109 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7229109 : Nat := 118140960795 + 7229109 * 2 ^ 59
def prefixEnd_7229109 : Nat := 4983230072969 + 3 ^ 40 * 7229109 * 2
def baseEnd_7229109 : Nat := 3712007620743661811491439

theorem tailTrace_7229109 : CollatzResearch.WordTrace tailWord_7229109 prefixEnd_7229109 3712007620743661811491439 := by
  unfold tailWord_7229109
  simp only [CollatzResearch.WordTrace]
  refine ⟨263667266367180201368114381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175778177578120134245409587 263667266367180201368114381)
  ·
    refine ⟨98875224887692575513042893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263667266367180201368114381 98875224887692575513042893)
    ·
      refine ⟨37078209332884715817391085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98875224887692575513042893 37078209332884715817391085)
      ·
        refine ⟨13904328499831768431521657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37078209332884715817391085 13904328499831768431521657)
        ·
          refine ⟨10428246374873826323641243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13904328499831768431521657 10428246374873826323641243)
          ·
            refine ⟨15642369562310739485461865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428246374873826323641243 15642369562310739485461865)
            ·
              refine ⟨11731777171733054614096399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15642369562310739485461865 11731777171733054614096399)
              ·
                refine ⟨17597665757599581921144599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731777171733054614096399 17597665757599581921144599)
                ·
                  refine ⟨26396498636399372881716899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17597665757599581921144599 26396498636399372881716899)
                  ·
                    refine ⟨39594747954599059322575349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26396498636399372881716899 39594747954599059322575349)
                    ·
                      refine ⟨3712007620743661811491439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39594747954599059322575349 3712007620743661811491439)
                      ·
                        rfl

theorem cell23_7229109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7229109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229109 prefixEnd_7229109 := by exact prefixLift 7229109
  have htrace : WordTrace (prefixWord ++ tailWord_7229109) baseStart_7229109 baseEnd_7229109 := by
    simpa [prefixWord, tailWord_7229109, baseEnd_7229109] using wordTrace_append hprefix tailTrace_7229109
  have hstable : (prefixWord ++ tailWord_7229109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229109).length < 2 ^ (prefixWord ++ tailWord_7229109).sum := by decide
  have hdescent : baseEnd_7229109 < baseStart_7229109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229126 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7229126 : Nat := 118140960795 + 7229126 * 2 ^ 59
def prefixEnd_7229126 : Nat := 4983230072969 + 3 ^ 40 * 7229126 * 2
def baseEnd_7229126 : Nat := 3712016349914788244978861

theorem tailTrace_7229126 : CollatzResearch.WordTrace tailWord_7229126 prefixEnd_7229126 3712016349914788244978861 := by
  unfold tailWord_7229126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239621450253706664733851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175778590938745742180988821 8239621450253706664733851)
  ·
    refine ⟨12359432175380559997100777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239621450253706664733851 12359432175380559997100777)
    ·
      refine ⟨9269574131535419997825583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12359432175380559997100777 9269574131535419997825583)
      ·
        refine ⟨13904361197303129996738375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269574131535419997825583 13904361197303129996738375)
        ·
          refine ⟨20856541795954694995107563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13904361197303129996738375 20856541795954694995107563)
          ·
            refine ⟨31284812693932042492661345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856541795954694995107563 31284812693932042492661345)
            ·
              refine ⟨23463609520449031869496009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31284812693932042492661345 23463609520449031869496009)
              ·
                refine ⟨17597707140336773902122007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23463609520449031869496009 17597707140336773902122007)
                ·
                  refine ⟨26396560710505160853183011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17597707140336773902122007 26396560710505160853183011)
                  ·
                    refine ⟨39594841065757741279774517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26396560710505160853183011 39594841065757741279774517)
                    ·
                      refine ⟨3712016349914788244978861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39594841065757741279774517 3712016349914788244978861)
                      ·
                        rfl

theorem cell23_7229126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7229126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229126 prefixEnd_7229126 := by exact prefixLift 7229126
  have htrace : WordTrace (prefixWord ++ tailWord_7229126) baseStart_7229126 baseEnd_7229126 := by
    simpa [prefixWord, tailWord_7229126, baseEnd_7229126] using wordTrace_append hprefix tailTrace_7229126
  have hstable : (prefixWord ++ tailWord_7229126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229126).length < 2 ^ (prefixWord ++ tailWord_7229126).sum := by decide
  have hdescent : baseEnd_7229126 < baseStart_7229126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229133 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7229133 : Nat := 118140960795 + 7229133 * 2 ^ 59
def prefixEnd_7229133 : Nat := 4983230072969 + 3 ^ 40 * 7229133 * 2
def baseEnd_7229133 : Nat := 1237339981426456572530443

theorem tailTrace_7229133 : CollatzResearch.WordTrace tailWord_7229133 prefixEnd_7229133 1237339981426456572530443 := by
  unfold tailWord_7229133
  simp only [CollatzResearch.WordTrace]
  refine ⟨263668141719093253466988053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175778761146062168977992035 263668141719093253466988053)
  ·
    refine ⟨12359444143082496256265065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263668141719093253466988053 12359444143082496256265065)
    ·
      refine ⟨9269583107311872192198799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12359444143082496256265065 9269583107311872192198799)
      ·
        refine ⟨13904374660967808288298199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269583107311872192198799 13904374660967808288298199)
        ·
          refine ⟨20856561991451712432447299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13904374660967808288298199 20856561991451712432447299)
          ·
            refine ⟨31284842987177568648670949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856561991451712432447299 31284842987177568648670949)
            ·
              refine ⟨5865908060095794121625803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31284842987177568648670949 5865908060095794121625803)
              ·
                refine ⟨8798862090143691182438705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865908060095794121625803 8798862090143691182438705)
                ·
                  refine ⟨6599146567607768386829029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798862090143691182438705 6599146567607768386829029)
                  ·
                    refine ⟨1237339981426456572530443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599146567607768386829029 1237339981426456572530443)
                    ·
                      rfl

theorem cell23_7229133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7229133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229133 prefixEnd_7229133 := by exact prefixLift 7229133
  have htrace : WordTrace (prefixWord ++ tailWord_7229133) baseStart_7229133 baseEnd_7229133 := by
    simpa [prefixWord, tailWord_7229133, baseEnd_7229133] using wordTrace_append hprefix tailTrace_7229133
  have hstable : (prefixWord ++ tailWord_7229133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229133).length < 2 ^ (prefixWord ++ tailWord_7229133).sum := by decide
  have hdescent : baseEnd_7229133 < baseStart_7229133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229192 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7229192 : Nat := 118140960795 + 7229192 * 2 ^ 59
def prefixEnd_7229192 : Nat := 4983230072969 + 3 ^ 40 * 7229192 * 2
def baseEnd_7229192 : Nat := 3712050239637984986753557

theorem tailTrace_7229192 : CollatzResearch.WordTrace tailWord_7229192 prefixEnd_7229192 3712050239637984986753557 := by
  unfold tailWord_7229192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835146812939753271692915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175780195750586337695590553 131835146812939753271692915)
  ·
    refine ⟨197752720219409629907539373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131835146812939753271692915 197752720219409629907539373)
    ·
      refine ⟨74157270082278611215327265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197752720219409629907539373 74157270082278611215327265)
      ·
        refine ⟨55617952561708958411495449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74157270082278611215327265 55617952561708958411495449)
        ·
          refine ⟨41713464421281718808621587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55617952561708958411495449 41713464421281718808621587)
          ·
            refine ⟨62570196631922578212932381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41713464421281718808621587 62570196631922578212932381)
            ·
              refine ⟨23463823736970966829849643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62570196631922578212932381 23463823736970966829849643)
              ·
                refine ⟨35195735605456450244774465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23463823736970966829849643 35195735605456450244774465)
                ·
                  refine ⟨26396801704092337683580849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35195735605456450244774465 26396801704092337683580849)
                  ·
                    refine ⟨19797601278069253262685637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26396801704092337683580849 19797601278069253262685637)
                    ·
                      refine ⟨3712050239637984986753557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19797601278069253262685637 3712050239637984986753557)
                      ·
                        rfl

theorem cell23_7229192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7229192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229192 prefixEnd_7229192 := by exact prefixLift 7229192
  have htrace : WordTrace (prefixWord ++ tailWord_7229192) baseStart_7229192 baseEnd_7229192 := by
    simpa [prefixWord, tailWord_7229192, baseEnd_7229192] using wordTrace_append hprefix tailTrace_7229192
  have hstable : (prefixWord ++ tailWord_7229192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229192).length < 2 ^ (prefixWord ++ tailWord_7229192).sum := by decide
  have hdescent : baseEnd_7229192 < baseStart_7229192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229196 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_7229196 : Nat := 118140960795 + 7229196 * 2 ^ 59
def prefixEnd_7229196 : Nat := 4983230072969 + 3 ^ 40 * 7229196 * 2
def baseEnd_7229196 : Nat := 3712052293560602971103539

theorem tailTrace_7229196 : CollatzResearch.WordTrace tailWord_7229196 prefixEnd_7229196 3712052293560602971103539 := by
  unfold tailWord_7229196
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835219758932507613265721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175780293011910010151020961 131835219758932507613265721)
  ·
    refine ⟨98876414819199380709949291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131835219758932507613265721 98876414819199380709949291)
    ·
      refine ⟨148314622228799071064923937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98876414819199380709949291 148314622228799071064923937)
      ·
        refine ⟨111235966671599303298692953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148314622228799071064923937 111235966671599303298692953)
        ·
          refine ⟨83426975003699477474019715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111235966671599303298692953 83426975003699477474019715)
          ·
            refine ⟨125140462505549216211029573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83426975003699477474019715 125140462505549216211029573)
            ·
              refine ⟨23463836719790478039568045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125140462505549216211029573 23463836719790478039568045)
              ·
                refine ⟨8798938769921429264838017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23463836719790478039568045 8798938769921429264838017)
                ·
                  refine ⟨6599204077441071948628513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798938769921429264838017 6599204077441071948628513)
                  ·
                    refine ⟨4949403058080803961471385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599204077441071948628513 4949403058080803961471385)
                    ·
                      refine ⟨3712052293560602971103539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949403058080803961471385 3712052293560602971103539)
                      ·
                        rfl

theorem cell23_7229196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_7229196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229196 prefixEnd_7229196 := by exact prefixLift 7229196
  have htrace : WordTrace (prefixWord ++ tailWord_7229196) baseStart_7229196 baseEnd_7229196 := by
    simpa [prefixWord, tailWord_7229196, baseEnd_7229196] using wordTrace_append hprefix tailTrace_7229196
  have hstable : (prefixWord ++ tailWord_7229196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229196).length < 2 ^ (prefixWord ++ tailWord_7229196).sum := by decide
  have hdescent : baseEnd_7229196 < baseStart_7229196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229212 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7229212 : Nat := 118140960795 + 7229212 * 2 ^ 59
def prefixEnd_7229212 : Nat := 4983230072969 + 3 ^ 40 * 7229212 * 2
def baseEnd_7229212 : Nat := 3712060509251074908503465

theorem tailTrace_7229212 : CollatzResearch.WordTrace tailWord_7229212 prefixEnd_7229212 3712060509251074908503465 := by
  unfold tailWord_7229212
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835511542903524979556945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175780682057204699972742593 131835511542903524979556945)
  ·
    refine ⟨98876633657177643734667709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131835511542903524979556945 98876633657177643734667709)
    ·
      refine ⟨37078737621441616400500391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98876633657177643734667709 37078737621441616400500391)
      ·
        refine ⟨55618106432162424600750587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37078737621441616400500391 55618106432162424600750587)
        ·
          refine ⟨83427159648243636901125881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55618106432162424600750587 83427159648243636901125881)
          ·
            refine ⟨62570369736182727675844411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83427159648243636901125881 62570369736182727675844411)
            ·
              refine ⟨93855554604274091513766617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62570369736182727675844411 93855554604274091513766617)
              ·
                refine ⟨70391665953205568635324963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93855554604274091513766617 70391665953205568635324963)
                ·
                  refine ⟨105587498929808352952987445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70391665953205568635324963 105587498929808352952987445)
                  ·
                    refine ⟨9898828024669533089342573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105587498929808352952987445 9898828024669533089342573)
                    ·
                      refine ⟨3712060509251074908503465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898828024669533089342573 3712060509251074908503465)
                      ·
                        rfl

theorem cell23_7229212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7229212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229212 prefixEnd_7229212 := by exact prefixLift 7229212
  have htrace : WordTrace (prefixWord ++ tailWord_7229212) baseStart_7229212 baseEnd_7229212 := by
    simpa [prefixWord, tailWord_7229212, baseEnd_7229212] using wordTrace_append hprefix tailTrace_7229212
  have hstable : (prefixWord ++ tailWord_7229212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229212).length < 2 ^ (prefixWord ++ tailWord_7229212).sum := by decide
  have hdescent : baseEnd_7229212 < baseStart_7229212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229236 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 5]
def baseStart_7229236 : Nat := 118140960795 + 7229236 * 2 ^ 59
def prefixEnd_7229236 : Nat := 4983230072969 + 3 ^ 40 * 7229236 * 2
def baseEnd_7229236 : Nat := 412452536976309201622595

theorem tailTrace_7229236 : CollatzResearch.WordTrace tailWord_7229236 prefixEnd_7229236 412452536976309201622595 := by
  unfold tailWord_7229236
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835949218860051028993781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175781265625146734705325041 131835949218860051028993781)
  ·
    refine ⟨12359620239268129783968167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131835949218860051028993781 12359620239268129783968167)
    ·
      refine ⟨18539430358902194675952251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12359620239268129783968167 18539430358902194675952251)
      ·
        refine ⟨27809145538353292013928377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18539430358902194675952251 27809145538353292013928377)
        ·
          refine ⟨20856859153764969010446283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27809145538353292013928377 20856859153764969010446283)
          ·
            refine ⟨31285288730647453515669425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856859153764969010446283 31285288730647453515669425)
            ·
              refine ⟨23463966547985590136752069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31285288730647453515669425 23463966547985590136752069)
              ·
                refine ⟨4399493727747298150641013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23463966547985590136752069 4399493727747298150641013)
                ·
                  refine ⟨412452536976309201622595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399493727747298150641013 412452536976309201622595)
                  ·
                    rfl

theorem cell23_7229236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_7229236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229236 prefixEnd_7229236 := by exact prefixLift 7229236
  have htrace : WordTrace (prefixWord ++ tailWord_7229236) baseStart_7229236 baseEnd_7229236 := by
    simpa [prefixWord, tailWord_7229236, baseEnd_7229236] using wordTrace_append hprefix tailTrace_7229236
  have hstable : (prefixWord ++ tailWord_7229236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229236).length < 2 ^ (prefixWord ++ tailWord_7229236).sum := by decide
  have hdescent : baseEnd_7229236 < baseStart_7229236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229292 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 8]
def baseStart_7229292 : Nat := 118140960795 + 7229292 * 2 ^ 59
def prefixEnd_7229292 : Nat := 4983230072969 + 3 ^ 40 * 7229292 * 2
def baseEnd_7229292 : Nat := 412455731967048288389233

theorem tailTrace_7229292 : CollatzResearch.WordTrace tailWord_7229292 prefixEnd_7229292 412455731967048288389233 := by
  unfold tailWord_7229292
  simp only [CollatzResearch.WordTrace]
  refine ⟨131836970462758611811013065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175782627283678149081350753 131836970462758611811013065)
  ·
    refine ⟨98877727847068958858259799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131836970462758611811013065 98877727847068958858259799)
    ·
      refine ⟨148316591770603438287389699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98877727847068958858259799 148316591770603438287389699)
      ·
        refine ⟨222474887655905157431084549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148316591770603438287389699 222474887655905157431084549)
        ·
          refine ⟨41714041435482217018328353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222474887655905157431084549 41714041435482217018328353)
          ·
            refine ⟨31285531076611662763746265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41714041435482217018328353 31285531076611662763746265)
            ·
              refine ⟨23464148307458747072809699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31285531076611662763746265 23464148307458747072809699)
              ·
                refine ⟨35196222461188120609214549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23464148307458747072809699 35196222461188120609214549)
                ·
                  refine ⟨412455731967048288389233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35196222461188120609214549 412455731967048288389233)
                  ·
                    rfl

theorem cell23_7229292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_7229292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229292 prefixEnd_7229292 := by exact prefixLift 7229292
  have htrace : WordTrace (prefixWord ++ tailWord_7229292) baseStart_7229292 baseEnd_7229292 := by
    simpa [prefixWord, tailWord_7229292, baseEnd_7229292] using wordTrace_append hprefix tailTrace_7229292
  have hstable : (prefixWord ++ tailWord_7229292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229292).length < 2 ^ (prefixWord ++ tailWord_7229292).sum := by decide
  have hdescent : baseEnd_7229292 < baseStart_7229292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229329 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_7229329 : Nat := 118140960795 + 7229329 * 2 ^ 59
def prefixEnd_7229329 : Nat := 4983230072969 + 3 ^ 40 * 7229329 * 2
def baseEnd_7229329 : Nat := 3712120586487650950740427

theorem tailTrace_7229329 : CollatzResearch.WordTrace tailWord_7229329 prefixEnd_7229329 3712120586487650950740427 := by
  unfold tailWord_7229329
  simp only [CollatzResearch.WordTrace]
  refine ⟨263675290426383178941123041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175783526950922119294082027 263675290426383178941123041)
  ·
    refine ⟨197756467819787384205842281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263675290426383178941123041 197756467819787384205842281)
    ·
      refine ⟨148317350864840538154381711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197756467819787384205842281 148317350864840538154381711)
      ·
        refine ⟨222476026297260807231572567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148317350864840538154381711 222476026297260807231572567)
        ·
          refine ⟨333714039445891210847358851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222476026297260807231572567 333714039445891210847358851)
          ·
            refine ⟨500571059168836816271038277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333714039445891210847358851 500571059168836816271038277)
            ·
              refine ⟨93857073594156903050819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 500571059168836816271038277 93857073594156903050819677)
              ·
                refine ⟨35196402597808838644057379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93857073594156903050819677 35196402597808838644057379)
                ·
                  refine ⟨52794603896713257966086069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35196402597808838644057379 52794603896713257966086069)
                  ·
                    refine ⟨4949494115316867934320569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52794603896713257966086069 4949494115316867934320569)
                    ·
                      refine ⟨3712120586487650950740427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949494115316867934320569 3712120586487650950740427)
                      ·
                        rfl

theorem cell23_7229329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_7229329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229329 prefixEnd_7229329 := by exact prefixLift 7229329
  have htrace : WordTrace (prefixWord ++ tailWord_7229329) baseStart_7229329 baseEnd_7229329 := by
    simpa [prefixWord, tailWord_7229329, baseEnd_7229329] using wordTrace_append hprefix tailTrace_7229329
  have hstable : (prefixWord ++ tailWord_7229329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229329).length < 2 ^ (prefixWord ++ tailWord_7229329).sum := by decide
  have hdescent : baseEnd_7229329 < baseStart_7229329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229369 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_7229369 : Nat := 118140960795 + 7229369 * 2 ^ 59
def prefixEnd_7229369 : Nat := 4983230072969 + 3 ^ 40 * 7229369 * 2
def baseEnd_7229369 : Nat := 1237380375237943598080081

theorem tailTrace_7229369 : CollatzResearch.WordTrace tailWord_7229369 prefixEnd_7229369 1237380375237943598080081 := by
  unfold tailWord_7229369
  simp only [CollatzResearch.WordTrace]
  refine ⟨263676749346238265772579161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175784499564158843848386107 263676749346238265772579161)
  ·
    refine ⟨197757562009678699329434371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263676749346238265772579161 197757562009678699329434371)
    ·
      refine ⟨296636343014518048994151557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197757562009678699329434371 296636343014518048994151557)
      ·
        refine ⟨55619314315222134186403417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296636343014518048994151557 55619314315222134186403417)
        ·
          refine ⟨41714485736416600639802563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55619314315222134186403417 41714485736416600639802563)
          ·
            refine ⟨62571728604624900959703845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41714485736416600639802563 62571728604624900959703845)
            ·
              refine ⟨11732199113367168929944471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62571728604624900959703845 11732199113367168929944471)
              ·
                refine ⟨17598298670050753394916707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732199113367168929944471 17598298670050753394916707)
                ·
                  refine ⟨26397448005076130092375061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17598298670050753394916707 26397448005076130092375061)
                  ·
                    refine ⟨1237380375237943598080081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26397448005076130092375061 1237380375237943598080081)
                    ·
                      rfl

theorem cell23_7229369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_7229369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229369 prefixEnd_7229369 := by exact prefixLift 7229369
  have htrace : WordTrace (prefixWord ++ tailWord_7229369) baseStart_7229369 baseEnd_7229369 := by
    simpa [prefixWord, tailWord_7229369, baseEnd_7229369] using wordTrace_append hprefix tailTrace_7229369
  have hstable : (prefixWord ++ tailWord_7229369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229369).length < 2 ^ (prefixWord ++ tailWord_7229369).sum := by decide
  have hdescent : baseEnd_7229369 < baseStart_7229369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229409 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_7229409 : Nat := 118140960795 + 7229409 * 2 ^ 59
def prefixEnd_7229409 : Nat := 4983230072969 + 3 ^ 40 * 7229409 * 2
def baseEnd_7229409 : Nat := 3712161664940010637740059

theorem tailTrace_7229409 : CollatzResearch.WordTrace tailWord_7229409 prefixEnd_7229409 3712161664940010637740059 := by
  unfold tailWord_7229409
  simp only [CollatzResearch.WordTrace]
  refine ⟨263678208266093352604035281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175785472177395568402690187 263678208266093352604035281)
  ·
    refine ⟨197758656199570014453026461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263678208266093352604035281 197758656199570014453026461)
    ·
      refine ⟨74159496074838755419884923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197758656199570014453026461 74159496074838755419884923)
      ·
        refine ⟨111239244112258133129827385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74159496074838755419884923 111239244112258133129827385)
        ·
          refine ⟨83429433084193599847370539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111239244112258133129827385 83429433084193599847370539)
          ·
            refine ⟨125144149626290399771055809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83429433084193599847370539 125144149626290399771055809)
            ·
              refine ⟨93858112219717799828291857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125144149626290399771055809 93858112219717799828291857)
              ·
                refine ⟨70393584164788349871218893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93858112219717799828291857 70393584164788349871218893)
                ·
                  refine ⟨26397594061795631201707085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70393584164788349871218893 26397594061795631201707085)
                  ·
                    refine ⟨9899097773173361700640157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26397594061795631201707085 9899097773173361700640157)
                    ·
                      refine ⟨3712161664940010637740059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899097773173361700640157 3712161664940010637740059)
                      ·
                        rfl

theorem cell23_7229409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_7229409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229409 prefixEnd_7229409 := by exact prefixLift 7229409
  have htrace : WordTrace (prefixWord ++ tailWord_7229409) baseStart_7229409 baseEnd_7229409 := by
    simpa [prefixWord, tailWord_7229409, baseEnd_7229409] using wordTrace_append hprefix tailTrace_7229409
  have hstable : (prefixWord ++ tailWord_7229409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229409).length < 2 ^ (prefixWord ++ tailWord_7229409).sum := by decide
  have hdescent : baseEnd_7229409 < baseStart_7229409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229430 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7229430 : Nat := 118140960795 + 7229430 * 2 ^ 59
def prefixEnd_7229430 : Nat := 4983230072969 + 3 ^ 40 * 7229430 * 2
def baseEnd_7229430 : Nat := 3712172448033755055577463

theorem tailTrace_7229430 : CollatzResearch.WordTrace tailWord_7229430 prefixEnd_7229430 3712172448033755055577463 := by
  unfold tailWord_7229430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16479935887438579574409359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175785982799344848793699829 16479935887438579574409359)
  ·
    refine ⟨24719903831157869361614039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16479935887438579574409359 24719903831157869361614039)
    ·
      refine ⟨37079855746736804042421059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24719903831157869361614039 37079855746736804042421059)
      ·
        refine ⟨55619783620105206063631589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37079855746736804042421059 55619783620105206063631589)
        ·
          refine ⟨10428709428769726136930923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55619783620105206063631589 10428709428769726136930923)
          ·
            refine ⟨15643064143154589205396385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428709428769726136930923 15643064143154589205396385)
            ·
              refine ⟨11732298107365941904047289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15643064143154589205396385 11732298107365941904047289)
              ·
                refine ⟨8799223580524456428035467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732298107365941904047289 8799223580524456428035467)
                ·
                  refine ⟨13198835370786684642053201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799223580524456428035467 13198835370786684642053201)
                  ·
                    refine ⟨9899126528090013481539901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13198835370786684642053201 9899126528090013481539901)
                    ·
                      refine ⟨3712172448033755055577463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899126528090013481539901 3712172448033755055577463)
                      ·
                        rfl

theorem cell23_7229430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7229430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229430 prefixEnd_7229430 := by exact prefixLift 7229430
  have htrace : WordTrace (prefixWord ++ tailWord_7229430) baseStart_7229430 baseEnd_7229430 := by
    simpa [prefixWord, tailWord_7229430, baseEnd_7229430] using wordTrace_append hprefix tailTrace_7229430
  have hstable : (prefixWord ++ tailWord_7229430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229430).length < 2 ^ (prefixWord ++ tailWord_7229430).sum := by decide
  have hdescent : baseEnd_7229430 < baseStart_7229430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229486 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7229486 : Nat := 118140960795 + 7229486 * 2 ^ 59
def prefixEnd_7229486 : Nat := 4983230072969 + 3 ^ 40 * 7229486 * 2
def baseEnd_7229486 : Nat := 3712201202950406836477205

theorem tailTrace_7229486 : CollatzResearch.WordTrace tailWord_7229486 prefixEnd_7229486 3712201202950406836477205 := by
  unfold tailWord_7229486
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960127085851799344323539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175787344457876263169725541 32960127085851799344323539)
  ·
    refine ⟨49440190628777699016485309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32960127085851799344323539 49440190628777699016485309)
    ·
      refine ⟨18540071485791637131181991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49440190628777699016485309 18540071485791637131181991)
      ·
        refine ⟨27810107228687455696772987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18540071485791637131181991 27810107228687455696772987)
        ·
          refine ⟨41715160843031183545159481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27810107228687455696772987 41715160843031183545159481)
          ·
            refine ⟨31286370632273387658869611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41715160843031183545159481 31286370632273387658869611)
            ·
              refine ⟨46929555948410081488304417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31286370632273387658869611 46929555948410081488304417)
              ·
                refine ⟨35197166961307561116228313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46929555948410081488304417 35197166961307561116228313)
                ·
                  refine ⟨26397875220980670837171235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35197166961307561116228313 26397875220980670837171235)
                  ·
                    refine ⟨39596812831471006255756853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26397875220980670837171235 39596812831471006255756853)
                    ·
                      refine ⟨3712201202950406836477205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39596812831471006255756853 3712201202950406836477205)
                      ·
                        rfl

theorem cell23_7229486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7229486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229486 prefixEnd_7229486 := by exact prefixLift 7229486
  have htrace : WordTrace (prefixWord ++ tailWord_7229486) baseStart_7229486 baseEnd_7229486 := by
    simpa [prefixWord, tailWord_7229486, baseEnd_7229486] using wordTrace_append hprefix tailTrace_7229486
  have hstable : (prefixWord ++ tailWord_7229486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229486).length < 2 ^ (prefixWord ++ tailWord_7229486).sum := by decide
  have hdescent : baseEnd_7229486 < baseStart_7229486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3]
def baseStart_7229499 : Nat := 118140960795 + 7229499 * 2 ^ 59
def prefixEnd_7229499 : Nat := 4983230072969 + 3 ^ 40 * 7229499 * 2
def baseEnd_7229499 : Nat := 3712207878198915285614645

theorem tailTrace_7229499 : CollatzResearch.WordTrace tailWord_7229499 prefixEnd_7229499 3712207878198915285614645 := by
  unfold tailWord_7229499
  simp only [CollatzResearch.WordTrace]
  refine ⟨263681490835767297974811551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175787660557178198649874367 263681490835767297974811551)
  ·
    refine ⟨395522236253650946962217327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263681490835767297974811551 395522236253650946962217327)
    ·
      refine ⟨593283354380476420443325991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395522236253650946962217327 593283354380476420443325991)
      ·
        refine ⟨889925031570714630664988987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593283354380476420443325991 889925031570714630664988987)
        ·
          refine ⟨1334887547356071945997483481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889925031570714630664988987 1334887547356071945997483481)
          ·
            refine ⟨1001165660517053959498112611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334887547356071945997483481 1001165660517053959498112611)
            ·
              refine ⟨1501748490775580939247168917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001165660517053959498112611 1501748490775580939247168917)
              ·
                refine ⟨70394460505105356527211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1501748490775580939247168917 70394460505105356527211043)
                ·
                  refine ⟨105591690757658034790816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70394460505105356527211043 105591690757658034790816565)
                  ·
                    refine ⟨9899221008530440761639053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105591690757658034790816565 9899221008530440761639053)
                    ·
                      refine ⟨3712207878198915285614645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899221008530440761639053 3712207878198915285614645)
                      ·
                        rfl

theorem cell23_7229499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].length) (baseStart_7229499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229499 prefixEnd_7229499 := by exact prefixLift 7229499
  have htrace : WordTrace (prefixWord ++ tailWord_7229499) baseStart_7229499 baseEnd_7229499 := by
    simpa [prefixWord, tailWord_7229499, baseEnd_7229499] using wordTrace_append hprefix tailTrace_7229499
  have hstable : (prefixWord ++ tailWord_7229499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229499).length < 2 ^ (prefixWord ++ tailWord_7229499).sum := by decide
  have hdescent : baseEnd_7229499 < baseStart_7229499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229517 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7229517 : Nat := 118140960795 + 7229517 * 2 ^ 59
def prefixEnd_7229517 : Nat := 4983230072969 + 3 ^ 40 * 7229517 * 2
def baseEnd_7229517 : Nat := 3712217120850696215189563

theorem tailTrace_7229517 : CollatzResearch.WordTrace tailWord_7229517 prefixEnd_7229517 3712217120850696215189563 := by
  unfold tailWord_7229517
  simp only [CollatzResearch.WordTrace]
  refine ⟨263682147349702087048966805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175788098233134724699311203 263682147349702087048966805)
  ·
    refine ⟨12360100657017285330420319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263682147349702087048966805 12360100657017285330420319)
    ·
      refine ⟨18540150985525927995630479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12360100657017285330420319 18540150985525927995630479)
      ·
        refine ⟨27810226478288891993445719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18540150985525927995630479 27810226478288891993445719)
        ·
          refine ⟨41715339717433337990168579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27810226478288891993445719 41715339717433337990168579)
          ·
            refine ⟨62573009576150006985252869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41715339717433337990168579 62573009576150006985252869)
            ·
              refine ⟨11732439295528126309734913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62573009576150006985252869 11732439295528126309734913)
              ·
                refine ⟨8799329471646094732301185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732439295528126309734913 8799329471646094732301185)
                ·
                  refine ⟨6599497103734571049225889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799329471646094732301185 6599497103734571049225889)
                  ·
                    refine ⟨4949622827800928286919417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599497103734571049225889 4949622827800928286919417)
                    ·
                      refine ⟨3712217120850696215189563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949622827800928286919417 3712217120850696215189563)
                      ·
                        rfl

theorem cell23_7229517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7229517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229517 prefixEnd_7229517 := by exact prefixLift 7229517
  have htrace : WordTrace (prefixWord ++ tailWord_7229517) baseStart_7229517 baseEnd_7229517 := by
    simpa [prefixWord, tailWord_7229517, baseEnd_7229517] using wordTrace_append hprefix tailTrace_7229517
  have hstable : (prefixWord ++ tailWord_7229517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229517).length < 2 ^ (prefixWord ++ tailWord_7229517).sum := by decide
  have hdescent : baseEnd_7229517 < baseStart_7229517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229529 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_7229529 : Nat := 118140960795 + 7229529 * 2 ^ 59
def prefixEnd_7229529 : Nat := 4983230072969 + 3 ^ 40 * 7229529 * 2
def baseEnd_7229529 : Nat := 3712223282618550168239507

theorem tailTrace_7229529 : CollatzResearch.WordTrace tailWord_7229529 prefixEnd_7229529 3712223282618550168239507 := by
  unfold tailWord_7229529
  simp only [CollatzResearch.WordTrace]
  refine ⟨263682585025658613098403641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175788390017105742065602427 263682585025658613098403641)
  ·
    refine ⟨197761938769243959823802731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263682585025658613098403641 197761938769243959823802731)
    ·
      refine ⟨296642908153865939735704097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197761938769243959823802731 296642908153865939735704097)
      ·
        refine ⟨222482181115399454801778073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296642908153865939735704097 222482181115399454801778073)
        ·
          refine ⟨166861635836549591101333555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222482181115399454801778073 166861635836549591101333555)
          ·
            refine ⟨250292453754824386652000333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166861635836549591101333555 250292453754824386652000333)
            ·
              refine ⟨93859670158059144994500125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250292453754824386652000333 93859670158059144994500125)
              ·
                refine ⟨35197376309272179372937547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93859670158059144994500125 35197376309272179372937547)
                ·
                  refine ⟨52796064463908269059406321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35197376309272179372937547 52796064463908269059406321)
                  ·
                    refine ⟨39597048347931201794554741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52796064463908269059406321 39597048347931201794554741)
                    ·
                      refine ⟨3712223282618550168239507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39597048347931201794554741 3712223282618550168239507)
                      ·
                        rfl

theorem cell23_7229529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_7229529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229529 prefixEnd_7229529 := by exact prefixLift 7229529
  have htrace : WordTrace (prefixWord ++ tailWord_7229529) baseStart_7229529 baseEnd_7229529 := by
    simpa [prefixWord, tailWord_7229529, baseEnd_7229529] using wordTrace_append hprefix tailTrace_7229529
  have hstable : (prefixWord ++ tailWord_7229529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229529).length < 2 ^ (prefixWord ++ tailWord_7229529).sum := by decide
  have hdescent : baseEnd_7229529 < baseStart_7229529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229533 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7229533 : Nat := 118140960795 + 7229533 * 2 ^ 59
def prefixEnd_7229533 : Nat := 4983230072969 + 3 ^ 40 * 7229533 * 2
def baseEnd_7229533 : Nat := 3712225336541168152589489

theorem tailTrace_7229533 : CollatzResearch.WordTrace tailWord_7229533 prefixEnd_7229533 3712225336541168152589489 := by
  unfold tailWord_7229533
  simp only [CollatzResearch.WordTrace]
  refine ⟨263682730917644121781549253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175788487278429414521032835 263682730917644121781549253)
  ·
    refine ⟨49440512047058272834040485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263682730917644121781549253 49440512047058272834040485)
    ·
      refine ⟨9270096008823426156382591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49440512047058272834040485 9270096008823426156382591)
      ·
        refine ⟨13905144013235139234573887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270096008823426156382591 13905144013235139234573887)
        ·
          refine ⟨20857716019852708851860831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13905144013235139234573887 20857716019852708851860831)
          ·
            refine ⟨31286574029779063277791247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20857716019852708851860831 31286574029779063277791247)
            ·
              refine ⟨46929861044668594916686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31286574029779063277791247 46929861044668594916686871)
              ·
                refine ⟨70394791567002892375030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46929861044668594916686871 70394791567002892375030307)
                ·
                  refine ⟨105592187350504338562545461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70394791567002892375030307 105592187350504338562545461)
                  ·
                    refine ⟨9899267564109781740238637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105592187350504338562545461 9899267564109781740238637)
                    ·
                      refine ⟨3712225336541168152589489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899267564109781740238637 3712225336541168152589489)
                      ·
                        rfl

theorem cell23_7229533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7229533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229533 prefixEnd_7229533 := by exact prefixLift 7229533
  have htrace : WordTrace (prefixWord ++ tailWord_7229533) baseStart_7229533 baseEnd_7229533 := by
    simpa [prefixWord, tailWord_7229533, baseEnd_7229533] using wordTrace_append hprefix tailTrace_7229533
  have hstable : (prefixWord ++ tailWord_7229533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229533).length < 2 ^ (prefixWord ++ tailWord_7229533).sum := by decide
  have hdescent : baseEnd_7229533 < baseStart_7229533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229534 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7229534 : Nat := 118140960795 + 7229534 * 2 ^ 59
def prefixEnd_7229534 : Nat := 4983230072969 + 3 ^ 40 * 7229534 * 2
def baseEnd_7229534 : Nat := 3712225850021822648676985

theorem tailTrace_7229534 : CollatzResearch.WordTrace tailWord_7229534 prefixEnd_7229534 3712225850021822648676985 := by
  unfold tailWord_7229534
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960345923830062369041957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175788511593760332634890437 32960345923830062369041957)
  ·
    refine ⟨6180064860718136694195367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32960345923830062369041957 6180064860718136694195367)
    ·
      refine ⟨9270097291077205041293051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180064860718136694195367 9270097291077205041293051)
      ·
        refine ⟨13905145936615807561939577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270097291077205041293051 13905145936615807561939577)
        ·
          refine ⟨10428859452461855671454683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13905145936615807561939577 10428859452461855671454683)
          ·
            refine ⟨15643289178692783507182025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428859452461855671454683 15643289178692783507182025)
            ·
              refine ⟨11732466884019587630386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15643289178692783507182025 11732466884019587630386519)
              ·
                refine ⟨17598700326029381445579779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732466884019587630386519 17598700326029381445579779)
                ·
                  refine ⟨26398050489044072168369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17598700326029381445579779 26398050489044072168369669)
                  ·
                    refine ⟨4949634466695763531569313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26398050489044072168369669 4949634466695763531569313)
                    ·
                      refine ⟨3712225850021822648676985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949634466695763531569313 3712225850021822648676985)
                      ·
                        rfl

theorem cell23_7229534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7229534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229534 prefixEnd_7229534 := by exact prefixLift 7229534
  have htrace : WordTrace (prefixWord ++ tailWord_7229534) baseStart_7229534 baseEnd_7229534 := by
    simpa [prefixWord, tailWord_7229534, baseEnd_7229534] using wordTrace_append hprefix tailTrace_7229534
  have hstable : (prefixWord ++ tailWord_7229534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229534).length < 2 ^ (prefixWord ++ tailWord_7229534).sum := by decide
  have hdescent : baseEnd_7229534 < baseStart_7229534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229573 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_7229573 : Nat := 118140960795 + 7229573 * 2 ^ 59
def prefixEnd_7229573 : Nat := 4983230072969 + 3 ^ 40 * 7229573 * 2
def baseEnd_7229573 : Nat := 3712245875767347996089305

theorem tailTrace_7229573 : CollatzResearch.WordTrace tailWord_7229573 prefixEnd_7229573 3712245875767347996089305 := by
  unfold tailWord_7229573
  simp only [CollatzResearch.WordTrace]
  refine ⟨263684189837499208613005373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175789459891666139075336915 263684189837499208613005373)
  ·
    refine ⟨98881571189062203229877015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263684189837499208613005373 98881571189062203229877015)
    ·
      refine ⟨148322356783593304844815523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98881571189062203229877015 148322356783593304844815523)
      ·
        refine ⟨222483535175389957267223285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148322356783593304844815523 222483535175389957267223285)
        ·
          refine ⟨20857831422692808493802183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222483535175389957267223285 20857831422692808493802183)
          ·
            refine ⟨31286747134039212740703275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20857831422692808493802183 31286747134039212740703275)
            ·
              refine ⟨46930120701058819111054913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31286747134039212740703275 46930120701058819111054913)
              ·
                refine ⟨35197590525794114333291185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46930120701058819111054913 35197590525794114333291185)
                ·
                  refine ⟨26398192894345585749968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35197590525794114333291185 26398192894345585749968389)
                  ·
                    refine ⟨4949661167689797328119073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26398192894345585749968389 4949661167689797328119073)
                    ·
                      refine ⟨3712245875767347996089305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949661167689797328119073 3712245875767347996089305)
                      ·
                        rfl

theorem cell23_7229573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_7229573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229573 prefixEnd_7229573 := by exact prefixLift 7229573
  have htrace : WordTrace (prefixWord ++ tailWord_7229573) baseStart_7229573 baseEnd_7229573 := by
    simpa [prefixWord, tailWord_7229573, baseEnd_7229573] using wordTrace_append hprefix tailTrace_7229573
  have hstable : (prefixWord ++ tailWord_7229573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229573).length < 2 ^ (prefixWord ++ tailWord_7229573).sum := by decide
  have hdescent : baseEnd_7229573 < baseStart_7229573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229586 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7229586 : Nat := 118140960795 + 7229586 * 2 ^ 59
def prefixEnd_7229586 : Nat := 4983230072969 + 3 ^ 40 * 7229586 * 2
def baseEnd_7229586 : Nat := 3712252551015856445226745

theorem tailTrace_7229586 : CollatzResearch.WordTrace tailWord_7229586 prefixEnd_7229586 3712252551015856445226745 := by
  unfold tailWord_7229586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65921165996613027958307153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175789775990968074555485741 65921165996613027958307153)
  ·
    refine ⟨49440874497459770968730365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65921165996613027958307153 49440874497459770968730365)
    ·
      refine ⟨18540327936547414113273887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49440874497459770968730365 18540327936547414113273887)
      ·
        refine ⟨27810491904821121169910831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18540327936547414113273887 27810491904821121169910831)
        ·
          refine ⟨41715737857231681754866247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27810491904821121169910831 41715737857231681754866247)
          ·
            refine ⟨62573606785847522632299371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41715737857231681754866247 62573606785847522632299371)
            ·
              refine ⟨93860410178771283948449057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62573606785847522632299371 93860410178771283948449057)
              ·
                refine ⟨70395307634078462961336793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93860410178771283948449057 70395307634078462961336793)
                ·
                  refine ⟨52796480725558847221002595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70395307634078462961336793 52796480725558847221002595)
                  ·
                    refine ⟨79194721088338270831503893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52796480725558847221002595 79194721088338270831503893)
                    ·
                      refine ⟨3712252551015856445226745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79194721088338270831503893 3712252551015856445226745)
                      ·
                        rfl

theorem cell23_7229586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7229586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229586 prefixEnd_7229586 := by exact prefixLift 7229586
  have htrace : WordTrace (prefixWord ++ tailWord_7229586) baseStart_7229586 baseEnd_7229586 := by
    simpa [prefixWord, tailWord_7229586, baseEnd_7229586] using wordTrace_append hprefix tailTrace_7229586
  have hstable : (prefixWord ++ tailWord_7229586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229586).length < 2 ^ (prefixWord ++ tailWord_7229586).sum := by decide
  have hdescent : baseEnd_7229586 < baseStart_7229586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229634 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7229634 : Nat := 118140960795 + 7229634 * 2 ^ 59
def prefixEnd_7229634 : Nat := 4983230072969 + 3 ^ 40 * 7229634 * 2
def baseEnd_7229634 : Nat := 1237425732695757419142175

theorem tailTrace_7229634 : CollatzResearch.WordTrace tailWord_7229634 prefixEnd_7229634 1237425732695757419142175 := by
  unfold tailWord_7229634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65921603672569554007743989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175790943126852144020650637 65921603672569554007743989)
  ·
    refine ⟨6180150344303395688225999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65921603672569554007743989 6180150344303395688225999)
    ·
      refine ⟨9270225516455093532338999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180150344303395688225999 9270225516455093532338999)
      ·
        refine ⟨13905338274682640298508499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270225516455093532338999 13905338274682640298508499)
        ·
          refine ⟨20858007412023960447762749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13905338274682640298508499 20858007412023960447762749)
          ·
            refine ⟨7821752779508985167911031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20858007412023960447762749 7821752779508985167911031)
            ·
              refine ⟨11732629169263477751866547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821752779508985167911031 11732629169263477751866547)
              ·
                refine ⟨17598943753895216627799821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732629169263477751866547 17598943753895216627799821)
                ·
                  refine ⟨6599603907710706235424933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17598943753895216627799821 6599603907710706235424933)
                  ·
                    refine ⟨1237425732695757419142175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599603907710706235424933 1237425732695757419142175)
                    ·
                      rfl

theorem cell23_7229634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7229634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229634 prefixEnd_7229634 := by exact prefixLift 7229634
  have htrace : WordTrace (prefixWord ++ tailWord_7229634) baseStart_7229634 baseEnd_7229634 := by
    simpa [prefixWord, tailWord_7229634, baseEnd_7229634] using wordTrace_append hprefix tailTrace_7229634
  have hstable : (prefixWord ++ tailWord_7229634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229634).length < 2 ^ (prefixWord ++ tailWord_7229634).sum := by decide
  have hdescent : baseEnd_7229634 < baseStart_7229634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229677 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7229677 : Nat := 118140960795 + 7229677 * 2 ^ 59
def prefixEnd_7229677 : Nat := 4983230072969 + 3 ^ 40 * 7229677 * 2
def baseEnd_7229677 : Nat := 1237433092585138529729609

theorem tailTrace_7229677 : CollatzResearch.WordTrace tailWord_7229677 prefixEnd_7229677 1237433092585138529729609 := by
  unfold tailWord_7229677
  simp only [CollatzResearch.WordTrace]
  refine ⟨263687983029122434374791285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175791988686081622916527523 263687983029122434374791285)
  ·
    refine ⟨24720748408980228222636683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263687983029122434374791285 24720748408980228222636683)
    ·
      refine ⟨37081122613470342333955025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720748408980228222636683 37081122613470342333955025)
      ·
        refine ⟨27810841960102756750466269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37081122613470342333955025 27810841960102756750466269)
        ·
          refine ⟨10429065735038533781424851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27810841960102756750466269 10429065735038533781424851)
          ·
            refine ⟨15643598602557800672137277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10429065735038533781424851 15643598602557800672137277)
            ·
              refine ⟨5866349475959175252051479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15643598602557800672137277 5866349475959175252051479)
              ·
                refine ⟨8799524213938762878077219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866349475959175252051479 8799524213938762878077219)
                ·
                  refine ⟨13199286320908144317115829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799524213938762878077219 13199286320908144317115829)
                  ·
                    refine ⟨1237433092585138529729609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13199286320908144317115829 1237433092585138529729609)
                    ·
                      rfl

theorem cell23_7229677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7229677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229677 prefixEnd_7229677 := by exact prefixLift 7229677
  have htrace : WordTrace (prefixWord ++ tailWord_7229677) baseStart_7229677 baseEnd_7229677 := by
    simpa [prefixWord, tailWord_7229677, baseEnd_7229677] using wordTrace_append hprefix tailTrace_7229677
  have hstable : (prefixWord ++ tailWord_7229677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229677).length < 2 ^ (prefixWord ++ tailWord_7229677).sum := by decide
  have hdescent : baseEnd_7229677 < baseStart_7229677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229690 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_7229690 : Nat := 118140960795 + 7229690 * 2 ^ 59
def prefixEnd_7229690 : Nat := 4983230072969 + 3 ^ 40 * 7229690 * 2
def baseEnd_7229690 : Nat := 1237435317667974679442089

theorem tailTrace_7229690 : CollatzResearch.WordTrace tailWord_7229690 prefixEnd_7229690 1237435317667974679442089 := by
  unfold tailWord_7229690
  simp only [CollatzResearch.WordTrace]
  refine ⟨65922114294518834398753631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175792304785383558396676349 65922114294518834398753631)
  ·
    refine ⟨98883171441778251598130447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65922114294518834398753631 98883171441778251598130447)
    ·
      refine ⟨148324757162667377397195671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98883171441778251598130447 148324757162667377397195671)
      ·
        refine ⟨222487135744001066095793507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148324757162667377397195671 222487135744001066095793507)
        ·
          refine ⟨333730703616001599143690261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222487135744001066095793507 333730703616001599143690261)
          ·
            refine ⟨15643626732000074959860481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333730703616001599143690261 15643626732000074959860481)
            ·
              refine ⟨11732720049000056219895361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15643626732000074959860481 11732720049000056219895361)
              ·
                refine ⟨8799540036750042164921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732720049000056219895361 8799540036750042164921521)
                ·
                  refine ⟨6599655027562531623691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799540036750042164921521 6599655027562531623691141)
                  ·
                    refine ⟨1237435317667974679442089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599655027562531623691141 1237435317667974679442089)
                    ·
                      rfl

theorem cell23_7229690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_7229690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229690 prefixEnd_7229690 := by exact prefixLift 7229690
  have htrace : WordTrace (prefixWord ++ tailWord_7229690) baseStart_7229690 baseEnd_7229690 := by
    simpa [prefixWord, tailWord_7229690, baseEnd_7229690] using wordTrace_append hprefix tailTrace_7229690
  have hstable : (prefixWord ++ tailWord_7229690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229690).length < 2 ^ (prefixWord ++ tailWord_7229690).sum := by decide
  have hdescent : baseEnd_7229690 < baseStart_7229690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229706 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7229706 : Nat := 118140960795 + 7229706 * 2 ^ 59
def prefixEnd_7229706 : Nat := 4983230072969 + 3 ^ 40 * 7229706 * 2
def baseEnd_7229706 : Nat := 3712314168694395975726193

theorem tailTrace_7229706 : CollatzResearch.WordTrace tailWord_7229706 prefixEnd_7229706 3712314168694395975726193 := by
  unfold tailWord_7229706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65922260186504343081899243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175792693830678248218397981 65922260186504343081899243)
  ·
    refine ⟨98883390279756514622848865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65922260186504343081899243 98883390279756514622848865)
    ·
      refine ⟨74162542709817385967136649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98883390279756514622848865 74162542709817385967136649)
      ·
        refine ⟨55621907032363039475352487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74162542709817385967136649 55621907032363039475352487)
        ·
          refine ⟨83432860548544559213028731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55621907032363039475352487 83432860548544559213028731)
          ·
            refine ⟨125149290822816838819543097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83432860548544559213028731 125149290822816838819543097)
            ·
              refine ⟨93861968117112629114657323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125149290822816838819543097 93861968117112629114657323)
              ·
                refine ⟨140792952175668943671985985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93861968117112629114657323 140792952175668943671985985)
                ·
                  refine ⟨105594714131751707753989489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140792952175668943671985985 105594714131751707753989489)
                  ·
                    refine ⟨79196035598813780815492117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105594714131751707753989489 79196035598813780815492117)
                    ·
                      refine ⟨3712314168694395975726193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79196035598813780815492117 3712314168694395975726193)
                      ·
                        rfl

theorem cell23_7229706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7229706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229706 prefixEnd_7229706 := by exact prefixLift 7229706
  have htrace : WordTrace (prefixWord ++ tailWord_7229706) baseStart_7229706 baseEnd_7229706 := by
    simpa [prefixWord, tailWord_7229706, baseEnd_7229706] using wordTrace_append hprefix tailTrace_7229706
  have hstable : (prefixWord ++ tailWord_7229706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229706).length < 2 ^ (prefixWord ++ tailWord_7229706).sum := by decide
  have hdescent : baseEnd_7229706 < baseStart_7229706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229713 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_7229713 : Nat := 118140960795 + 7229713 * 2 ^ 59
def prefixEnd_7229713 : Nat := 4983230072969 + 3 ^ 40 * 7229713 * 2
def baseEnd_7229713 : Nat := 3712317763058977448338661

theorem tailTrace_7229713 : CollatzResearch.WordTrace tailWord_7229713 prefixEnd_7229713 3712317763058977448338661 := by
  unfold tailWord_7229713
  simp only [CollatzResearch.WordTrace]
  refine ⟨263689296056992012523101793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175792864037994675015401195 263689296056992012523101793)
  ·
    refine ⟨197766972042744009392326345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263689296056992012523101793 197766972042744009392326345)
    ·
      refine ⟨148325229032058007044244759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197766972042744009392326345 148325229032058007044244759)
      ·
        refine ⟨222487843548087010566367139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148325229032058007044244759 222487843548087010566367139)
        ·
          refine ⟨333731765322130515849550709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222487843548087010566367139 333731765322130515849550709)
          ·
            refine ⟨31287352998949735860895379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333731765322130515849550709 31287352998949735860895379)
            ·
              refine ⟨46931029498424603791343069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31287352998949735860895379 46931029498424603791343069)
              ·
                refine ⟨17599136061909226421753651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46931029498424603791343069 17599136061909226421753651)
                ·
                  refine ⟨26398704092863839632630477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17599136061909226421753651 26398704092863839632630477)
                  ·
                    refine ⟨9899514034823939862236429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26398704092863839632630477 9899514034823939862236429)
                    ·
                      refine ⟨3712317763058977448338661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899514034823939862236429 3712317763058977448338661)
                      ·
                        rfl

theorem cell23_7229713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_7229713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229713 prefixEnd_7229713 := by exact prefixLift 7229713
  have htrace : WordTrace (prefixWord ++ tailWord_7229713) baseStart_7229713 baseEnd_7229713 := by
    simpa [prefixWord, tailWord_7229713, baseEnd_7229713] using wordTrace_append hprefix tailTrace_7229713
  have hstable : (prefixWord ++ tailWord_7229713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229713).length < 2 ^ (prefixWord ++ tailWord_7229713).sum := by decide
  have hdescent : baseEnd_7229713 < baseStart_7229713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229730 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7229730 : Nat := 118140960795 + 7229730 * 2 ^ 59
def prefixEnd_7229730 : Nat := 4983230072969 + 3 ^ 40 * 7229730 * 2
def baseEnd_7229730 : Nat := 3712326492230103881826083

theorem tailTrace_7229730 : CollatzResearch.WordTrace tailWord_7229730 prefixEnd_7229730 3712326492230103881826083 := by
  unfold tailWord_7229730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65922479024482606106617661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175793277398620282950980429 65922479024482606106617661)
  ·
    refine ⟨24720929634180977289981623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65922479024482606106617661 24720929634180977289981623)
    ·
      refine ⟨37081394451271465934972435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720929634180977289981623 37081394451271465934972435)
      ·
        refine ⟨55622091676907198902458653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37081394451271465934972435 55622091676907198902458653)
        ·
          refine ⟨20858284378840199588421995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55622091676907198902458653 20858284378840199588421995)
          ·
            refine ⟨31287426568260299382632993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20858284378840199588421995 31287426568260299382632993)
            ·
              refine ⟨23465569926195224536974745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31287426568260299382632993 23465569926195224536974745)
              ·
                refine ⟨17599177444646418402731059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23465569926195224536974745 17599177444646418402731059)
                ·
                  refine ⟨26398766166969627604096589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17599177444646418402731059 26398766166969627604096589)
                  ·
                    refine ⟨9899537312613610351536221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26398766166969627604096589 9899537312613610351536221)
                    ·
                      refine ⟨3712326492230103881826083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899537312613610351536221 3712326492230103881826083)
                      ·
                        rfl

theorem cell23_7229730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7229730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229730 prefixEnd_7229730 := by exact prefixLift 7229730
  have htrace : WordTrace (prefixWord ++ tailWord_7229730) baseStart_7229730 baseEnd_7229730 := by
    simpa [prefixWord, tailWord_7229730, baseEnd_7229730] using wordTrace_append hprefix tailTrace_7229730
  have hstable : (prefixWord ++ tailWord_7229730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229730).length < 2 ^ (prefixWord ++ tailWord_7229730).sum := by decide
  have hdescent : baseEnd_7229730 < baseStart_7229730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229741 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7229741 : Nat := 118140960795 + 7229741 * 2 ^ 59
def prefixEnd_7229741 : Nat := 4983230072969 + 3 ^ 40 * 7229741 * 2
def baseEnd_7229741 : Nat := 1237444046839101112929511

theorem tailTrace_7229741 : CollatzResearch.WordTrace tailWord_7229741 prefixEnd_7229741 1237444046839101112929511 := by
  unfold tailWord_7229741
  simp only [CollatzResearch.WordTrace]
  refine ⟨263690317300890573305121077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175793544867260382203414051 263690317300890573305121077)
  ·
    refine ⟨24720967246958491247355101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263690317300890573305121077 24720967246958491247355101)
    ·
      refine ⟨9270362717609434217758163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24720967246958491247355101 9270362717609434217758163)
      ·
        refine ⟨13905544076414151326637245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270362717609434217758163 13905544076414151326637245)
        ·
          refine ⟨5214579028655306747488967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13905544076414151326637245 5214579028655306747488967)
          ·
            refine ⟨7821868542982960121233451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214579028655306747488967 7821868542982960121233451)
            ·
              refine ⟨11732802814474440181850177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821868542982960121233451 11732802814474440181850177)
              ·
                refine ⟨8799602110855830136387633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732802814474440181850177 8799602110855830136387633)
                ·
                  refine ⟨6599701583141872602290725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799602110855830136387633 6599701583141872602290725)
                  ·
                    refine ⟨1237444046839101112929511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599701583141872602290725 1237444046839101112929511)
                    ·
                      rfl

theorem cell23_7229741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7229741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229741 prefixEnd_7229741 := by exact prefixLift 7229741
  have htrace : WordTrace (prefixWord ++ tailWord_7229741) baseStart_7229741 baseEnd_7229741 := by
    simpa [prefixWord, tailWord_7229741, baseEnd_7229741] using wordTrace_append hprefix tailTrace_7229741
  have hstable : (prefixWord ++ tailWord_7229741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229741).length < 2 ^ (prefixWord ++ tailWord_7229741).sum := by decide
  have hdescent : baseEnd_7229741 < baseStart_7229741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229764 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7229764 : Nat := 118140960795 + 7229764 * 2 ^ 59
def prefixEnd_7229764 : Nat := 4983230072969 + 3 ^ 40 * 7229764 * 2
def baseEnd_7229764 : Nat := 3712343950572356748800927

theorem tailTrace_7229764 : CollatzResearch.WordTrace tailWord_7229764 prefixEnd_7229764 3712343950572356748800927 := by
  unfold tailWord_7229764
  simp only [CollatzResearch.WordTrace]
  refine ⟨131845578089903624116604173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175794104119871498822138897 131845578089903624116604173)
  ·
    refine ⟨49442091783713859043726565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131845578089903624116604173 49442091783713859043726565)
    ·
      refine ⟨9270392209446348570698731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49442091783713859043726565 9270392209446348570698731)
      ·
        refine ⟨13905588314169522856048097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270392209446348570698731 13905588314169522856048097)
        ·
          refine ⟨10429191235627142142036073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13905588314169522856048097 10429191235627142142036073)
          ·
            refine ⟨7821893426720356606527055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10429191235627142142036073 7821893426720356606527055)
            ·
              refine ⟨11732840140080534909790583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821893426720356606527055 11732840140080534909790583)
              ·
                refine ⟨17599260210120802364685875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732840140080534909790583 17599260210120802364685875)
                ·
                  refine ⟨26398890315181203547028813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17599260210120802364685875 26398890315181203547028813)
                  ·
                    refine ⟨9899583868192951330135805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26398890315181203547028813 9899583868192951330135805)
                    ·
                      refine ⟨3712343950572356748800927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899583868192951330135805 3712343950572356748800927)
                      ·
                        rfl

theorem cell23_7229764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7229764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229764 prefixEnd_7229764 := by exact prefixLift 7229764
  have htrace : WordTrace (prefixWord ++ tailWord_7229764) baseStart_7229764 baseEnd_7229764 := by
    simpa [prefixWord, tailWord_7229764, baseEnd_7229764] using wordTrace_append hprefix tailTrace_7229764
  have hstable : (prefixWord ++ tailWord_7229764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229764).length < 2 ^ (prefixWord ++ tailWord_7229764).sum := by decide
  have hdescent : baseEnd_7229764 < baseStart_7229764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229810 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_7229810 : Nat := 118140960795 + 7229810 * 2 ^ 59
def prefixEnd_7229810 : Nat := 4983230072969 + 3 ^ 40 * 7229810 * 2
def baseEnd_7229810 : Nat := 412485285631384840980635

theorem tailTrace_7229810 : CollatzResearch.WordTrace tailWord_7229810 prefixEnd_7229810 412485285631384840980635 := by
  unfold tailWord_7229810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65923208484410149522345721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175795222625093732059588589 65923208484410149522345721)
  ·
    refine ⟨49442406363307612141759291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65923208484410149522345721 49442406363307612141759291)
    ·
      refine ⟨74163609544961418212638937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49442406363307612141759291 74163609544961418212638937)
      ·
        refine ⟨55622707158721063659479203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74163609544961418212638937 55622707158721063659479203)
        ·
          refine ⟨83434060738081595489218805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55622707158721063659479203 83434060738081595489218805)
          ·
            refine ⟨7821943194195149577114263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83434060738081595489218805 7821943194195149577114263)
            ·
              refine ⟨11732914791292724365671395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821943194195149577114263 11732914791292724365671395)
              ·
                refine ⟨17599372186939086548507093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732914791292724365671395 17599372186939086548507093)
                ·
                  refine ⟨412485285631384840980635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17599372186939086548507093 412485285631384840980635)
                  ·
                    rfl

theorem cell23_7229810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_7229810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229810 prefixEnd_7229810 := by exact prefixLift 7229810
  have htrace : WordTrace (prefixWord ++ tailWord_7229810) baseStart_7229810 baseEnd_7229810 := by
    simpa [prefixWord, tailWord_7229810, baseEnd_7229810] using wordTrace_append hprefix tailTrace_7229810
  have hstable : (prefixWord ++ tailWord_7229810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229810).length < 2 ^ (prefixWord ++ tailWord_7229810).sum := by decide
  have hdescent : baseEnd_7229810 < baseStart_7229810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229821 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_7229821 : Nat := 118140960795 + 7229821 * 2 ^ 59
def prefixEnd_7229821 : Nat := 4983230072969 + 3 ^ 40 * 7229821 * 2
def baseEnd_7229821 : Nat := 3712373218969663025788165

theorem tailTrace_7229821 : CollatzResearch.WordTrace tailWord_7229821 prefixEnd_7229821 3712373218969663025788165 := by
  unfold tailWord_7229821
  simp only [CollatzResearch.WordTrace]
  refine ⟨263693235140600746968033317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175795490093733831312022211 263693235140600746968033317)
  ·
    refine ⟨49442481588862640056506247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263693235140600746968033317 49442481588862640056506247)
    ·
      refine ⟨74163722383293960084759371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49442481588862640056506247 74163722383293960084759371)
      ·
        refine ⟨111245583574940940127139057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74163722383293960084759371 111245583574940940127139057)
        ·
          refine ⟨83434187681205705095354293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111245583574940940127139057 83434187681205705095354293)
          ·
            refine ⟨7821955095113034852689465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83434187681205705095354293 7821955095113034852689465)
            ·
              refine ⟨5866466321334776139517099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7821955095113034852689465 5866466321334776139517099)
              ·
                refine ⟨8799699482002164209275649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866466321334776139517099 8799699482002164209275649)
                ·
                  refine ⟨6599774611501623156956737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799699482002164209275649 6599774611501623156956737)
                  ·
                    refine ⟨4949830958626217367717553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599774611501623156956737 4949830958626217367717553)
                    ·
                      refine ⟨3712373218969663025788165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949830958626217367717553 3712373218969663025788165)
                      ·
                        rfl

theorem cell23_7229821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_7229821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229821 prefixEnd_7229821 := by exact prefixLift 7229821
  have htrace : WordTrace (prefixWord ++ tailWord_7229821) baseStart_7229821 baseEnd_7229821 := by
    simpa [prefixWord, tailWord_7229821, baseEnd_7229821] using wordTrace_append hprefix tailTrace_7229821
  have hstable : (prefixWord ++ tailWord_7229821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229821).length < 2 ^ (prefixWord ++ tailWord_7229821).sum := by decide
  have hdescent : baseEnd_7229821 < baseStart_7229821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229860 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7229860 : Nat := 118140960795 + 7229860 * 2 ^ 59
def prefixEnd_7229860 : Nat := 4983230072969 + 3 ^ 40 * 7229860 * 2
def baseEnd_7229860 : Nat := 3712393244715188373200485

theorem tailTrace_7229860 : CollatzResearch.WordTrace tailWord_7229860 prefixEnd_7229860 3712393244715188373200485 := by
  unfold tailWord_7229860
  simp only [CollatzResearch.WordTrace]
  refine ⟨131847328793729728314351517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175796438391639637752468689 131847328793729728314351517)
  ·
    refine ⟨49442748297648648117881819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131847328793729728314351517 49442748297648648117881819)
    ·
      refine ⟨74164122446472972176822729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49442748297648648117881819 74164122446472972176822729)
      ·
        refine ⟨55623091834854729132617047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74164122446472972176822729 55623091834854729132617047)
        ·
          refine ⟨83434637752282093698925571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55623091834854729132617047 83434637752282093698925571)
          ·
            refine ⟨125151956628423140548388357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83434637752282093698925571 125151956628423140548388357)
            ·
              refine ⟨23465991867829338852822817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125151956628423140548388357 23465991867829338852822817)
              ·
                refine ⟨17599493900872004139617113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23465991867829338852822817 17599493900872004139617113)
                ·
                  refine ⟨13199620425654003104712835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17599493900872004139617113 13199620425654003104712835)
                  ·
                    refine ⟨19799430638481004657069253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13199620425654003104712835 19799430638481004657069253)
                    ·
                      refine ⟨3712393244715188373200485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19799430638481004657069253 3712393244715188373200485)
                      ·
                        rfl

theorem cell23_7229860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7229860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229860 prefixEnd_7229860 := by exact prefixLift 7229860
  have htrace : WordTrace (prefixWord ++ tailWord_7229860) baseStart_7229860 baseEnd_7229860 := by
    simpa [prefixWord, tailWord_7229860, baseEnd_7229860] using wordTrace_append hprefix tailTrace_7229860
  have hstable : (prefixWord ++ tailWord_7229860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229860).length < 2 ^ (prefixWord ++ tailWord_7229860).sum := by decide
  have hdescent : baseEnd_7229860 < baseStart_7229860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 7, 2, 2]
def baseStart_7229967 : Nat := 118140960795 + 7229967 * 2 ^ 59
def prefixEnd_7229967 : Nat := 4983230072969 + 3 ^ 40 * 7229967 * 2
def baseEnd_7229967 : Nat := 3712448187145219454562493

theorem tailTrace_7229967 : CollatzResearch.WordTrace tailWord_7229967 prefixEnd_7229967 3712448187145219454562493 := by
  unfold tailWord_7229967
  simp only [CollatzResearch.WordTrace]
  refine ⟨263698560198071813902848155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175799040132047875935232103 263698560198071813902848155)
  ·
    refine ⟨395547840297107720854272233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263698560198071813902848155 395547840297107720854272233)
    ·
      refine ⟨296660880222830790640704175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395547840297107720854272233 296660880222830790640704175)
      ·
        refine ⟨444991320334246185961056263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296660880222830790640704175 444991320334246185961056263)
        ·
          refine ⟨667486980501369278941584395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444991320334246185961056263 667486980501369278941584395)
          ·
            refine ⟨1001230470752053918412376593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667486980501369278941584395 1001230470752053918412376593)
            ·
              refine ⟨750922853064040438809282445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001230470752053918412376593 750922853064040438809282445)
              ·
                refine ⟨281596069899015164553480917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750922853064040438809282445 281596069899015164553480917)
                ·
                  refine ⟨6599907888258167919222209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281596069899015164553480917 6599907888258167919222209)
                  ·
                    refine ⟨4949930916193625939416657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599907888258167919222209 4949930916193625939416657)
                    ·
                      refine ⟨3712448187145219454562493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949930916193625939416657 3712448187145219454562493)
                      ·
                        rfl

theorem cell23_7229967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2, 2].length) (baseStart_7229967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229967 prefixEnd_7229967 := by exact prefixLift 7229967
  have htrace : WordTrace (prefixWord ++ tailWord_7229967) baseStart_7229967 baseEnd_7229967 := by
    simpa [prefixWord, tailWord_7229967, baseEnd_7229967] using wordTrace_append hprefix tailTrace_7229967
  have hstable : (prefixWord ++ tailWord_7229967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229967).length < 2 ^ (prefixWord ++ tailWord_7229967).sum := by decide
  have hdescent : baseEnd_7229967 < baseStart_7229967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229980 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7229980 : Nat := 118140960795 + 7229980 * 2 ^ 59
def prefixEnd_7229980 : Nat := 4983230072969 + 3 ^ 40 * 7229980 * 2
def baseEnd_7229980 : Nat := 3712454862393727903699933

theorem tailTrace_7229980 : CollatzResearch.WordTrace tailWord_7229980 prefixEnd_7229980 3712454862393727903699933 := by
  unfold tailWord_7229980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131849517173512358561535697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175799356231349811415380929 131849517173512358561535697)
  ·
    refine ⟨98887137880134268921151773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131849517173512358561535697 98887137880134268921151773)
    ·
      refine ⟨37082676705050350845431915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98887137880134268921151773 37082676705050350845431915)
      ·
        refine ⟨55624015057575526268147873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37082676705050350845431915 55624015057575526268147873)
        ·
          refine ⟨41718011293181644701110905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55624015057575526268147873 41718011293181644701110905)
          ·
            refine ⟨31288508469886233525833179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41718011293181644701110905 31288508469886233525833179)
            ·
              refine ⟨46932762704829350288749769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31288508469886233525833179 46932762704829350288749769)
              ·
                refine ⟨35199572028622012716562327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46932762704829350288749769 35199572028622012716562327)
                ·
                  refine ⟨52799358042933019074843491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35199572028622012716562327 52799358042933019074843491)
                  ·
                    refine ⟨79199037064399528612265237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52799358042933019074843491 79199037064399528612265237)
                    ·
                      refine ⟨3712454862393727903699933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79199037064399528612265237 3712454862393727903699933)
                      ·
                        rfl

theorem cell23_7229980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7229980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229980 prefixEnd_7229980 := by exact prefixLift 7229980
  have htrace : WordTrace (prefixWord ++ tailWord_7229980) baseStart_7229980 baseEnd_7229980 := by
    simpa [prefixWord, tailWord_7229980, baseEnd_7229980] using wordTrace_append hprefix tailTrace_7229980
  have hstable : (prefixWord ++ tailWord_7229980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229980).length < 2 ^ (prefixWord ++ tailWord_7229980).sum := by decide
  have hdescent : baseEnd_7229980 < baseStart_7229980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229994 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_7229994 : Nat := 118140960795 + 7229994 * 2 ^ 59
def prefixEnd_7229994 : Nat := 4983230072969 + 3 ^ 40 * 7229994 * 2
def baseEnd_7229994 : Nat := 1237487350374296949641623

theorem tailTrace_7229994 : CollatzResearch.WordTrace tailWord_7229994 prefixEnd_7229994 1237487350374296949641623 := by
  unfold tailWord_7229994
  simp only [CollatzResearch.WordTrace]
  refine ⟨65924886242243499378520259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175799696645982665009387357 65924886242243499378520259)
  ·
    refine ⟨98887329363365249067780389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65924886242243499378520259 98887329363365249067780389)
    ·
      refine ⟨18541374255630984200208823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98887329363365249067780389 18541374255630984200208823)
      ·
        refine ⟨27812061383446476300313235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18541374255630984200208823 27812061383446476300313235)
        ·
          refine ⟨41718092075169714450469853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27812061383446476300313235 41718092075169714450469853)
          ·
            refine ⟨15644284528188642918926195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41718092075169714450469853 15644284528188642918926195)
            ·
              refine ⟨23466426792282964378389293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15644284528188642918926195 23466426792282964378389293)
              ·
                refine ⟨8799910047106111641895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23466426792282964378389293 8799910047106111641895985)
                ·
                  refine ⟨6599932535329583731421989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799910047106111641895985 6599932535329583731421989)
                  ·
                    refine ⟨1237487350374296949641623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599932535329583731421989 1237487350374296949641623)
                    ·
                      rfl

theorem cell23_7229994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_7229994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7229994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7229994 prefixEnd_7229994 := by exact prefixLift 7229994
  have htrace : WordTrace (prefixWord ++ tailWord_7229994) baseStart_7229994 baseEnd_7229994 := by
    simpa [prefixWord, tailWord_7229994, baseEnd_7229994] using wordTrace_append hprefix tailTrace_7229994
  have hstable : (prefixWord ++ tailWord_7229994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229994).length < 2 ^ (prefixWord ++ tailWord_7229994).sum := by decide
  have hdescent : baseEnd_7229994 < baseStart_7229994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230017 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7230017 : Nat := 118140960795 + 7230017 * 2 ^ 59
def prefixEnd_7230017 : Nat := 4983230072969 + 3 ^ 40 * 7230017 * 2
def baseEnd_7230017 : Nat := 3712473861177944258937263

theorem tailTrace_7230017 : CollatzResearch.WordTrace tailWord_7230017 prefixEnd_7230017 3712473861177944258937263 := by
  unfold tailWord_7230017
  simp only [CollatzResearch.WordTrace]
  refine ⟨263700383847890672442168305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175800255898593781628112203 263700383847890672442168305)
  ·
    refine ⟨197775287885918004331626229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263700383847890672442168305 197775287885918004331626229)
    ·
      refine ⟨18541433239304812906089959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197775287885918004331626229 18541433239304812906089959)
      ·
        refine ⟨27812149858957219359134939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18541433239304812906089959 27812149858957219359134939)
        ·
          refine ⟨41718224788435829038702409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27812149858957219359134939 41718224788435829038702409)
          ·
            refine ⟨31288668591326871779026807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41718224788435829038702409 31288668591326871779026807)
            ·
              refine ⟨46933002886990307668540211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31288668591326871779026807 46933002886990307668540211)
              ·
                refine ⟨70399504330485461502810317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46933002886990307668540211 70399504330485461502810317)
                ·
                  refine ⟨26399814123932048063553869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70399504330485461502810317 26399814123932048063553869)
                  ·
                    refine ⟨9899930296474518023832701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26399814123932048063553869 9899930296474518023832701)
                    ·
                      refine ⟨3712473861177944258937263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9899930296474518023832701 3712473861177944258937263)
                      ·
                        rfl

theorem cell23_7230017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7230017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230017 prefixEnd_7230017 := by exact prefixLift 7230017
  have htrace : WordTrace (prefixWord ++ tailWord_7230017) baseStart_7230017 baseEnd_7230017 := by
    simpa [prefixWord, tailWord_7230017, baseEnd_7230017] using wordTrace_append hprefix tailTrace_7230017
  have hstable : (prefixWord ++ tailWord_7230017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230017).length < 2 ^ (prefixWord ++ tailWord_7230017).sum := by decide
  have hdescent : baseEnd_7230017 < baseStart_7230017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230030 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7230030 : Nat := 118140960795 + 7230030 * 2 ^ 59
def prefixEnd_7230030 : Nat := 4983230072969 + 3 ^ 40 * 7230030 * 2
def baseEnd_7230030 : Nat := 3712480536426452708074703

theorem tailTrace_7230030 : CollatzResearch.WordTrace tailWord_7230030 prefixEnd_7230030 3712480536426452708074703 := by
  unfold tailWord_7230030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32962607249605446957798943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175800571997895717108261029 32962607249605446957798943)
  ·
    refine ⟨49443910874408170436698415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32962607249605446957798943 49443910874408170436698415)
    ·
      refine ⟨74165866311612255655047623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49443910874408170436698415 74165866311612255655047623)
      ·
        refine ⟨111248799467418383482571435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74165866311612255655047623 111248799467418383482571435)
        ·
          refine ⟨166873199201127575223857153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111248799467418383482571435 166873199201127575223857153)
          ·
            refine ⟨125154899400845681417892865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166873199201127575223857153 125154899400845681417892865)
            ·
              refine ⟨93866174550634261063419649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125154899400845681417892865 93866174550634261063419649)
              ·
                refine ⟨70399630912975695797564737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93866174550634261063419649 70399630912975695797564737)
                ·
                  refine ⟨52799723184731771848173553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70399630912975695797564737 52799723184731771848173553)
                  ·
                    refine ⟨39599792388548828886130165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52799723184731771848173553 39599792388548828886130165)
                    ·
                      refine ⟨3712480536426452708074703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39599792388548828886130165 3712480536426452708074703)
                      ·
                        rfl

theorem cell23_7230030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7230030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230030 prefixEnd_7230030 := by exact prefixLift 7230030
  have htrace : WordTrace (prefixWord ++ tailWord_7230030) baseStart_7230030 baseEnd_7230030 := by
    simpa [prefixWord, tailWord_7230030, baseEnd_7230030] using wordTrace_append hprefix tailTrace_7230030
  have hstable : (prefixWord ++ tailWord_7230030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230030).length < 2 ^ (prefixWord ++ tailWord_7230030).sum := by decide
  have hdescent : baseEnd_7230030 < baseStart_7230030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230040 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7230040 : Nat := 118140960795 + 7230040 * 2 ^ 59
def prefixEnd_7230040 : Nat := 4983230072969 + 3 ^ 40 * 7230040 * 2
def baseEnd_7230040 : Nat := 3712485671232997668949657

theorem tailTrace_7230040 : CollatzResearch.WordTrace tailWord_7230040 prefixEnd_7230040 3712485671232997668949657 := by
  unfold tailWord_7230040
  simp only [CollatzResearch.WordTrace]
  refine ⟨131850611363403673685127787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175800815151204898246837049 131850611363403673685127787)
  ·
    refine ⟨197775917045105510527691681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131850611363403673685127787 197775917045105510527691681)
    ·
      refine ⟨148331937783829132895768761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197775917045105510527691681 148331937783829132895768761)
      ·
        refine ⟨111248953337871849671826571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148331937783829132895768761 111248953337871849671826571)
        ·
          refine ⟨166873430006807774507739857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111248953337871849671826571 166873430006807774507739857)
          ·
            refine ⟨125155072505105830880804893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166873430006807774507739857 125155072505105830880804893)
            ·
              refine ⟨46933152189414686580301835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125155072505105830880804893 46933152189414686580301835)
              ·
                refine ⟨70399728284122029870452753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46933152189414686580301835 70399728284122029870452753)
                ·
                  refine ⟨52799796213091522402839565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70399728284122029870452753 52799796213091522402839565)
                  ·
                    refine ⟨19799923579909320901064837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52799796213091522402839565 19799923579909320901064837)
                    ·
                      refine ⟨3712485671232997668949657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19799923579909320901064837 3712485671232997668949657)
                      ·
                        rfl

theorem cell23_7230040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7230040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230040 prefixEnd_7230040 := by exact prefixLift 7230040
  have htrace : WordTrace (prefixWord ++ tailWord_7230040) baseStart_7230040 baseEnd_7230040 := by
    simpa [prefixWord, tailWord_7230040, baseEnd_7230040] using wordTrace_append hprefix tailTrace_7230040
  have hstable : (prefixWord ++ tailWord_7230040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230040).length < 2 ^ (prefixWord ++ tailWord_7230040).sum := by decide
  have hdescent : baseEnd_7230040 < baseStart_7230040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230060 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7230060 : Nat := 118140960795 + 7230060 * 2 ^ 59
def prefixEnd_7230060 : Nat := 4983230072969 + 3 ^ 40 * 7230060 * 2
def baseEnd_7230060 : Nat := 3712495940846087590699565

theorem tailTrace_7230060 : CollatzResearch.WordTrace tailWord_7230060 prefixEnd_7230060 3712495940846087590699565 := by
  unfold tailWord_7230060
  simp only [CollatzResearch.WordTrace]
  refine ⟨131850976093367445392991817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175801301457823260523989089 131850976093367445392991817)
  ·
    refine ⟨98888232070025584044743863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131850976093367445392991817 98888232070025584044743863)
    ·
      refine ⟨148332348105038376067115795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98888232070025584044743863 148332348105038376067115795)
      ·
        refine ⟨222498522157557564100673693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148332348105038376067115795 222498522157557564100673693)
        ·
          refine ⟨83436945809084086537752635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222498522157557564100673693 83436945809084086537752635)
          ·
            refine ⟨125155418713626129806628953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83436945809084086537752635 125155418713626129806628953)
            ·
              refine ⟨93866564035219597354971715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125155418713626129806628953 93866564035219597354971715)
              ·
                refine ⟨140799846052829396032457573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93866564035219597354971715 140799846052829396032457573)
                ·
                  refine ⟨26399971134905511756085795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140799846052829396032457573 26399971134905511756085795)
                  ·
                    refine ⟨39599956702358267634128693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26399971134905511756085795 39599956702358267634128693)
                    ·
                      refine ⟨3712495940846087590699565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39599956702358267634128693 3712495940846087590699565)
                      ·
                        rfl

theorem cell23_7230060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7230060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230060 prefixEnd_7230060 := by exact prefixLift 7230060
  have htrace : WordTrace (prefixWord ++ tailWord_7230060) baseStart_7230060 baseEnd_7230060 := by
    simpa [prefixWord, tailWord_7230060, baseEnd_7230060] using wordTrace_append hprefix tailTrace_7230060
  have hstable : (prefixWord ++ tailWord_7230060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230060).length < 2 ^ (prefixWord ++ tailWord_7230060).sum := by decide
  have hdescent : baseEnd_7230060 < baseStart_7230060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_7230160 : Nat := 118140960795 + 7230160 * 2 ^ 59
def prefixEnd_7230160 : Nat := 4983230072969 + 3 ^ 40 * 7230160 * 2
def baseEnd_7230160 : Nat := 3712547288911537199449105

theorem tailTrace_7230160 : CollatzResearch.WordTrace tailWord_7230160 prefixEnd_7230160 3712547288911537199449105 := by
  unfold tailWord_7230160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131852799743186303932311967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175803732990915071909749289 131852799743186303932311967)
  ·
    refine ⟨197779199614779455898467951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131852799743186303932311967 197779199614779455898467951)
    ·
      refine ⟨296668799422169183847701927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197779199614779455898467951 296668799422169183847701927)
      ·
        refine ⟨445003199133253775771552891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296668799422169183847701927 445003199133253775771552891)
        ·
          refine ⟨667504798699880663657329337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445003199133253775771552891 667504798699880663657329337)
          ·
            refine ⟨500628599024910497742997003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667504798699880663657329337 500628599024910497742997003)
            ·
              refine ⟨750942898537365746614495505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500628599024910497742997003 750942898537365746614495505)
              ·
                refine ⟨563207173903024309960871629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750942898537365746614495505 563207173903024309960871629)
                ·
                  refine ⟨211202690213634116235326861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563207173903024309960871629 211202690213634116235326861)
                  ·
                    refine ⟨79201008830112793588247573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211202690213634116235326861 79201008830112793588247573)
                    ·
                      refine ⟨3712547288911537199449105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79201008830112793588247573 3712547288911537199449105)
                      ·
                        rfl

theorem cell23_7230160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_7230160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230160 prefixEnd_7230160 := by exact prefixLift 7230160
  have htrace : WordTrace (prefixWord ++ tailWord_7230160) baseStart_7230160 baseEnd_7230160 := by
    simpa [prefixWord, tailWord_7230160, baseEnd_7230160] using wordTrace_append hprefix tailTrace_7230160
  have hstable : (prefixWord ++ tailWord_7230160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230160).length < 2 ^ (prefixWord ++ tailWord_7230160).sum := by decide
  have hdescent : baseEnd_7230160 < baseStart_7230160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230204 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 6]
def baseStart_7230204 : Nat := 118140960795 + 7230204 * 2 ^ 59
def prefixEnd_7230204 : Nat := 4983230072969 + 3 ^ 40 * 7230204 * 2
def baseEnd_7230204 : Nat := 412507764673370558588767

theorem tailTrace_7230204 : CollatzResearch.WordTrace tailWord_7230204 prefixEnd_7230204 412507764673370558588767 := by
  unfold tailWord_7230204
  simp only [CollatzResearch.WordTrace]
  refine ⟨131853602149106601689612833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175804802865475468919483777 131853602149106601689612833)
  ·
    refine ⟨98890201611829951267209625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131853602149106601689612833 98890201611829951267209625)
    ·
      refine ⟨74167651208872463450407219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98890201611829951267209625 74167651208872463450407219)
      ·
        refine ⟨111251476813308695175610829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74167651208872463450407219 111251476813308695175610829)
        ·
          refine ⟨41719303804990760690854061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111251476813308695175610829 41719303804990760690854061)
          ·
            refine ⟨15644738926871535259070273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41719303804990760690854061 15644738926871535259070273)
            ·
              refine ⟨11733554195153651444302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15644738926871535259070273 11733554195153651444302705)
              ·
                refine ⟨8800165646365238583227029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733554195153651444302705 8800165646365238583227029)
                ·
                  refine ⟨412507764673370558588767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8800165646365238583227029 412507764673370558588767)
                  ·
                    rfl

theorem cell23_7230204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_7230204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230204 prefixEnd_7230204 := by exact prefixLift 7230204
  have htrace : WordTrace (prefixWord ++ tailWord_7230204) baseStart_7230204 baseEnd_7230204 := by
    simpa [prefixWord, tailWord_7230204, baseEnd_7230204] using wordTrace_append hprefix tailTrace_7230204
  have hstable : (prefixWord ++ tailWord_7230204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230204).length < 2 ^ (prefixWord ++ tailWord_7230204).sum := by decide
  have hdescent : baseEnd_7230204 < baseStart_7230204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230217 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_7230217 : Nat := 118140960795 + 7230217 * 2 ^ 59
def prefixEnd_7230217 : Nat := 4983230072969 + 3 ^ 40 * 7230217 * 2
def baseEnd_7230217 : Nat := 1237525519102947825478781

theorem tailTrace_7230217 : CollatzResearch.WordTrace tailWord_7230217 prefixEnd_7230217 1237525519102947825478781 := by
  unfold tailWord_7230217
  simp only [CollatzResearch.WordTrace]
  refine ⟨263707678447166106599448905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175805118964777404399632603 263707678447166106599448905)
  ·
    refine ⟨197780758835374579949586679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263707678447166106599448905 197780758835374579949586679)
    ·
      refine ⟨296671138253061869924380019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197780758835374579949586679 296671138253061869924380019)
      ·
        refine ⟨445006707379592804886570029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296671138253061869924380019 445006707379592804886570029)
        ·
          refine ⟨166877515267347301832463761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445006707379592804886570029 166877515267347301832463761)
          ·
            refine ⟨125158136450510476374347821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166877515267347301832463761 125158136450510476374347821)
            ·
              refine ⟨46934301168941428640380433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125158136450510476374347821 46934301168941428640380433)
              ·
                refine ⟨35200725876706071480285325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46934301168941428640380433 35200725876706071480285325)
                ·
                  refine ⟨13200272203764776805106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35200725876706071480285325 13200272203764776805106997)
                  ·
                    refine ⟨1237525519102947825478781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200272203764776805106997 1237525519102947825478781)
                    ·
                      rfl

theorem cell23_7230217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_7230217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230217 prefixEnd_7230217 := by exact prefixLift 7230217
  have htrace : WordTrace (prefixWord ++ tailWord_7230217) baseStart_7230217 baseEnd_7230217 := by
    simpa [prefixWord, tailWord_7230217, baseEnd_7230217] using wordTrace_append hprefix tailTrace_7230217
  have hstable : (prefixWord ++ tailWord_7230217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230217).length < 2 ^ (prefixWord ++ tailWord_7230217).sum := by decide
  have hdescent : baseEnd_7230217 < baseStart_7230217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230234 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_7230234 : Nat := 118140960795 + 7230234 * 2 ^ 59
def prefixEnd_7230234 : Nat := 4983230072969 + 3 ^ 40 * 7230234 * 2
def baseEnd_7230234 : Nat := 1237528428826656636641255

theorem tailTrace_7230234 : CollatzResearch.WordTrace tailWord_7230234 prefixEnd_7230234 1237528428826656636641255 := by
  unfold tailWord_7230234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65927074622026129625704439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175805532325403012335211837 65927074622026129625704439)
  ·
    refine ⟨98890611933039194438556659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65927074622026129625704439 98890611933039194438556659)
    ·
      refine ⟨148335917899558791657834989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98890611933039194438556659 148335917899558791657834989)
      ·
        refine ⟨55625969212334546871688121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148335917899558791657834989 55625969212334546871688121)
        ·
          refine ⟨41719476909250910153766091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55625969212334546871688121 41719476909250910153766091)
          ·
            refine ⟨62579215363876365230649137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41719476909250910153766091 62579215363876365230649137)
            ·
              refine ⟨46934411522907273922986853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62579215363876365230649137 46934411522907273922986853)
              ·
                refine ⟨8800202160545113860560035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46934411522907273922986853 8800202160545113860560035)
                ·
                  refine ⟨13200303240817670790840053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800202160545113860560035 13200303240817670790840053)
                  ·
                    refine ⟨1237528428826656636641255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200303240817670790840053 1237528428826656636641255)
                    ·
                      rfl

theorem cell23_7230234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_7230234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230234 prefixEnd_7230234 := by exact prefixLift 7230234
  have htrace : WordTrace (prefixWord ++ tailWord_7230234) baseStart_7230234 baseEnd_7230234 := by
    simpa [prefixWord, tailWord_7230234, baseEnd_7230234] using wordTrace_append hprefix tailTrace_7230234
  have hstable : (prefixWord ++ tailWord_7230234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230234).length < 2 ^ (prefixWord ++ tailWord_7230234).sum := by decide
  have hdescent : baseEnd_7230234 < baseStart_7230234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230264 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_7230264 : Nat := 118140960795 + 7230264 * 2 ^ 59
def prefixEnd_7230264 : Nat := 4983230072969 + 3 ^ 40 * 7230264 * 2
def baseEnd_7230264 : Nat := 1237533563633201597516209

theorem tailTrace_7230264 : CollatzResearch.WordTrace tailWord_7230264 prefixEnd_7230264 1237533563633201597516209 := by
  unfold tailWord_7230264
  simp only [CollatzResearch.WordTrace]
  refine ⟨131854696338997916813204923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175806261785330555750939897 131854696338997916813204923)
  ·
    refine ⟨197782044508496875219807385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131854696338997916813204923 197782044508496875219807385)
    ·
      refine ⟨148336533381372656414855539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197782044508496875219807385 148336533381372656414855539)
      ·
        refine ⟨222504800072058984622283309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148336533381372656414855539 222504800072058984622283309)
        ·
          refine ⟨83439300027022119233356241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222504800072058984622283309 83439300027022119233356241)
          ·
            refine ⟨62579475020266589425017181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83439300027022119233356241 62579475020266589425017181)
            ·
              refine ⟨23467303132599971034381443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62579475020266589425017181 23467303132599971034381443)
              ·
                refine ⟨35200954698899956551572165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23467303132599971034381443 35200954698899956551572165)
                ·
                  refine ⟨6600179006043741853419781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35200954698899956551572165 6600179006043741853419781)
                  ·
                    refine ⟨1237533563633201597516209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600179006043741853419781 1237533563633201597516209)
                    ·
                      rfl

theorem cell23_7230264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_7230264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230264 prefixEnd_7230264 := by exact prefixLift 7230264
  have htrace : WordTrace (prefixWord ++ tailWord_7230264) baseStart_7230264 baseEnd_7230264 := by
    simpa [prefixWord, tailWord_7230264, baseEnd_7230264] using wordTrace_append hprefix tailTrace_7230264
  have hstable : (prefixWord ++ tailWord_7230264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230264).length < 2 ^ (prefixWord ++ tailWord_7230264).sum := by decide
  have hdescent : baseEnd_7230264 < baseStart_7230264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230284 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7230284 : Nat := 118140960795 + 7230284 * 2 ^ 59
def prefixEnd_7230284 : Nat := 4983230072969 + 3 ^ 40 * 7230284 * 2
def baseEnd_7230284 : Nat := 3712610960512694714298535

theorem tailTrace_7230284 : CollatzResearch.WordTrace tailWord_7230284 prefixEnd_7230284 3712610960512694714298535 := by
  unfold tailWord_7230284
  simp only [CollatzResearch.WordTrace]
  refine ⟨131855061068961688521068953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175806748091948918028091937 131855061068961688521068953)
  ·
    refine ⟨98891295801721266390801715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131855061068961688521068953 98891295801721266390801715)
    ·
      refine ⟨148336943702581899586202573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98891295801721266390801715 148336943702581899586202573)
      ·
        refine ⟨55626353888468212344825965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148336943702581899586202573 55626353888468212344825965)
        ·
          refine ⟨20859882708175579629309737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55626353888468212344825965 20859882708175579629309737)
          ·
            refine ⟨15644912031131684721982303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20859882708175579629309737 15644912031131684721982303)
            ·
              refine ⟨23467368046697527082973455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15644912031131684721982303 23467368046697527082973455)
              ·
                refine ⟨35201052070046290624460183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23467368046697527082973455 35201052070046290624460183)
                ·
                  refine ⟨52801578105069435936690275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35201052070046290624460183 52801578105069435936690275)
                  ·
                    refine ⟨79202367157604153905035413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52801578105069435936690275 79202367157604153905035413)
                    ·
                      refine ⟨3712610960512694714298535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79202367157604153905035413 3712610960512694714298535)
                      ·
                        rfl

theorem cell23_7230284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7230284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230284 prefixEnd_7230284 := by exact prefixLift 7230284
  have htrace : WordTrace (prefixWord ++ tailWord_7230284) baseStart_7230284 baseEnd_7230284 := by
    simpa [prefixWord, tailWord_7230284, baseEnd_7230284] using wordTrace_append hprefix tailTrace_7230284
  have hstable : (prefixWord ++ tailWord_7230284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230284).length < 2 ^ (prefixWord ++ tailWord_7230284).sum := by decide
  have hdescent : baseEnd_7230284 < baseStart_7230284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230304 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_7230304 : Nat := 118140960795 + 7230304 * 2 ^ 59
def prefixEnd_7230304 : Nat := 4983230072969 + 3 ^ 40 * 7230304 * 2
def baseEnd_7230304 : Nat := 3712621230125784636048443

theorem tailTrace_7230304 : CollatzResearch.WordTrace tailWord_7230304 prefixEnd_7230304 3712621230125784636048443 := by
  unfold tailWord_7230304
  simp only [CollatzResearch.WordTrace]
  refine ⟨131855425798925460228932983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175807234398567280305243977 131855425798925460228932983)
  ·
    refine ⟨197783138698388190343399475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131855425798925460228932983 197783138698388190343399475)
    ·
      refine ⟨296674708047582285515099213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197783138698388190343399475 296674708047582285515099213)
      ·
        refine ⟨111253015517843357068162205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296674708047582285515099213 111253015517843357068162205)
        ·
          refine ⟨41719880819191258900560827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111253015517843357068162205 41719880819191258900560827)
          ·
            refine ⟨62579821228786888350841241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41719880819191258900560827 62579821228786888350841241)
            ·
              refine ⟨46934865921590166263130931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62579821228786888350841241 46934865921590166263130931)
              ·
                refine ⟨70402298882385249394696397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46934865921590166263130931 70402298882385249394696397)
                ·
                  refine ⟨26400862080894468523011149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70402298882385249394696397 26400862080894468523011149)
                  ·
                    refine ⟨9900323280335425696129181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26400862080894468523011149 9900323280335425696129181)
                    ·
                      refine ⟨3712621230125784636048443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9900323280335425696129181 3712621230125784636048443)
                      ·
                        rfl

theorem cell23_7230304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_7230304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230304 prefixEnd_7230304 := by exact prefixLift 7230304
  have htrace : WordTrace (prefixWord ++ tailWord_7230304) baseStart_7230304 baseEnd_7230304 := by
    simpa [prefixWord, tailWord_7230304, baseEnd_7230304] using wordTrace_append hprefix tailTrace_7230304
  have hstable : (prefixWord ++ tailWord_7230304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230304).length < 2 ^ (prefixWord ++ tailWord_7230304).sum := by decide
  have hdescent : baseEnd_7230304 < baseStart_7230304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230321 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_7230321 : Nat := 118140960795 + 7230321 * 2 ^ 59
def prefixEnd_7230321 : Nat := 4983230072969 + 3 ^ 40 * 7230321 * 2
def baseEnd_7230321 : Nat := 3712629959296911069535865

theorem tailTrace_7230321 : CollatzResearch.WordTrace tailWord_7230321 prefixEnd_7230321 3712629959296911069535865 := by
  unfold tailWord_7230321
  simp only [CollatzResearch.WordTrace]
  refine ⟨263711471638789332361234817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175807647759192888240823211 263711471638789332361234817)
  ·
    refine ⟨197783603729091999270926113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263711471638789332361234817 197783603729091999270926113)
    ·
      refine ⟨148337702796818999453194585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197783603729091999270926113 148337702796818999453194585)
      ·
        refine ⟨111253277097614249589895939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148337702796818999453194585 111253277097614249589895939)
        ·
          refine ⟨166879915646421374384843909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111253277097614249589895939 166879915646421374384843909)
          ·
            refine ⟨31289984183704007697158233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166879915646421374384843909 31289984183704007697158233)
            ·
              refine ⟨23467488137778005772868675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31289984183704007697158233 23467488137778005772868675)
              ·
                refine ⟨35201232206667008659303013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23467488137778005772868675 35201232206667008659303013)
                ·
                  refine ⟨6600231038750064123619315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35201232206667008659303013 6600231038750064123619315)
                  ·
                    refine ⟨9900346558125096185428973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6600231038750064123619315 9900346558125096185428973)
                    ·
                      refine ⟨3712629959296911069535865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9900346558125096185428973 3712629959296911069535865)
                      ·
                        rfl

theorem cell23_7230321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_7230321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230321 prefixEnd_7230321 := by exact prefixLift 7230321
  have htrace : WordTrace (prefixWord ++ tailWord_7230321) baseStart_7230321 baseEnd_7230321 := by
    simpa [prefixWord, tailWord_7230321, baseEnd_7230321] using wordTrace_append hprefix tailTrace_7230321
  have hstable : (prefixWord ++ tailWord_7230321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230321).length < 2 ^ (prefixWord ++ tailWord_7230321).sum := by decide
  have hdescent : baseEnd_7230321 < baseStart_7230321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230348 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_7230348 : Nat := 118140960795 + 7230348 * 2 ^ 59
def prefixEnd_7230348 : Nat := 4983230072969 + 3 ^ 40 * 7230348 * 2
def baseEnd_7230348 : Nat := 3712643823274582463898241

theorem tailTrace_7230348 : CollatzResearch.WordTrace tailWord_7230348 prefixEnd_7230348 3712643823274582463898241 := by
  unfold tailWord_7230348
  simp only [CollatzResearch.WordTrace]
  refine ⟨131856228204845757986233849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175808304273127677314978465 131856228204845757986233849)
  ·
    refine ⟨98892171153634318489675387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131856228204845757986233849 98892171153634318489675387)
    ·
      refine ⟨148338256730451477734513081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98892171153634318489675387 148338256730451477734513081)
      ·
        refine ⟨111253692547838608300884811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148338256730451477734513081 111253692547838608300884811)
        ·
          refine ⟨166880538821757912451327217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111253692547838608300884811 166880538821757912451327217)
          ·
            refine ⟨125160404116318434338495413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166880538821757912451327217 125160404116318434338495413)
            ·
              refine ⟨11733787885904853219233945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125160404116318434338495413 11733787885904853219233945)
              ·
                refine ⟨8800340914428639914425459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733787885904853219233945 8800340914428639914425459)
                ·
                  refine ⟨13200511371642959871638189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800340914428639914425459 13200511371642959871638189)
                  ·
                    refine ⟨4950191764366109951864321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13200511371642959871638189 4950191764366109951864321)
                    ·
                      refine ⟨3712643823274582463898241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950191764366109951864321 3712643823274582463898241)
                      ·
                        rfl

theorem cell23_7230348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_7230348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230348 prefixEnd_7230348 := by exact prefixLift 7230348
  have htrace : WordTrace (prefixWord ++ tailWord_7230348) baseStart_7230348 baseEnd_7230348 := by
    simpa [prefixWord, tailWord_7230348, baseEnd_7230348] using wordTrace_append hprefix tailTrace_7230348
  have hstable : (prefixWord ++ tailWord_7230348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230348).length < 2 ^ (prefixWord ++ tailWord_7230348).sum := by decide
  have hdescent : baseEnd_7230348 < baseStart_7230348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230365 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_7230365 : Nat := 118140960795 + 7230365 * 2 ^ 59
def prefixEnd_7230365 : Nat := 4983230072969 + 3 ^ 40 * 7230365 * 2
def baseEnd_7230365 : Nat := 3712652552445708897385663

theorem tailTrace_7230365 : CollatzResearch.WordTrace tailWord_7230365 prefixEnd_7230365 3712652552445708897385663 := by
  unfold tailWord_7230365
  simp only [CollatzResearch.WordTrace]
  refine ⟨263713076450629927875836549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175808717633753285250557699 263713076450629927875836549)
  ·
    refine ⟨49446201834493111476719353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263713076450629927875836549 49446201834493111476719353)
    ·
      refine ⟨37084651375869833607539515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49446201834493111476719353 37084651375869833607539515)
      ·
        refine ⟨55626977063804750411309273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37084651375869833607539515 55626977063804750411309273)
        ·
          refine ⟨41720232797853562808481955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55626977063804750411309273 41720232797853562808481955)
          ·
            refine ⟨62580349196780344212722933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41720232797853562808481955 62580349196780344212722933)
            ·
              refine ⟨5866907737198157269942775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62580349196780344212722933 5866907737198157269942775)
              ·
                refine ⟨8800361605797235904914163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866907737198157269942775 8800361605797235904914163)
                ·
                  refine ⟨13200542408695853857371245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800361605797235904914163 13200542408695853857371245)
                  ·
                    refine ⟨4950203403260945196514217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13200542408695853857371245 4950203403260945196514217)
                    ·
                      refine ⟨3712652552445708897385663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950203403260945196514217 3712652552445708897385663)
                      ·
                        rfl

theorem cell23_7230365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_7230365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230365 prefixEnd_7230365 := by exact prefixLift 7230365
  have htrace : WordTrace (prefixWord ++ tailWord_7230365) baseStart_7230365 baseEnd_7230365 := by
    simpa [prefixWord, tailWord_7230365, baseEnd_7230365] using wordTrace_append hprefix tailTrace_7230365
  have hstable : (prefixWord ++ tailWord_7230365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230365).length < 2 ^ (prefixWord ++ tailWord_7230365).sum := by decide
  have hdescent : baseEnd_7230365 < baseStart_7230365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230388 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7230388 : Nat := 118140960795 + 7230388 * 2 ^ 59
def prefixEnd_7230388 : Nat := 4983230072969 + 3 ^ 40 * 7230388 * 2
def baseEnd_7230388 : Nat := 1237554787500254102466019

theorem tailTrace_7230388 : CollatzResearch.WordTrace tailWord_7230388 prefixEnd_7230388 1237554787500254102466019 := by
  unfold tailWord_7230388
  simp only [CollatzResearch.WordTrace]
  refine ⟨131856957664773301401961909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175809276886364401869282545 131856957664773301401961909)
  ·
    refine ⟨12361589781072497006433929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131856957664773301401961909 12361589781072497006433929)
    ·
      refine ⟨9271192335804372754825447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12361589781072497006433929 9271192335804372754825447)
      ·
        refine ⟨13906788503706559132238171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271192335804372754825447 13906788503706559132238171)
        ·
          refine ⟨20860182755559838698357257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906788503706559132238171 20860182755559838698357257)
          ·
            refine ⟨15645137066669879023767943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20860182755559838698357257 15645137066669879023767943)
            ·
              refine ⟨23467705600004818535651915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15645137066669879023767943 23467705600004818535651915)
              ·
                refine ⟨35201558400007227803477873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23467705600004818535651915 35201558400007227803477873)
                ·
                  refine ⟨26401168800005420852608405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35201558400007227803477873 26401168800005420852608405)
                  ·
                    refine ⟨1237554787500254102466019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26401168800005420852608405 1237554787500254102466019)
                    ·
                      rfl

theorem cell23_7230388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7230388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230388 prefixEnd_7230388 := by exact prefixLift 7230388
  have htrace : WordTrace (prefixWord ++ tailWord_7230388) baseStart_7230388 baseEnd_7230388 := by
    simpa [prefixWord, tailWord_7230388, baseEnd_7230388] using wordTrace_append hprefix tailTrace_7230388
  have hstable : (prefixWord ++ tailWord_7230388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230388).length < 2 ^ (prefixWord ++ tailWord_7230388).sum := by decide
  have hdescent : baseEnd_7230388 < baseStart_7230388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230418 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_7230418 : Nat := 118140960795 + 7230418 * 2 ^ 59
def prefixEnd_7230418 : Nat := 4983230072969 + 3 ^ 40 * 7230418 * 2
def baseEnd_7230418 : Nat := 412519974102266354446991

theorem tailTrace_7230418 : CollatzResearch.WordTrace tailWord_7230418 prefixEnd_7230418 412519974102266354446991 := by
  unfold tailWord_7230418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65928752379859479481878977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175810006346291945285010605 65928752379859479481878977)
  ·
    refine ⟨49446564284894609611409233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65928752379859479481878977 49446564284894609611409233)
    ·
      refine ⟨37084923213670957208556925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49446564284894609611409233 37084923213670957208556925)
      ·
        refine ⟨13906846205126608953208847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37084923213670957208556925 13906846205126608953208847)
        ·
          refine ⟨20860269307689913429813271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906846205126608953208847 20860269307689913429813271)
          ·
            refine ⟨31290403961534870144719907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20860269307689913429813271 31290403961534870144719907)
            ·
              refine ⟨46935605942302305217079861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31290403961534870144719907 46935605942302305217079861)
              ·
                refine ⟨4400213057090841114101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46935605942302305217079861 4400213057090841114101237)
                ·
                  refine ⟨412519974102266354446991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400213057090841114101237 412519974102266354446991)
                  ·
                    rfl

theorem cell23_7230418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_7230418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230418 prefixEnd_7230418 := by exact prefixLift 7230418
  have htrace : WordTrace (prefixWord ++ tailWord_7230418) baseStart_7230418 baseEnd_7230418 := by
    simpa [prefixWord, tailWord_7230418, baseEnd_7230418] using wordTrace_append hprefix tailTrace_7230418
  have hstable : (prefixWord ++ tailWord_7230418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230418).length < 2 ^ (prefixWord ++ tailWord_7230418).sum := by decide
  have hdescent : baseEnd_7230418 < baseStart_7230418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230471 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7230471 : Nat := 118140960795 + 7230471 * 2 ^ 59
def prefixEnd_7230471 : Nat := 4983230072969 + 3 ^ 40 * 7230471 * 2
def baseEnd_7230471 : Nat := 3712706981395085482660175

theorem tailTrace_7230471 : CollatzResearch.WordTrace tailWord_7230471 prefixEnd_7230471 3712706981395085482660175 := by
  unfold tailWord_7230471
  simp only [CollatzResearch.WordTrace]
  refine ⟨263716942588245907979195267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175811295058830605319463511 263716942588245907979195267)
  ·
    refine ⟨395575413882368861968792901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263716942588245907979195267 395575413882368861968792901)
    ·
      refine ⟨74170390102944161619148669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395575413882368861968792901 74170390102944161619148669)
      ·
        refine ⟨27813896288604060607180751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74170390102944161619148669 27813896288604060607180751)
        ·
          refine ⟨41720844432906090910771127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27813896288604060607180751 41720844432906090910771127)
          ·
            refine ⟨62581266649359136366156691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41720844432906090910771127 62581266649359136366156691)
            ·
              refine ⟨93871899974038704549235037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62581266649359136366156691 93871899974038704549235037)
              ·
                refine ⟨35201962490264514205963139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93871899974038704549235037 35201962490264514205963139)
                ·
                  refine ⟨52802943735396771308944709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35201962490264514205963139 52802943735396771308944709)
                  ·
                    refine ⟨9900551950386894620427133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52802943735396771308944709 9900551950386894620427133)
                    ·
                      refine ⟨3712706981395085482660175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9900551950386894620427133 3712706981395085482660175)
                      ·
                        rfl

theorem cell23_7230471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7230471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230471 prefixEnd_7230471 := by exact prefixLift 7230471
  have htrace : WordTrace (prefixWord ++ tailWord_7230471) baseStart_7230471 baseEnd_7230471 := by
    simpa [prefixWord, tailWord_7230471, baseEnd_7230471] using wordTrace_append hprefix tailTrace_7230471
  have hstable : (prefixWord ++ tailWord_7230471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230471).length < 2 ^ (prefixWord ++ tailWord_7230471).sum := by decide
  have hdescent : baseEnd_7230471 < baseStart_7230471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230482 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7230482 : Nat := 118140960795 + 7230482 * 2 ^ 59
def prefixEnd_7230482 : Nat := 4983230072969 + 3 ^ 40 * 7230482 * 2
def baseEnd_7230482 : Nat := 1237570876560761646540875

theorem tailTrace_7230482 : CollatzResearch.WordTrace tailWord_7230482 prefixEnd_7230482 1237570876560761646540875 := by
  unfold tailWord_7230482
  simp only [CollatzResearch.WordTrace]
  refine ⟨65929335947801514214461425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175811562527470704571897133 65929335947801514214461425)
  ·
    refine ⟨49447001960851135660846069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65929335947801514214461425 49447001960851135660846069)
    ·
      refine ⟨4635656433829793968204319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49447001960851135660846069 4635656433829793968204319)
      ·
        refine ⟨6953484650744690952306479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635656433829793968204319 6953484650744690952306479)
        ·
          refine ⟨10430226976117036428459719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953484650744690952306479 10430226976117036428459719)
          ·
            refine ⟨15645340464175554642689579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430226976117036428459719 15645340464175554642689579)
            ·
              refine ⟨23468010696263331964034369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15645340464175554642689579 23468010696263331964034369)
              ·
                refine ⟨17601008022197498973025777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23468010696263331964034369 17601008022197498973025777)
                ·
                  refine ⟨13200756016648124229769333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601008022197498973025777 13200756016648124229769333)
                  ·
                    refine ⟨1237570876560761646540875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200756016648124229769333 1237570876560761646540875)
                    ·
                      rfl

theorem cell23_7230482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7230482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230482 prefixEnd_7230482 := by exact prefixLift 7230482
  have htrace : WordTrace (prefixWord ++ tailWord_7230482) baseStart_7230482 baseEnd_7230482 := by
    simpa [prefixWord, tailWord_7230482, baseEnd_7230482] using wordTrace_append hprefix tailTrace_7230482
  have hstable : (prefixWord ++ tailWord_7230482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230482).length < 2 ^ (prefixWord ++ tailWord_7230482).sum := by decide
  have hdescent : baseEnd_7230482 < baseStart_7230482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230488 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7230488 : Nat := 118140960795 + 7230488 * 2 ^ 59
def prefixEnd_7230488 : Nat := 4983230072969 + 3 ^ 40 * 7230488 * 2
def baseEnd_7230488 : Nat := 3712715710566211916147597

theorem tailTrace_7230488 : CollatzResearch.WordTrace tailWord_7230488 prefixEnd_7230488 3712715710566211916147597 := by
  unfold tailWord_7230488
  simp only [CollatzResearch.WordTrace]
  refine ⟨131858781314592159941282059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175811708419456213255042745 131858781314592159941282059)
  ·
    refine ⟨197788171971888239911923089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131858781314592159941282059 197788171971888239911923089)
    ·
      refine ⟨148341128978916179933942317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197788171971888239911923089 148341128978916179933942317)
      ·
        refine ⟨55627923367093567475228369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148341128978916179933942317 55627923367093567475228369)
        ·
          refine ⟨41720942525320175606421277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55627923367093567475228369 41720942525320175606421277)
          ·
            refine ⟨15645353446995065852407979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41720942525320175606421277 15645353446995065852407979)
            ·
              refine ⟨23468030170492598778611969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15645353446995065852407979 23468030170492598778611969)
              ·
                refine ⟨17601022627869449083958977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23468030170492598778611969 17601022627869449083958977)
                ·
                  refine ⟨13200766970902086812969233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601022627869449083958977 13200766970902086812969233)
                  ·
                    refine ⟨9900575228176565109726925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13200766970902086812969233 9900575228176565109726925)
                    ·
                      refine ⟨3712715710566211916147597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9900575228176565109726925 3712715710566211916147597)
                      ·
                        rfl

theorem cell23_7230488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7230488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230488 prefixEnd_7230488 := by exact prefixLift 7230488
  have htrace : WordTrace (prefixWord ++ tailWord_7230488) baseStart_7230488 baseEnd_7230488 := by
    simpa [prefixWord, tailWord_7230488, baseEnd_7230488] using wordTrace_append hprefix tailTrace_7230488
  have hstable : (prefixWord ++ tailWord_7230488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230488).length < 2 ^ (prefixWord ++ tailWord_7230488).sum := by decide
  have hdescent : baseEnd_7230488 < baseStart_7230488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230561 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_7230561 : Nat := 118140960795 + 7230561 * 2 ^ 59
def prefixEnd_7230561 : Nat := 4983230072969 + 3 ^ 40 * 7230561 * 2
def baseEnd_7230561 : Nat := 3712753194653990130534761

theorem tailTrace_7230561 : CollatzResearch.WordTrace tailWord_7230561 prefixEnd_7230561 3712753194653990130534761 := by
  unfold tailWord_7230561
  simp only [CollatzResearch.WordTrace]
  refine ⟨263720225157919853349971537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175813483438613235566647691 263720225157919853349971537)
  ·
    refine ⟨197790168868439890012478653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263720225157919853349971537 197790168868439890012478653)
    ·
      refine ⟨74171313325664958754679495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197790168868439890012478653 74171313325664958754679495)
      ·
        refine ⟨111256969988497438132019243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74171313325664958754679495 111256969988497438132019243)
        ·
          refine ⟨166885454982746157198028865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111256969988497438132019243 166885454982746157198028865)
          ·
            refine ⟨125164091237059617898521649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166885454982746157198028865 125164091237059617898521649)
            ·
              refine ⟨93873068427794713423891237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125164091237059617898521649 93873068427794713423891237)
              ·
                refine ⟨17601200330211508766979607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93873068427794713423891237 17601200330211508766979607)
                ·
                  refine ⟨26401800495317263150469411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17601200330211508766979607 26401800495317263150469411)
                  ·
                    refine ⟨39602700742975894725704117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26401800495317263150469411 39602700742975894725704117)
                    ·
                      refine ⟨3712753194653990130534761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39602700742975894725704117 3712753194653990130534761)
                      ·
                        rfl

theorem cell23_7230561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_7230561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230561 prefixEnd_7230561 := by exact prefixLift 7230561
  have htrace : WordTrace (prefixWord ++ tailWord_7230561) baseStart_7230561 baseEnd_7230561 := by
    simpa [prefixWord, tailWord_7230561, baseEnd_7230561] using wordTrace_append hprefix tailTrace_7230561
  have hstable : (prefixWord ++ tailWord_7230561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230561).length < 2 ^ (prefixWord ++ tailWord_7230561).sum := by decide
  have hdescent : baseEnd_7230561 < baseStart_7230561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230575 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 3, 2, 2]
def baseStart_7230575 : Nat := 118140960795 + 7230575 * 2 ^ 59
def prefixEnd_7230575 : Nat := 4983230072969 + 3 ^ 40 * 7230575 * 2
def baseEnd_7230575 : Nat := 3712760383383153075759697

theorem tailTrace_7230575 : CollatzResearch.WordTrace tailWord_7230575 prefixEnd_7230575 3712760383383153075759697 := by
  unfold tailWord_7230575
  simp only [CollatzResearch.WordTrace]
  refine ⟨263720735779869133740981179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175813823853246089160654119 263720735779869133740981179)
  ·
    refine ⟨395581103669803700611471769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263720735779869133740981179 395581103669803700611471769)
    ·
      refine ⟨296685827752352775458603827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395581103669803700611471769 296685827752352775458603827)
      ·
        refine ⟨445028741628529163187905741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296685827752352775458603827 445028741628529163187905741)
        ·
          refine ⟨166885778110698436195464653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445028741628529163187905741 166885778110698436195464653)
          ·
            refine ⟨62582166791511913573299245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166885778110698436195464653 62582166791511913573299245)
            ·
              refine ⟨23468312546816967589987217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62582166791511913573299245 23468312546816967589987217)
              ·
                refine ⟨17601234410112725692490413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23468312546816967589987217 17601234410112725692490413)
                ·
                  refine ⟨6600462903792272134683905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17601234410112725692490413 6600462903792272134683905)
                  ·
                    refine ⟨4950347177844204101012929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6600462903792272134683905 4950347177844204101012929)
                    ·
                      refine ⟨3712760383383153075759697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950347177844204101012929 3712760383383153075759697)
                      ·
                        rfl

theorem cell23_7230575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2, 2].length) (baseStart_7230575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230575 prefixEnd_7230575 := by exact prefixLift 7230575
  have htrace : WordTrace (prefixWord ++ tailWord_7230575) baseStart_7230575 baseEnd_7230575 := by
    simpa [prefixWord, tailWord_7230575, baseEnd_7230575] using wordTrace_append hprefix tailTrace_7230575
  have hstable : (prefixWord ++ tailWord_7230575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230575).length < 2 ^ (prefixWord ++ tailWord_7230575).sum := by decide
  have hdescent : baseEnd_7230575 < baseStart_7230575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230578 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7230578 : Nat := 118140960795 + 7230578 * 2 ^ 59
def prefixEnd_7230578 : Nat := 4983230072969 + 3 ^ 40 * 7230578 * 2
def baseEnd_7230578 : Nat := 3712761923825116564022183

theorem tailTrace_7230578 : CollatzResearch.WordTrace tailWord_7230578 prefixEnd_7230578 3712761923825116564022183 := by
  unfold tailWord_7230578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65930211299714566313335097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175813896799238843502226925 65930211299714566313335097)
  ·
    refine ⟨49447658474785924735001323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65930211299714566313335097 49447658474785924735001323)
    ·
      refine ⟨74171487712178887102501985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49447658474785924735001323 74171487712178887102501985)
      ·
        refine ⟨55628615784134165326876489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74171487712178887102501985 55628615784134165326876489)
        ·
          refine ⟨41721461838100623995157367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55628615784134165326876489 41721461838100623995157367)
          ·
            refine ⟨62582192757150935992736051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41721461838100623995157367 62582192757150935992736051)
            ·
              refine ⟨93873289135726403989104077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62582192757150935992736051 93873289135726403989104077)
              ·
                refine ⟨35202483425897401495914029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93873289135726403989104077 35202483425897401495914029)
                ·
                  refine ⟨13200931284711525560967761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35202483425897401495914029 13200931284711525560967761)
                  ·
                    refine ⟨9900698463533644170725821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13200931284711525560967761 9900698463533644170725821)
                    ·
                      refine ⟨3712761923825116564022183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9900698463533644170725821 3712761923825116564022183)
                      ·
                        rfl

theorem cell23_7230578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7230578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230578 prefixEnd_7230578 := by exact prefixLift 7230578
  have htrace : WordTrace (prefixWord ++ tailWord_7230578) baseStart_7230578 baseEnd_7230578 := by
    simpa [prefixWord, tailWord_7230578, baseEnd_7230578] using wordTrace_append hprefix tailTrace_7230578
  have hstable : (prefixWord ++ tailWord_7230578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230578).length < 2 ^ (prefixWord ++ tailWord_7230578).sum := by decide
  have hdescent : baseEnd_7230578 < baseStart_7230578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230592 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 1, 2, 2]
def baseStart_7230592 : Nat := 118140960795 + 7230592 * 2 ^ 59
def prefixEnd_7230592 : Nat := 4983230072969 + 3 ^ 40 * 7230592 * 2
def baseEnd_7230592 : Nat := 3712769112554279509247119

theorem tailTrace_7230592 : CollatzResearch.WordTrace tailWord_7230592 prefixEnd_7230592 3712769112554279509247119 := by
  unfold tailWord_7230592
  simp only [CollatzResearch.WordTrace]
  refine ⟨131860677910403772822175015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175814237213871697096233353 131860677910403772822175015)
  ·
    refine ⟨197791016865605659233262523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131860677910403772822175015 197791016865605659233262523)
    ·
      refine ⟨296686525298408488849893785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197791016865605659233262523 296686525298408488849893785)
      ·
        refine ⟨222514893973806366637420339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296686525298408488849893785 222514893973806366637420339)
        ·
          refine ⟨333772340960709549956130509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222514893973806366637420339 333772340960709549956130509)
          ·
            refine ⟨125164627860266081233548941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333772340960709549956130509 125164627860266081233548941)
            ·
              refine ⟨46936735447599780462580853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125164627860266081233548941 46936735447599780462580853)
              ·
                refine ⟨4400318948212479418366955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46936735447599780462580853 4400318948212479418366955)
                ·
                  refine ⟨6600478422318719127550433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400318948212479418366955 6600478422318719127550433)
                  ·
                    refine ⟨4950358816739039345662825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6600478422318719127550433 4950358816739039345662825)
                    ·
                      refine ⟨3712769112554279509247119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950358816739039345662825 3712769112554279509247119)
                      ·
                        rfl

theorem cell23_7230592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_7230592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230592 prefixEnd_7230592 := by exact prefixLift 7230592
  have htrace : WordTrace (prefixWord ++ tailWord_7230592) baseStart_7230592 baseEnd_7230592 := by
    simpa [prefixWord, tailWord_7230592, baseEnd_7230592] using wordTrace_append hprefix tailTrace_7230592
  have hstable : (prefixWord ++ tailWord_7230592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230592).length < 2 ^ (prefixWord ++ tailWord_7230592).sum := by decide
  have hdescent : baseEnd_7230592 < baseStart_7230592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230622 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7230622 : Nat := 118140960795 + 7230622 * 2 ^ 59
def prefixEnd_7230622 : Nat := 4983230072969 + 3 ^ 40 * 7230622 * 2
def baseEnd_7230622 : Nat := 3712784516973914391871981

theorem tailTrace_7230622 : CollatzResearch.WordTrace tailWord_7230622 prefixEnd_7230622 3712784516973914391871981 := by
  unfold tailWord_7230622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32965306251337357595992765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175814966673799240511961413 32965306251337357595992765)
  ·
    refine ⟨12361989844251509098497287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32965306251337357595992765 12361989844251509098497287)
    ·
      refine ⟨18542984766377263647745931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361989844251509098497287 18542984766377263647745931)
      ·
        refine ⟨27814477149565895471618897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18542984766377263647745931 27814477149565895471618897)
        ·
          refine ⟨20860857862174421603714173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27814477149565895471618897 20860857862174421603714173)
          ·
            refine ⟨7822821698315408101392815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20860857862174421603714173 7822821698315408101392815)
            ·
              refine ⟨11734232547473112152089223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822821698315408101392815 11734232547473112152089223)
              ·
                refine ⟨17601348821209668228133835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734232547473112152089223 17601348821209668228133835)
                ·
                  refine ⟨26402023231814502342200753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17601348821209668228133835 26402023231814502342200753)
                  ·
                    refine ⟨19801517423860876756650565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26402023231814502342200753 19801517423860876756650565)
                    ·
                      refine ⟨3712784516973914391871981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19801517423860876756650565 3712784516973914391871981)
                      ·
                        rfl

theorem cell23_7230622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7230622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230622 prefixEnd_7230622 := by exact prefixLift 7230622
  have htrace : WordTrace (prefixWord ++ tailWord_7230622) baseStart_7230622 baseEnd_7230622 := by
    simpa [prefixWord, tailWord_7230622, baseEnd_7230622] using wordTrace_append hprefix tailTrace_7230622
  have hstable : (prefixWord ++ tailWord_7230622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230622).length < 2 ^ (prefixWord ++ tailWord_7230622).sum := by decide
  have hdescent : baseEnd_7230622 < baseStart_7230622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230652 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_7230652 : Nat := 118140960795 + 7230652 * 2 ^ 59
def prefixEnd_7230652 : Nat := 4983230072969 + 3 ^ 40 * 7230652 * 2
def baseEnd_7230652 : Nat := 3712799921393549274496843

theorem tailTrace_7230652 : CollatzResearch.WordTrace tailWord_7230652 prefixEnd_7230652 3712799921393549274496843 := by
  unfold tailWord_7230652
  simp only [CollatzResearch.WordTrace]
  refine ⟨131861772100295087945767105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175815696133726783927689473 131861772100295087945767105)
  ·
    refine ⟨98896329075221315959325329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131861772100295087945767105 98896329075221315959325329)
    ·
      refine ⟨74172246806415986969493997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98896329075221315959325329 74172246806415986969493997)
      ·
        refine ⟨27814592552405995113560249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74172246806415986969493997 27814592552405995113560249)
        ·
          refine ⟨20860944414304496335170187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27814592552405995113560249 20860944414304496335170187)
          ·
            refine ⟨31291416621456744502755281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20860944414304496335170187 31291416621456744502755281)
            ·
              refine ⟨23468562466092558377066461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31291416621456744502755281 23468562466092558377066461)
              ·
                refine ⟨8800710924784709391399923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23468562466092558377066461 8800710924784709391399923)
                ·
                  refine ⟨13201066387177064087099885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800710924784709391399923 13201066387177064087099885)
                  ·
                    refine ⟨4950399895191399032662457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13201066387177064087099885 4950399895191399032662457)
                    ·
                      refine ⟨3712799921393549274496843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950399895191399032662457 3712799921393549274496843)
                      ·
                        rfl

theorem cell23_7230652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_7230652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230652 prefixEnd_7230652 := by exact prefixLift 7230652
  have htrace : WordTrace (prefixWord ++ tailWord_7230652) baseStart_7230652 baseEnd_7230652 := by
    simpa [prefixWord, tailWord_7230652, baseEnd_7230652] using wordTrace_append hprefix tailTrace_7230652
  have hstable : (prefixWord ++ tailWord_7230652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230652).length < 2 ^ (prefixWord ++ tailWord_7230652).sum := by decide
  have hdescent : baseEnd_7230652 < baseStart_7230652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230671 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 7]
def baseStart_7230671 : Nat := 118140960795 + 7230671 * 2 ^ 59
def prefixEnd_7230671 : Nat := 4983230072969 + 3 ^ 40 * 7230671 * 2
def baseEnd_7230671 : Nat := 412534408613998300017695

theorem tailTrace_7230671 : CollatzResearch.WordTrace tailWord_7230671 prefixEnd_7230671 412534408613998300017695 := by
  unfold tailWord_7230671
  simp only [CollatzResearch.WordTrace]
  refine ⟨263724237187521342136475867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175816158125014228090983911 263724237187521342136475867)
  ·
    refine ⟨395586355781282013204713801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263724237187521342136475867 395586355781282013204713801)
    ·
      refine ⟨296689766835961509903535351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395586355781282013204713801 296689766835961509903535351)
      ·
        refine ⟨445034650253942264855303027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296689766835961509903535351 445034650253942264855303027)
        ·
          refine ⟨667551975380913397282954541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445034650253942264855303027 667551975380913397282954541)
          ·
            refine ⟨250331990767842523981107953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667551975380913397282954541 250331990767842523981107953)
            ·
              refine ⟨187748993075881892985830965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250331990767842523981107953 187748993075881892985830965)
              ·
                refine ⟨17601468100863927467421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187748993075881892985830965 17601468100863927467421653)
                ·
                  refine ⟨412534408613998300017695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17601468100863927467421653 412534408613998300017695)
                  ·
                    rfl

theorem cell23_7230671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 7].length) (baseStart_7230671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230671 prefixEnd_7230671 := by exact prefixLift 7230671
  have htrace : WordTrace (prefixWord ++ tailWord_7230671) baseStart_7230671 baseEnd_7230671 := by
    simpa [prefixWord, tailWord_7230671, baseEnd_7230671] using wordTrace_append hprefix tailTrace_7230671
  have hstable : (prefixWord ++ tailWord_7230671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230671).length < 2 ^ (prefixWord ++ tailWord_7230671).sum := by decide
  have hdescent : baseEnd_7230671 < baseStart_7230671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230711 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_7230711 : Nat := 118140960795 + 7230711 * 2 ^ 59
def prefixEnd_7230711 : Nat := 4983230072969 + 3 ^ 40 * 7230711 * 2
def baseEnd_7230711 : Nat := 3712830216752164543659071

theorem tailTrace_7230711 : CollatzResearch.WordTrace tailWord_7230711 prefixEnd_7230711 3712830216752164543659071 := by
  unfold tailWord_7230711
  simp only [CollatzResearch.WordTrace]
  refine ⟨263725696107376428967931987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175817130738250952645287991 263725696107376428967931987)
  ·
    refine ⟨395588544161064643451897981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263725696107376428967931987 395588544161064643451897981)
    ·
      refine ⟨148345704060399241294461743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395588544161064643451897981 148345704060399241294461743)
      ·
        refine ⟨222518556090598861941692615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148345704060399241294461743 222518556090598861941692615)
        ·
          refine ⟨333777834135898292912538923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222518556090598861941692615 333777834135898292912538923)
          ·
            refine ⟨500666751203847439368808385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333777834135898292912538923 500666751203847439368808385)
            ·
              refine ⟨375500063402885579526606289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500666751203847439368808385 375500063402885579526606289)
              ·
                refine ⟨281625047552164184644954717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375500063402885579526606289 281625047552164184644954717)
                ·
                  refine ⟨105609392832061569241858019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281625047552164184644954717 105609392832061569241858019)
                  ·
                    refine ⟨158414089248092353862787029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105609392832061569241858019 158414089248092353862787029)
                    ·
                      refine ⟨3712830216752164543659071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158414089248092353862787029 3712830216752164543659071)
                      ·
                        rfl

theorem cell23_7230711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_7230711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230711 prefixEnd_7230711 := by exact prefixLift 7230711
  have htrace : WordTrace (prefixWord ++ tailWord_7230711) baseStart_7230711 baseEnd_7230711 := by
    simpa [prefixWord, tailWord_7230711, baseEnd_7230711] using wordTrace_append hprefix tailTrace_7230711
  have hstable : (prefixWord ++ tailWord_7230711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230711).length < 2 ^ (prefixWord ++ tailWord_7230711).sum := by decide
  have hdescent : baseEnd_7230711 < baseStart_7230711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230752 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_7230752 : Nat := 118140960795 + 7230752 * 2 ^ 59
def prefixEnd_7230752 : Nat := 4983230072969 + 3 ^ 40 * 7230752 * 2
def baseEnd_7230752 : Nat := 1237617089819666294415461

theorem tailTrace_7230752 : CollatzResearch.WordTrace tailWord_7230752 prefixEnd_7230752 1237617089819666294415461 := by
  unfold tailWord_7230752
  simp only [CollatzResearch.WordTrace]
  refine ⟨131863595750113946485087255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175818127666818595313449673 131863595750113946485087255)
  ·
    refine ⟨197795393625170919727630883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131863595750113946485087255 197795393625170919727630883)
    ·
      refine ⟨296693090437756379591446325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197795393625170919727630883 296693090437756379591446325)
      ·
        refine ⟨27814977228539660586698093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296693090437756379591446325 27814977228539660586698093)
        ·
          refine ⟨10430616460702372720011785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27814977228539660586698093 10430616460702372720011785)
          ·
            refine ⟨7822962345526779540008839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10430616460702372720011785 7822962345526779540008839)
            ·
              refine ⟨11734443518290169310013259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822962345526779540008839 11734443518290169310013259)
              ·
                refine ⟨17601665277435253965019889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734443518290169310013259 17601665277435253965019889)
                ·
                  refine ⟨13201248958076440473764917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601665277435253965019889 13201248958076440473764917)
                  ·
                    refine ⟨1237617089819666294415461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13201248958076440473764917 1237617089819666294415461)
                    ·
                      rfl

theorem cell23_7230752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_7230752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230752 prefixEnd_7230752 := by exact prefixLift 7230752
  have htrace : WordTrace (prefixWord ++ tailWord_7230752) baseStart_7230752 baseEnd_7230752 := by
    simpa [prefixWord, tailWord_7230752, baseEnd_7230752] using wordTrace_append hprefix tailTrace_7230752
  have hstable : (prefixWord ++ tailWord_7230752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230752).length < 2 ^ (prefixWord ++ tailWord_7230752).sum := by decide
  have hdescent : baseEnd_7230752 < baseStart_7230752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230755 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4]
def baseStart_7230755 : Nat := 118140960795 + 7230755 * 2 ^ 59
def prefixEnd_7230755 : Nat := 4983230072969 + 3 ^ 40 * 7230755 * 2
def baseEnd_7230755 : Nat := 3712852809900962371508869

theorem tailTrace_7230755 : CollatzResearch.WordTrace tailWord_7230755 prefixEnd_7230755 3712852809900962371508869 := by
  unfold tailWord_7230755
  simp only [CollatzResearch.WordTrace]
  refine ⟨263727300919217024482533719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175818200612811349655022479 263727300919217024482533719)
  ·
    refine ⟨395590951378825536723800579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263727300919217024482533719 395590951378825536723800579)
    ·
      refine ⟨593386427068238305085700869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395590951378825536723800579 593386427068238305085700869)
      ·
        refine ⟨111259955075294682203568913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593386427068238305085700869 111259955075294682203568913)
        ·
          refine ⟨83444966306471011652676685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111259955075294682203568913 83444966306471011652676685)
          ·
            refine ⟨31291862364926629369753757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83444966306471011652676685 31291862364926629369753757)
            ·
              refine ⟨11734448386847486013657659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31291862364926629369753757 11734448386847486013657659)
              ·
                refine ⟨17601672580271229020486489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734448386847486013657659 17601672580271229020486489)
                ·
                  refine ⟨13201254435203421765364867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601672580271229020486489 13201254435203421765364867)
                  ·
                    refine ⟨19801881652805132648047301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13201254435203421765364867 19801881652805132648047301)
                    ·
                      refine ⟨3712852809900962371508869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19801881652805132648047301 3712852809900962371508869)
                      ·
                        rfl

theorem cell23_7230755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_7230755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230755 prefixEnd_7230755 := by exact prefixLift 7230755
  have htrace : WordTrace (prefixWord ++ tailWord_7230755) baseStart_7230755 baseEnd_7230755 := by
    simpa [prefixWord, tailWord_7230755, baseEnd_7230755] using wordTrace_append hprefix tailTrace_7230755
  have hstable : (prefixWord ++ tailWord_7230755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230755).length < 2 ^ (prefixWord ++ tailWord_7230755).sum := by decide
  have hdescent : baseEnd_7230755 < baseStart_7230755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230772 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7230772 : Nat := 118140960795 + 7230772 * 2 ^ 59
def prefixEnd_7230772 : Nat := 4983230072969 + 3 ^ 40 * 7230772 * 2
def baseEnd_7230772 : Nat := 3712861539072088804996291

theorem tailTrace_7230772 : CollatzResearch.WordTrace tailWord_7230772 prefixEnd_7230772 3712861539072088804996291 := by
  unfold tailWord_7230772
  simp only [CollatzResearch.WordTrace]
  refine ⟨131863960480077718192951285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175818613973436957590601713 131863960480077718192951285)
  ·
    refine ⟨12362246295007286080589183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131863960480077718192951285 12362246295007286080589183)
    ·
      refine ⟨18543369442510929120883775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362246295007286080589183 18543369442510929120883775)
      ·
        refine ⟨27815054163766393681325663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18543369442510929120883775 27815054163766393681325663)
        ·
          refine ⟨41722581245649590521988495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815054163766393681325663 41722581245649590521988495)
          ·
            refine ⟨62583871868474385782982743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41722581245649590521988495 62583871868474385782982743)
            ·
              refine ⟨93875807802711578674474115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62583871868474385782982743 93875807802711578674474115)
              ·
                refine ⟨140813711704067368011711173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93875807802711578674474115 140813711704067368011711173)
                ·
                  refine ⟨26402570944512631502195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140813711704067368011711173 26402570944512631502195845)
                  ·
                    refine ⟨4950482052096118406661721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26402570944512631502195845 4950482052096118406661721)
                    ·
                      refine ⟨3712861539072088804996291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950482052096118406661721 3712861539072088804996291)
                      ·
                        rfl

theorem cell23_7230772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7230772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230772 prefixEnd_7230772 := by exact prefixLift 7230772
  have htrace : WordTrace (prefixWord ++ tailWord_7230772) baseStart_7230772 baseEnd_7230772 := by
    simpa [prefixWord, tailWord_7230772, baseEnd_7230772] using wordTrace_append hprefix tailTrace_7230772
  have hstable : (prefixWord ++ tailWord_7230772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230772).length < 2 ^ (prefixWord ++ tailWord_7230772).sum := by decide
  have hdescent : baseEnd_7230772 < baseStart_7230772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230778 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_7230778 : Nat := 118140960795 + 7230778 * 2 ^ 59
def prefixEnd_7230778 : Nat := 4983230072969 + 3 ^ 40 * 7230778 * 2
def baseEnd_7230778 : Nat := 412540513328446197946807

theorem tailTrace_7230778 : CollatzResearch.WordTrace tailWord_7230778 prefixEnd_7230778 412540513328446197946807 := by
  unfold tailWord_7230778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65932034949533424852655247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175818759865422466273747325 65932034949533424852655247)
  ·
    refine ⟨98898052424300137278982871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65932034949533424852655247 98898052424300137278982871)
    ·
      refine ⟨148347078636450205918474307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98898052424300137278982871 148347078636450205918474307)
      ·
        refine ⟨222520617954675308877711461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148347078636450205918474307 222520617954675308877711461)
        ·
          refine ⟨41722615866501620414570899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222520617954675308877711461 41722615866501620414570899)
          ·
            refine ⟨62583923799752430621856349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41722615866501620414570899 62583923799752430621856349)
            ·
              refine ⟨23468971424907161483196131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62583923799752430621856349 23468971424907161483196131)
              ·
                refine ⟨35203457137360742224794197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23468971424907161483196131 35203457137360742224794197)
                ·
                  refine ⟨412540513328446197946807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35203457137360742224794197 412540513328446197946807)
                  ·
                    rfl

theorem cell23_7230778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_7230778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230778 prefixEnd_7230778 := by exact prefixLift 7230778
  have htrace : WordTrace (prefixWord ++ tailWord_7230778) baseStart_7230778 baseEnd_7230778 := by
    simpa [prefixWord, tailWord_7230778, baseEnd_7230778] using wordTrace_append hprefix tailTrace_7230778
  have hstable : (prefixWord ++ tailWord_7230778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230778).length < 2 ^ (prefixWord ++ tailWord_7230778).sum := by decide
  have hdescent : baseEnd_7230778 < baseStart_7230778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230782 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7230782 : Nat := 118140960795 + 7230782 * 2 ^ 59
def prefixEnd_7230782 : Nat := 4983230072969 + 3 ^ 40 * 7230782 * 2
def baseEnd_7230782 : Nat := 1237622224626211255290415

theorem tailTrace_7230782 : CollatzResearch.WordTrace tailWord_7230782 prefixEnd_7230782 1237622224626211255290415 := by
  unfold tailWord_7230782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32966035711264901011720825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175818857126746138729177733 32966035711264901011720825)
  ·
    refine ⟨24724526783448675758790619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32966035711264901011720825 24724526783448675758790619)
    ·
      refine ⟨37086790175173013638185929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24724526783448675758790619 37086790175173013638185929)
      ·
        refine ⟨27815092631379760228639447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37086790175173013638185929 27815092631379760228639447)
        ·
          refine ⟨41722638947069640342959171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815092631379760228639447 41722638947069640342959171)
          ·
            refine ⟨62583958420604460514438757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41722638947069640342959171 62583958420604460514438757)
            ·
              refine ⟨11734492203863336346457267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62583958420604460514438757 11734492203863336346457267)
              ·
                refine ⟨17601738305795004519685901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734492203863336346457267 17601738305795004519685901)
                ·
                  refine ⟨6600651864673126694882213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17601738305795004519685901 6600651864673126694882213)
                  ·
                    refine ⟨1237622224626211255290415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600651864673126694882213 1237622224626211255290415)
                    ·
                      rfl

theorem cell23_7230782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7230782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230782 prefixEnd_7230782 := by exact prefixLift 7230782
  have htrace : WordTrace (prefixWord ++ tailWord_7230782) baseStart_7230782 baseEnd_7230782 := by
    simpa [prefixWord, tailWord_7230782, baseEnd_7230782] using wordTrace_append hprefix tailTrace_7230782
  have hstable : (prefixWord ++ tailWord_7230782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230782).length < 2 ^ (prefixWord ++ tailWord_7230782).sum := by decide
  have hdescent : baseEnd_7230782 < baseStart_7230782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230798 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7230798 : Nat := 118140960795 + 7230798 * 2 ^ 59
def prefixEnd_7230798 : Nat := 4983230072969 + 3 ^ 40 * 7230798 * 2
def baseEnd_7230798 : Nat := 3712874889569105703271171

theorem tailTrace_7230798 : CollatzResearch.WordTrace tailWord_7230798 prefixEnd_7230798 3712874889569105703271171 := by
  unfold tailWord_7230798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32966108657257655353293631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175819246172040828550899365 32966108657257655353293631)
  ·
    refine ⟨49449162985886483029940447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32966108657257655353293631 49449162985886483029940447)
    ·
      refine ⟨74173744478829724544910671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49449162985886483029940447 74173744478829724544910671)
      ·
        refine ⟨111260616718244586817366007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74173744478829724544910671 111260616718244586817366007)
        ·
          refine ⟨166890925077366880226049011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111260616718244586817366007 166890925077366880226049011)
          ·
            refine ⟨250336387616050320339073517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166890925077366880226049011 250336387616050320339073517)
            ·
              refine ⟨93876145356018870127152569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250336387616050320339073517 93876145356018870127152569)
              ·
                refine ⟨70407109017014152595364427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93876145356018870127152569 70407109017014152595364427)
                ·
                  refine ⟨105610663525521228893046641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70407109017014152595364427 105610663525521228893046641)
                  ·
                    refine ⟨79207997644140921669784981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105610663525521228893046641 79207997644140921669784981)
                    ·
                      refine ⟨3712874889569105703271171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79207997644140921669784981 3712874889569105703271171)
                      ·
                        rfl

theorem cell23_7230798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7230798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230798 prefixEnd_7230798 := by exact prefixLift 7230798
  have htrace : WordTrace (prefixWord ++ tailWord_7230798) baseStart_7230798 baseEnd_7230798 := by
    simpa [prefixWord, tailWord_7230798, baseEnd_7230798] using wordTrace_append hprefix tailTrace_7230798
  have hstable : (prefixWord ++ tailWord_7230798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230798).length < 2 ^ (prefixWord ++ tailWord_7230798).sum := by decide
  have hdescent : baseEnd_7230798 < baseStart_7230798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230832 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2]
def baseStart_7230832 : Nat := 118140960795 + 7230832 * 2 ^ 59
def prefixEnd_7230832 : Nat := 4983230072969 + 3 ^ 40 * 7230832 * 2
def baseEnd_7230832 : Nat := 3712892347911358570246015

theorem tailTrace_7230832 : CollatzResearch.WordTrace tailWord_7230832 prefixEnd_7230832 3712892347911358570246015 := by
  unfold tailWord_7230832
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865054669969033316543375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175820072893292044422057833 131865054669969033316543375)
  ·
    refine ⟨197797582004953549974815063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131865054669969033316543375 197797582004953549974815063)
    ·
      refine ⟨296696373007430324962222595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197797582004953549974815063 296696373007430324962222595)
      ·
        refine ⟨445044559511145487443333893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296696373007430324962222595 445044559511145487443333893)
        ·
          refine ⟨83445854908339778895625105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445044559511145487443333893 83445854908339778895625105)
          ·
            refine ⟨62584391181254834171718829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83445854908339778895625105 62584391181254834171718829)
            ·
              refine ⟨23469146692970562814394561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62584391181254834171718829 23469146692970562814394561)
              ·
                refine ⟨17601860019727922110795921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23469146692970562814394561 17601860019727922110795921)
                ·
                  refine ⟨13201395014795941583096941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601860019727922110795921 13201395014795941583096941)
                  ·
                    refine ⟨4950523130548478093661353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13201395014795941583096941 4950523130548478093661353)
                    ·
                      refine ⟨3712892347911358570246015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950523130548478093661353 3712892347911358570246015)
                      ·
                        rfl

theorem cell23_7230832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2].length) (baseStart_7230832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230832 prefixEnd_7230832 := by exact prefixLift 7230832
  have htrace : WordTrace (prefixWord ++ tailWord_7230832) baseStart_7230832 baseEnd_7230832 := by
    simpa [prefixWord, tailWord_7230832, baseEnd_7230832] using wordTrace_append hprefix tailTrace_7230832
  have hstable : (prefixWord ++ tailWord_7230832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230832).length < 2 ^ (prefixWord ++ tailWord_7230832).sum := by decide
  have hdescent : baseEnd_7230832 < baseStart_7230832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230845 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_7230845 : Nat := 118140960795 + 7230845 * 2 ^ 59
def prefixEnd_7230845 : Nat := 4983230072969 + 3 ^ 40 * 7230845 * 2
def baseEnd_7230845 : Nat := 3712899023159867019383455

theorem tailTrace_7230845 : CollatzResearch.WordTrace tailWord_7230845 prefixEnd_7230845 3712899023159867019383455 := by
  unfold tailWord_7230845
  simp only [CollatzResearch.WordTrace]
  refine ⟨263730583488890969853309989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175820388992593979902206659 263730583488890969853309989)
  ·
    refine ⟨49449484404167056847495623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263730583488890969853309989 49449484404167056847495623)
    ·
      refine ⟨74174226606250585271243435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49449484404167056847495623 74174226606250585271243435)
      ·
        refine ⟨111261339909375877906865153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74174226606250585271243435 111261339909375877906865153)
        ·
          refine ⟨83446004932031908430148865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111261339909375877906865153 83446004932031908430148865)
          ·
            refine ⟨62584503699023931322611649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83446004932031908430148865 62584503699023931322611649)
            ·
              refine ⟨46938377774267948491958737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62584503699023931322611649 46938377774267948491958737)
              ·
                refine ⟨35203783330700961368969053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46938377774267948491958737 35203783330700961368969053)
                ·
                  refine ⟨13201418749012860513363395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35203783330700961368969053 13201418749012860513363395)
                  ·
                    refine ⟨19802128123519290770045093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13201418749012860513363395 19802128123519290770045093)
                    ·
                      refine ⟨3712899023159867019383455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19802128123519290770045093 3712899023159867019383455)
                      ·
                        rfl

theorem cell23_7230845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_7230845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230845 prefixEnd_7230845 := by exact prefixLift 7230845
  have htrace : WordTrace (prefixWord ++ tailWord_7230845) baseStart_7230845 baseEnd_7230845 := by
    simpa [prefixWord, tailWord_7230845, baseEnd_7230845] using wordTrace_append hprefix tailTrace_7230845
  have hstable : (prefixWord ++ tailWord_7230845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230845).length < 2 ^ (prefixWord ++ tailWord_7230845).sum := by decide
  have hdescent : baseEnd_7230845 < baseStart_7230845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230865 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_7230865 : Nat := 118140960795 + 7230865 * 2 ^ 59
def prefixEnd_7230865 : Nat := 4983230072969 + 3 ^ 40 * 7230865 * 2
def baseEnd_7230865 : Nat := 3712909292772956941133363

theorem tailTrace_7230865 : CollatzResearch.WordTrace tailWord_7230865 prefixEnd_7230865 3712909292772956941133363 := by
  unfold tailWord_7230865
  simp only [CollatzResearch.WordTrace]
  refine ⟨263731312948818513269038049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175820875299212342179358699 263731312948818513269038049)
  ·
    refine ⟨197798484711613884951778537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263731312948818513269038049 197798484711613884951778537)
    ·
      refine ⟨148348863533710413713833903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197798484711613884951778537 148348863533710413713833903)
      ·
        refine ⟨222523295300565620570750855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148348863533710413713833903 222523295300565620570750855)
        ·
          refine ⟨333784942950848430856126283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222523295300565620570750855 333784942950848430856126283)
          ·
            refine ⟨500677414426272646284189425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333784942950848430856126283 500677414426272646284189425)
            ·
              refine ⟨375508060819704484713142069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500677414426272646284189425 375508060819704484713142069)
              ·
                refine ⟨35203880701847295441857069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375508060819704484713142069 35203880701847295441857069)
                ·
                  refine ⟨13201455263192735790696401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35203880701847295441857069 13201455263192735790696401)
                  ·
                    refine ⟨9901091447394551843022301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13201455263192735790696401 9901091447394551843022301)
                    ·
                      refine ⟨3712909292772956941133363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901091447394551843022301 3712909292772956941133363)
                      ·
                        rfl

theorem cell23_7230865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_7230865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230865 prefixEnd_7230865 := by exact prefixLift 7230865
  have htrace : WordTrace (prefixWord ++ tailWord_7230865) baseStart_7230865 baseEnd_7230865 := by
    simpa [prefixWord, tailWord_7230865, baseEnd_7230865] using wordTrace_append hprefix tailTrace_7230865
  have hstable : (prefixWord ++ tailWord_7230865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230865).length < 2 ^ (prefixWord ++ tailWord_7230865).sum := by decide
  have hdescent : baseEnd_7230865 < baseStart_7230865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230872 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_7230872 : Nat := 118140960795 + 7230872 * 2 ^ 59
def prefixEnd_7230872 : Nat := 4983230072969 + 3 ^ 40 * 7230872 * 2
def baseEnd_7230872 : Nat := 1237637629045846137915277

theorem tailTrace_7230872 : CollatzResearch.WordTrace tailWord_7230872 prefixEnd_7230872 1237637629045846137915277 := by
  unfold tailWord_7230872
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865784129896576732271435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175821045506528768976361913 131865784129896576732271435)
  ·
    refine ⟨197798676194844865098407153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131865784129896576732271435 197798676194844865098407153)
    ·
      refine ⟨148349007146133648823805365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197798676194844865098407153 148349007146133648823805365)
      ·
        refine ⟨13907719419950029577231753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148349007146133648823805365 13907719419950029577231753)
        ·
          refine ⟨10430789564962522182923815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13907719419950029577231753 10430789564962522182923815)
          ·
            refine ⟨15646184347443783274385723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430789564962522182923815 15646184347443783274385723)
            ·
              refine ⟨23469276521165674911578585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15646184347443783274385723 23469276521165674911578585)
              ·
                refine ⟨17601957390874256183683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23469276521165674911578585 17601957390874256183683939)
                ·
                  refine ⟨26402936086311384275525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17601957390874256183683939 26402936086311384275525909)
                  ·
                    refine ⟨1237637629045846137915277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26402936086311384275525909 1237637629045846137915277)
                    ·
                      rfl

theorem cell23_7230872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_7230872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230872 prefixEnd_7230872 := by exact prefixLift 7230872
  have htrace : WordTrace (prefixWord ++ tailWord_7230872) baseStart_7230872 baseEnd_7230872 := by
    simpa [prefixWord, tailWord_7230872, baseEnd_7230872] using wordTrace_append hprefix tailTrace_7230872
  have hstable : (prefixWord ++ tailWord_7230872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230872).length < 2 ^ (prefixWord ++ tailWord_7230872).sum := by decide
  have hdescent : baseEnd_7230872 < baseStart_7230872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230876 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7230876 : Nat := 118140960795 + 7230876 * 2 ^ 59
def prefixEnd_7230876 : Nat := 4983230072969 + 3 ^ 40 * 7230876 * 2
def baseEnd_7230876 : Nat := 1237638313686718799365271

theorem tailTrace_7230876 : CollatzResearch.WordTrace tailWord_7230876 prefixEnd_7230876 1237638313686718799365271 := by
  unfold tailWord_7230876
  simp only [CollatzResearch.WordTrace]
  refine ⟨131865857075889331073844241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175821142767852441431792321 131865857075889331073844241)
  ·
    refine ⟨98899392806916998305383181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131865857075889331073844241 98899392806916998305383181)
    ·
      refine ⟨37087272302593874364518693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98899392806916998305383181 37087272302593874364518693)
      ·
        refine ⟨6953863556736351443347255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37087272302593874364518693 6953863556736351443347255)
        ·
          refine ⟨10430795335104527165020883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953863556736351443347255 10430795335104527165020883)
          ·
            refine ⟨15646193002656790747531325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430795335104527165020883 15646193002656790747531325)
            ·
              refine ⟨5867322375996296530324247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15646193002656790747531325 5867322375996296530324247)
              ·
                refine ⟨8800983563994444795486371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867322375996296530324247 8800983563994444795486371)
                ·
                  refine ⟨13201475345991667193229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800983563994444795486371 13201475345991667193229557)
                  ·
                    refine ⟨1237638313686718799365271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13201475345991667193229557 1237638313686718799365271)
                    ·
                      rfl

theorem cell23_7230876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7230876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230876 prefixEnd_7230876 := by exact prefixLift 7230876
  have htrace : WordTrace (prefixWord ++ tailWord_7230876) baseStart_7230876 baseEnd_7230876 := by
    simpa [prefixWord, tailWord_7230876, baseEnd_7230876] using wordTrace_append hprefix tailTrace_7230876
  have hstable : (prefixWord ++ tailWord_7230876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230876).length < 2 ^ (prefixWord ++ tailWord_7230876).sum := by decide
  have hdescent : baseEnd_7230876 < baseStart_7230876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230879 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7230879 : Nat := 118140960795 + 7230879 * 2 ^ 59
def prefixEnd_7230879 : Nat := 4983230072969 + 3 ^ 40 * 7230879 * 2
def baseEnd_7230879 : Nat := 3712916481502119886358299

theorem tailTrace_7230879 : CollatzResearch.WordTrace tailWord_7230879 prefixEnd_7230879 3712916481502119886358299 := by
  unfold tailWord_7230879
  simp only [CollatzResearch.WordTrace]
  refine ⟨263731823570767793660047691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175821215713845195773365127 263731823570767793660047691)
  ·
    refine ⟨395597735356151690490071537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263731823570767793660047691 395597735356151690490071537)
    ·
      refine ⟨296698301517113767867553653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395597735356151690490071537 296698301517113767867553653)
      ·
        refine ⟨27815465767229415737583155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296698301517113767867553653 27815465767229415737583155)
        ·
          refine ⟨41723198650844123606374733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815465767229415737583155 41723198650844123606374733)
          ·
            refine ⟨15646199494066546352390525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41723198650844123606374733 15646199494066546352390525)
            ·
              refine ⟨5867324810274954882146447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15646199494066546352390525 5867324810274954882146447)
              ·
                refine ⟨8800987215412432323219671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867324810274954882146447 8800987215412432323219671)
                ·
                  refine ⟨13201480823118648484829507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800987215412432323219671 13201480823118648484829507)
                  ·
                    refine ⟨19802221234677972727244261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13201480823118648484829507 19802221234677972727244261)
                    ·
                      refine ⟨3712916481502119886358299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19802221234677972727244261 3712916481502119886358299)
                      ·
                        rfl

theorem cell23_7230879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7230879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230879 prefixEnd_7230879 := by exact prefixLift 7230879
  have htrace : WordTrace (prefixWord ++ tailWord_7230879) baseStart_7230879 baseEnd_7230879 := by
    simpa [prefixWord, tailWord_7230879, baseEnd_7230879] using wordTrace_append hprefix tailTrace_7230879
  have hstable : (prefixWord ++ tailWord_7230879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230879).length < 2 ^ (prefixWord ++ tailWord_7230879).sum := by decide
  have hdescent : baseEnd_7230879 < baseStart_7230879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230882 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7230882 : Nat := 118140960795 + 7230882 * 2 ^ 59
def prefixEnd_7230882 : Nat := 4983230072969 + 3 ^ 40 * 7230882 * 2
def baseEnd_7230882 : Nat := 3712918021944083374620785

theorem tailTrace_7230882 : CollatzResearch.WordTrace tailWord_7230882 prefixEnd_7230882 3712918021944083374620785 := by
  unfold tailWord_7230882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65932983247439231293101725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175821288659837950114937933 65932983247439231293101725)
  ·
    refine ⟨24724868717789711734913147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65932983247439231293101725 24724868717789711734913147)
    ·
      refine ⟨37087303076684567602369721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24724868717789711734913147 37087303076684567602369721)
      ·
        refine ⟨27815477307513425701777291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37087303076684567602369721 27815477307513425701777291)
        ·
          refine ⟨41723215961270138552665937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815477307513425701777291 41723215961270138552665937)
          ·
            refine ⟨31292411970952603914499453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41723215961270138552665937 31292411970952603914499453)
            ·
              refine ⟨11734654489107226467937295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31292411970952603914499453 11734654489107226467937295)
              ·
                refine ⟨17601981733660839701905943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734654489107226467937295 17601981733660839701905943)
                ·
                  refine ⟨26402972600491259552858915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17601981733660839701905943 26402972600491259552858915)
                  ·
                    refine ⟨39604458900736889329288373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26402972600491259552858915 39604458900736889329288373)
                    ·
                      refine ⟨3712918021944083374620785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39604458900736889329288373 3712918021944083374620785)
                      ·
                        rfl

theorem cell23_7230882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7230882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230882 prefixEnd_7230882 := by exact prefixLift 7230882
  have htrace : WordTrace (prefixWord ++ tailWord_7230882) baseStart_7230882 baseEnd_7230882 := by
    simpa [prefixWord, tailWord_7230882, baseEnd_7230882] using wordTrace_append hprefix tailTrace_7230882
  have hstable : (prefixWord ++ tailWord_7230882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230882).length < 2 ^ (prefixWord ++ tailWord_7230882).sum := by decide
  have hdescent : baseEnd_7230882 < baseStart_7230882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230945 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7230945 : Nat := 118140960795 + 7230945 * 2 ^ 59
def prefixEnd_7230945 : Nat := 4983230072969 + 3 ^ 40 * 7230945 * 2
def baseEnd_7230945 : Nat := 1237650123741772209377665

theorem tailTrace_7230945 : CollatzResearch.WordTrace tailWord_7230945 prefixEnd_7230945 1237650123741772209377665 := by
  unfold tailWord_7230945
  simp only [CollatzResearch.WordTrace]
  refine ⟨263734230788528686931950289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175822820525685791287966859 263734230788528686931950289)
  ·
    refine ⟨197800673091396515198962717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263734230788528686931950289 197800673091396515198962717)
    ·
      refine ⟨74175252409273693199611019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197800673091396515198962717 74175252409273693199611019)
      ·
        refine ⟨111262878613910539799416529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74175252409273693199611019 111262878613910539799416529)
        ·
          refine ⟨83447158960432904849562397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111262878613910539799416529 83447158960432904849562397)
          ·
            refine ⟨31292684610162339318585899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83447158960432904849562397 31292684610162339318585899)
            ·
              refine ⟨46939026915243508977878849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31292684610162339318585899 46939026915243508977878849)
              ·
                refine ⟨35204270186432631733409137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46939026915243508977878849 35204270186432631733409137)
                ·
                  refine ⟨26403202639824473800056853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35204270186432631733409137 26403202639824473800056853)
                  ·
                    refine ⟨1237650123741772209377665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26403202639824473800056853 1237650123741772209377665)
                    ·
                      rfl

theorem cell23_7230945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7230945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230945 prefixEnd_7230945 := by exact prefixLift 7230945
  have htrace : WordTrace (prefixWord ++ tailWord_7230945) baseStart_7230945 baseEnd_7230945 := by
    simpa [prefixWord, tailWord_7230945, baseEnd_7230945] using wordTrace_append hprefix tailTrace_7230945
  have hstable : (prefixWord ++ tailWord_7230945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230945).length < 2 ^ (prefixWord ++ tailWord_7230945).sum := by decide
  have hdescent : baseEnd_7230945 < baseStart_7230945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230955 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3]
def baseStart_7230955 : Nat := 118140960795 + 7230955 * 2 ^ 59
def prefixEnd_7230955 : Nat := 4983230072969 + 3 ^ 40 * 7230955 * 2
def baseEnd_7230955 : Nat := 3712955506031861589007949

theorem tailTrace_7230955 : CollatzResearch.WordTrace tailWord_7230955 prefixEnd_7230955 3712955506031861589007949 := by
  unfold tailWord_7230955
  simp only [CollatzResearch.WordTrace]
  refine ⟨263734595518492458639814319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175823063678994972426542879 263734595518492458639814319)
  ·
    refine ⟨395601893277738687959721479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263734595518492458639814319 395601893277738687959721479)
    ·
      refine ⟨593402839916608031939582219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395601893277738687959721479 593402839916608031939582219)
      ·
        refine ⟨890104259874912047909373329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593402839916608031939582219 890104259874912047909373329)
        ·
          refine ⟨667578194906184035932029997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890104259874912047909373329 667578194906184035932029997)
          ·
            refine ⟨250341823089819013474511249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667578194906184035932029997 250341823089819013474511249)
            ·
              refine ⟨187756367317364260105883437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250341823089819013474511249 187756367317364260105883437)
              ·
                refine ⟨70408637744011597539706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187756367317364260105883437 70408637744011597539706289)
                ·
                  refine ⟨52806478308008698154779717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70408637744011597539706289 52806478308008698154779717)
                  ·
                    refine ⟨9901214682751630904021197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52806478308008698154779717 9901214682751630904021197)
                    ·
                      refine ⟨3712955506031861589007949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901214682751630904021197 3712955506031861589007949)
                      ·
                        rfl

theorem cell23_7230955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].length) (baseStart_7230955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230955 prefixEnd_7230955 := by exact prefixLift 7230955
  have htrace : WordTrace (prefixWord ++ tailWord_7230955) baseStart_7230955 baseEnd_7230955 := by
    simpa [prefixWord, tailWord_7230955, baseEnd_7230955] using wordTrace_append hprefix tailTrace_7230955
  have hstable : (prefixWord ++ tailWord_7230955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230955).length < 2 ^ (prefixWord ++ tailWord_7230955).sum := by decide
  have hdescent : baseEnd_7230955 < baseStart_7230955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7230962 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_7230962 : Nat := 118140960795 + 7230962 * 2 ^ 59
def prefixEnd_7230962 : Nat := 4983230072969 + 3 ^ 40 * 7230962 * 2
def baseEnd_7230962 : Nat := 1237653033465481020540139

theorem tailTrace_7230962 : CollatzResearch.WordTrace tailWord_7230962 prefixEnd_7230962 1237653033465481020540139 := by
  unfold tailWord_7230962
  simp only [CollatzResearch.WordTrace]
  refine ⟨65933712707366774708829785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175823233886311399223546093 65933712707366774708829785)
  ·
    refine ⟨49450284530525081031622339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65933712707366774708829785 49450284530525081031622339)
    ·
      refine ⟨74175426795787621547433509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49450284530525081031622339 74175426795787621547433509)
      ·
        refine ⟨13907892524210179040143783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74175426795787621547433509 13907892524210179040143783)
        ·
          refine ⟨20861838786315268560215675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13907892524210179040143783 20861838786315268560215675)
          ·
            refine ⟨31292758179472902840323513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20861838786315268560215675 31292758179472902840323513)
            ·
              refine ⟨23469568634604677130242635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31292758179472902840323513 23469568634604677130242635)
              ·
                refine ⟨35204352951907015695363953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23469568634604677130242635 35204352951907015695363953)
                ·
                  refine ⟨26403264713930261771522965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35204352951907015695363953 26403264713930261771522965)
                  ·
                    refine ⟨1237653033465481020540139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26403264713930261771522965 1237653033465481020540139)
                    ·
                      rfl

theorem cell23_7230962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_7230962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7230962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7230962 prefixEnd_7230962 := by exact prefixLift 7230962
  have htrace : WordTrace (prefixWord ++ tailWord_7230962) baseStart_7230962 baseEnd_7230962 := by
    simpa [prefixWord, tailWord_7230962, baseEnd_7230962] using wordTrace_append hprefix tailTrace_7230962
  have hstable : (prefixWord ++ tailWord_7230962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7230962).length < 2 ^ (prefixWord ++ tailWord_7230962).sum := by decide
  have hdescent : baseEnd_7230962 < baseStart_7230962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7230962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231055 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_7231055 : Nat := 118140960795 + 7231055 * 2 ^ 59
def prefixEnd_7231055 : Nat := 4983230072969 + 3 ^ 40 * 7231055 * 2
def baseEnd_7231055 : Nat := 3713006854097311197757489

theorem tailTrace_7231055 : CollatzResearch.WordTrace tailWord_7231055 prefixEnd_7231055 3713006854097311197757489 := by
  unfold tailWord_7231055
  simp only [CollatzResearch.WordTrace]
  refine ⟨263738242818130175718454619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175825495212086783812303079 263738242818130175718454619)
  ·
    refine ⟨395607364227195263577681929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263738242818130175718454619 395607364227195263577681929)
    ·
      refine ⟨296705523170396447683261447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395607364227195263577681929 296705523170396447683261447)
      ·
        refine ⟨445058284755594671524892171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296705523170396447683261447 445058284755594671524892171)
        ·
          refine ⟨667587427133392007287338257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445058284755594671524892171 667587427133392007287338257)
          ·
            refine ⟨500690570350044005465503693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667587427133392007287338257 500690570350044005465503693)
            ·
              refine ⟨187758963881266502049563885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500690570350044005465503693 187758963881266502049563885)
              ·
                refine ⟨70409611455474938268586457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187758963881266502049563885 70409611455474938268586457)
                ·
                  refine ⟨52807208591606203701439843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70409611455474938268586457 52807208591606203701439843)
                  ·
                    refine ⟨79210812887409305552159765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52807208591606203701439843 79210812887409305552159765)
                    ·
                      refine ⟨3713006854097311197757489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79210812887409305552159765 3713006854097311197757489)
                      ·
                        rfl

theorem cell23_7231055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_7231055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231055 prefixEnd_7231055 := by exact prefixLift 7231055
  have htrace : WordTrace (prefixWord ++ tailWord_7231055) baseStart_7231055 baseEnd_7231055 := by
    simpa [prefixWord, tailWord_7231055, baseEnd_7231055] using wordTrace_append hprefix tailTrace_7231055
  have hstable : (prefixWord ++ tailWord_7231055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231055).length < 2 ^ (prefixWord ++ tailWord_7231055).sum := by decide
  have hdescent : baseEnd_7231055 < baseStart_7231055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231065 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 8]
def baseStart_7231065 : Nat := 118140960795 + 7231065 * 2 ^ 59
def prefixEnd_7231065 : Nat := 4983230072969 + 3 ^ 40 * 7231065 * 2
def baseEnd_7231065 : Nat := 412556887655984017625827

theorem tailTrace_7231065 : CollatzResearch.WordTrace tailWord_7231065 prefixEnd_7231065 412556887655984017625827 := by
  unfold tailWord_7231065
  simp only [CollatzResearch.WordTrace]
  refine ⟨263738607548093947426318649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175825738365395964950879099 263738607548093947426318649)
  ·
    refine ⟨197803955661070460569738987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263738607548093947426318649 197803955661070460569738987)
    ·
      refine ⟨296705933491605690854608481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197803955661070460569738987 296705933491605690854608481)
      ·
        refine ⟨222529450118704268140956361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296705933491605690854608481 222529450118704268140956361)
        ·
          refine ⟨166897087589028201105717271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222529450118704268140956361 166897087589028201105717271)
          ·
            refine ⟨250345631383542301658575907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166897087589028201105717271 250345631383542301658575907)
            ·
              refine ⟨375518447075313452487863861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250345631383542301658575907 375518447075313452487863861)
              ·
                refine ⟨35204854413310636170737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375518447075313452487863861 35204854413310636170737237)
                ·
                  refine ⟨412556887655984017625827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35204854413310636170737237 412556887655984017625827)
                  ·
                    rfl

theorem cell23_7231065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_7231065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231065 prefixEnd_7231065 := by exact prefixLift 7231065
  have htrace : WordTrace (prefixWord ++ tailWord_7231065) baseStart_7231065 baseEnd_7231065 := by
    simpa [prefixWord, tailWord_7231065, baseEnd_7231065] using wordTrace_append hprefix tailTrace_7231065
  have hstable : (prefixWord ++ tailWord_7231065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231065).length < 2 ^ (prefixWord ++ tailWord_7231065).sum := by decide
  have hdescent : baseEnd_7231065 < baseStart_7231065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231086 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7231086 : Nat := 118140960795 + 7231086 * 2 ^ 59
def prefixEnd_7231086 : Nat := 4983230072969 + 3 ^ 40 * 7231086 * 2
def baseEnd_7231086 : Nat := 1237674257332533525489949

theorem tailTrace_7231086 : CollatzResearch.WordTrace tailWord_7231086 prefixEnd_7231086 1237674257332533525489949 := by
  unfold tailWord_7231086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967421685127233501604139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175826248987345245341888741 32967421685127233501604139)
  ·
    refine ⟨49451132527690850252406209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32967421685127233501604139 49451132527690850252406209)
    ·
      refine ⟨37088349395768137689304657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49451132527690850252406209 37088349395768137689304657)
      ·
        refine ⟨27816262046826103266978493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37088349395768137689304657 27816262046826103266978493)
        ·
          refine ⟨10431098267559788725116935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27816262046826103266978493 10431098267559788725116935)
          ·
            refine ⟨15646647401339683087675403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431098267559788725116935 15646647401339683087675403)
            ·
              refine ⟨23469971102009524631513105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15646647401339683087675403 23469971102009524631513105)
              ·
                refine ⟨17602478326507143473634829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23469971102009524631513105 17602478326507143473634829)
                ·
                  refine ⟨6600929372440178802613061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17602478326507143473634829 6600929372440178802613061)
                  ·
                    refine ⟨1237674257332533525489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600929372440178802613061 1237674257332533525489949)
                    ·
                      rfl

theorem cell23_7231086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7231086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231086 prefixEnd_7231086 := by exact prefixLift 7231086
  have htrace : WordTrace (prefixWord ++ tailWord_7231086) baseStart_7231086 baseEnd_7231086 := by
    simpa [prefixWord, tailWord_7231086, baseEnd_7231086] using wordTrace_append hprefix tailTrace_7231086
  have hstable : (prefixWord ++ tailWord_7231086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231086).length < 2 ^ (prefixWord ++ tailWord_7231086).sum := by decide
  have hdescent : baseEnd_7231086 < baseStart_7231086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231109 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_7231109 : Nat := 118140960795 + 7231109 * 2 ^ 59
def prefixEnd_7231109 : Nat := 4983230072969 + 3 ^ 40 * 7231109 * 2
def baseEnd_7231109 : Nat := 3713034582052653986482241

theorem tailTrace_7231109 : CollatzResearch.WordTrace tailWord_7231109 prefixEnd_7231109 3713034582052653986482241 := by
  unfold tailWord_7231109
  simp only [CollatzResearch.WordTrace]
  refine ⟨263740212359934542940920381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175826808239956361960613587 263740212359934542940920381)
  ·
    refine ⟨98902579634975453602845143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263740212359934542940920381 98902579634975453602845143)
    ·
      refine ⟨148353869452463180404267715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98902579634975453602845143 148353869452463180404267715)
      ·
        refine ⟨222530804178694770606401573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148353869452463180404267715 222530804178694770606401573)
        ·
          refine ⟨41724525783505269488700295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222530804178694770606401573 41724525783505269488700295)
          ·
            refine ⟨62586788675257904233050443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41724525783505269488700295 62586788675257904233050443)
            ·
              refine ⟨93880183012886856349575665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62586788675257904233050443 93880183012886856349575665)
              ·
                refine ⟨70410137259665142262181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93880183012886856349575665 70410137259665142262181749)
                ·
                  refine ⟨6600950368093607087079539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70410137259665142262181749 6600950368093607087079539)
                  ·
                    refine ⟨9901425552140410630619309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6600950368093607087079539 9901425552140410630619309)
                    ·
                      refine ⟨3713034582052653986482241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901425552140410630619309 3713034582052653986482241)
                      ·
                        rfl

theorem cell23_7231109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_7231109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231109 prefixEnd_7231109 := by exact prefixLift 7231109
  have htrace : WordTrace (prefixWord ++ tailWord_7231109) baseStart_7231109 baseEnd_7231109 := by
    simpa [prefixWord, tailWord_7231109, baseEnd_7231109] using wordTrace_append hprefix tailTrace_7231109
  have hstable : (prefixWord ++ tailWord_7231109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231109).length < 2 ^ (prefixWord ++ tailWord_7231109).sum := by decide
  have hdescent : baseEnd_7231109 < baseStart_7231109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231159 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 4, 4]
def baseStart_7231159 : Nat := 118140960795 + 7231159 * 2 ^ 59
def prefixEnd_7231159 : Nat := 4983230072969 + 3 ^ 40 * 7231159 * 2
def baseEnd_7231159 : Nat := 1237686752028459596952337

theorem tailTrace_7231159 : CollatzResearch.WordTrace tailWord_7231159 prefixEnd_7231159 1237686752028459596952337 := by
  unfold tailWord_7231159
  simp only [CollatzResearch.WordTrace]
  refine ⟨263742036009753401480240531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175828024006502267653493687 263742036009753401480240531)
  ·
    refine ⟨395613054014630102220360797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263742036009753401480240531 395613054014630102220360797)
    ·
      refine ⟨148354895255486288332635299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395613054014630102220360797 148354895255486288332635299)
      ·
        refine ⟨222532342883229432498952949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148354895255486288332635299 222532342883229432498952949)
        ·
          refine ⟨20862407145302759296776839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222532342883229432498952949 20862407145302759296776839)
          ·
            refine ⟨31293610717954138945165259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20862407145302759296776839 31293610717954138945165259)
            ·
              refine ⟨46940416076931208417747889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31293610717954138945165259 46940416076931208417747889)
              ·
                refine ⟨35205312057698406313310917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46940416076931208417747889 35205312057698406313310917)
                ·
                  refine ⟨6600996010818451183745797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35205312057698406313310917 6600996010818451183745797)
                  ·
                    refine ⟨1237686752028459596952337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6600996010818451183745797 1237686752028459596952337)
                    ·
                      rfl

theorem cell23_7231159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_7231159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231159 prefixEnd_7231159 := by exact prefixLift 7231159
  have htrace : WordTrace (prefixWord ++ tailWord_7231159) baseStart_7231159 baseEnd_7231159 := by
    simpa [prefixWord, tailWord_7231159, baseEnd_7231159] using wordTrace_append hprefix tailTrace_7231159
  have hstable : (prefixWord ++ tailWord_7231159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231159).length < 2 ^ (prefixWord ++ tailWord_7231159).sum := by decide
  have hdescent : baseEnd_7231159 < baseStart_7231159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231166 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_7231166 : Nat := 118140960795 + 7231166 * 2 ^ 59
def prefixEnd_7231166 : Nat := 4983230072969 + 3 ^ 40 * 7231166 * 2
def baseEnd_7231166 : Nat := 3713063850449960263469479

theorem tailTrace_7231166 : CollatzResearch.WordTrace tailWord_7231166 prefixEnd_7231166 3713063850449960263469479 := by
  unfold tailWord_7231166
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967786415091005209468169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175828194213818694450496901 32967786415091005209468169)
  ·
    refine ⟨24725839811318253907101127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32967786415091005209468169 24725839811318253907101127)
    ·
      refine ⟨37088759716977380860651691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24725839811318253907101127 37088759716977380860651691)
      ·
        refine ⟨55633139575466071290977537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37088759716977380860651691 55633139575466071290977537)
        ·
          refine ⟨41724854681599553468233153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55633139575466071290977537 41724854681599553468233153)
          ·
            refine ⟨31293641011199665101174865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41724854681599553468233153 31293641011199665101174865)
            ·
              refine ⟨23470230758399748825881149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31293641011199665101174865 23470230758399748825881149)
              ·
                refine ⟨8801336534399905809705431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23470230758399748825881149 8801336534399905809705431)
                ·
                  refine ⟨13202004801599858714558147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8801336534399905809705431 13202004801599858714558147)
                  ·
                    refine ⟨19803007202399788071837221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13202004801599858714558147 19803007202399788071837221)
                    ·
                      refine ⟨3713063850449960263469479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19803007202399788071837221 3713063850449960263469479)
                      ·
                        rfl

theorem cell23_7231166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_7231166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231166 prefixEnd_7231166 := by exact prefixLift 7231166
  have htrace : WordTrace (prefixWord ++ tailWord_7231166) baseStart_7231166 baseEnd_7231166 := by
    simpa [prefixWord, tailWord_7231166, baseEnd_7231166] using wordTrace_append hprefix tailTrace_7231166
  have hstable : (prefixWord ++ tailWord_7231166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231166).length < 2 ^ (prefixWord ++ tailWord_7231166).sum := by decide
  have hdescent : baseEnd_7231166 < baseStart_7231166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231183 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 1, 2, 2]
def baseStart_7231183 : Nat := 118140960795 + 7231183 * 2 ^ 59
def prefixEnd_7231183 : Nat := 4983230072969 + 3 ^ 40 * 7231183 * 2
def baseEnd_7231183 : Nat := 3713072579621086696956901

theorem tailTrace_7231183 : CollatzResearch.WordTrace tailWord_7231183 prefixEnd_7231183 3713072579621086696956901 := by
  unfold tailWord_7231183
  simp only [CollatzResearch.WordTrace]
  refine ⟨263742911361666453579114203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175828607574444302386076135 263742911361666453579114203)
  ·
    refine ⟨395614367042499680368671305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263742911361666453579114203 395614367042499680368671305)
    ·
      refine ⟨296710775281874760276503479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395614367042499680368671305 296710775281874760276503479)
      ·
        refine ⟨445066162922812140414755219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296710775281874760276503479 445066162922812140414755219)
        ·
          refine ⟨667599244384218210622132829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445066162922812140414755219 667599244384218210622132829)
          ·
            refine ⟨250349716644081828983299811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667599244384218210622132829 250349716644081828983299811)
            ·
              refine ⟨375524574966122743474949717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250349716644081828983299811 375524574966122743474949717)
              ·
                refine ⟨4400678612884250900097067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 375524574966122743474949717 4400678612884250900097067)
                ·
                  refine ⟨6601017919326376350145601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400678612884250900097067 6601017919326376350145601)
                  ·
                    refine ⟨4950763439494782262609201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601017919326376350145601 4950763439494782262609201)
                    ·
                      refine ⟨3713072579621086696956901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950763439494782262609201 3713072579621086696956901)
                      ·
                        rfl

theorem cell23_7231183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 2, 2].length) (baseStart_7231183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231183 prefixEnd_7231183 := by exact prefixLift 7231183
  have htrace : WordTrace (prefixWord ++ tailWord_7231183) baseStart_7231183 baseEnd_7231183 := by
    simpa [prefixWord, tailWord_7231183, baseEnd_7231183] using wordTrace_append hprefix tailTrace_7231183
  have hstable : (prefixWord ++ tailWord_7231183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231183).length < 2 ^ (prefixWord ++ tailWord_7231183).sum := by decide
  have hdescent : baseEnd_7231183 < baseStart_7231183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231192 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7231192 : Nat := 118140960795 + 7231192 * 2 ^ 59
def prefixEnd_7231192 : Nat := 4983230072969 + 3 ^ 40 * 7231192 * 2
def baseEnd_7231192 : Nat := 3713077200946977161744359

theorem tailTrace_7231192 : CollatzResearch.WordTrace tailWord_7231192 prefixEnd_7231192 3713077200946977161744359 := by
  unfold tailWord_7231192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131871619809316924058095915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175828826412422565410794553 131871619809316924058095915)
  ·
    refine ⟨197807429713975386087143873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131871619809316924058095915 197807429713975386087143873)
    ·
      refine ⟨148355572285481539565357905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197807429713975386087143873 148355572285481539565357905)
      ·
        refine ⟨111266679214111154674018429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148355572285481539565357905 111266679214111154674018429)
        ·
          refine ⟨41725004705291683002756911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111266679214111154674018429 41725004705291683002756911)
          ·
            refine ⟨62587507057937524504135367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41725004705291683002756911 62587507057937524504135367)
            ·
              refine ⟨93881260586906286756203051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62587507057937524504135367 93881260586906286756203051)
              ·
                refine ⟨140821890880359430134304577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93881260586906286756203051 140821890880359430134304577)
                ·
                  refine ⟨105616418160269572600728433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140821890880359430134304577 105616418160269572600728433)
                  ·
                    refine ⟨79212313620202179450546325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105616418160269572600728433 79212313620202179450546325)
                    ·
                      refine ⟨3713077200946977161744359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79212313620202179450546325 3713077200946977161744359)
                      ·
                        rfl

theorem cell23_7231192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7231192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231192 prefixEnd_7231192 := by exact prefixLift 7231192
  have htrace : WordTrace (prefixWord ++ tailWord_7231192) baseStart_7231192 baseEnd_7231192 := by
    simpa [prefixWord, tailWord_7231192, baseEnd_7231192] using wordTrace_append hprefix tailTrace_7231192
  have hstable : (prefixWord ++ tailWord_7231192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231192).length < 2 ^ (prefixWord ++ tailWord_7231192).sum := by decide
  have hdescent : baseEnd_7231192 < baseStart_7231192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231193 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_7231193 : Nat := 118140960795 + 7231193 * 2 ^ 59
def prefixEnd_7231193 : Nat := 4983230072969 + 3 ^ 40 * 7231193 * 2
def baseEnd_7231193 : Nat := 1237692571475877219277285

theorem tailTrace_7231193 : CollatzResearch.WordTrace tailWord_7231193 prefixEnd_7231193 1237692571475877219277285 := by
  unfold tailWord_7231193
  simp only [CollatzResearch.WordTrace]
  refine ⟨263743276091630225286978233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175828850727753483524652155 263743276091630225286978233)
  ·
    refine ⟨197807457068722668965233675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263743276091630225286978233 197807457068722668965233675)
    ·
      refine ⟨296711185603084003447850513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197807457068722668965233675 296711185603084003447850513)
      ·
        refine ⟨222533389202313002585887885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296711185603084003447850513 222533389202313002585887885)
        ·
          refine ⟨83450020950867375969707957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222533389202313002585887885 83450020950867375969707957)
          ·
            refine ⟨7823439464143816497160121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83450020950867375969707957 7823439464143816497160121)
            ·
              refine ⟨5867579598107862372870091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7823439464143816497160121 5867579598107862372870091)
              ·
                refine ⟨8801369397161793559305137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867579598107862372870091 8801369397161793559305137)
                ·
                  refine ⟨6601027047871345169478853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801369397161793559305137 6601027047871345169478853)
                  ·
                    refine ⟨1237692571475877219277285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601027047871345169478853 1237692571475877219277285)
                    ·
                      rfl

theorem cell23_7231193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_7231193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231193 prefixEnd_7231193 := by exact prefixLift 7231193
  have htrace : WordTrace (prefixWord ++ tailWord_7231193) baseStart_7231193 baseEnd_7231193 := by
    simpa [prefixWord, tailWord_7231193, baseEnd_7231193] using wordTrace_append hprefix tailTrace_7231193
  have hstable : (prefixWord ++ tailWord_7231193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231193).length < 2 ^ (prefixWord ++ tailWord_7231193).sum := by decide
  have hdescent : baseEnd_7231193 < baseStart_7231193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231199 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_7231199 : Nat := 118140960795 + 7231199 * 2 ^ 59
def prefixEnd_7231199 : Nat := 4983230072969 + 3 ^ 40 * 7231199 * 2
def baseEnd_7231199 : Nat := 3713080795311558634356827

theorem tailTrace_7231199 : CollatzResearch.WordTrace tailWord_7231199 prefixEnd_7231199 3713080795311558634356827 := by
  unfold tailWord_7231199
  simp only [CollatzResearch.WordTrace]
  refine ⟨263743494929608488311696651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175828996619738992207797767 263743494929608488311696651)
  ·
    refine ⟨395615242394412732467544977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263743494929608488311696651 395615242394412732467544977)
    ·
      refine ⟨296711431795809549350658733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395615242394412732467544977 296711431795809549350658733)
      ·
        refine ⟨111266786923428581006497025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296711431795809549350658733 111266786923428581006497025)
        ·
          refine ⟨83450090192571435754872769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111266786923428581006497025 83450090192571435754872769)
          ·
            refine ⟨62587567644428576816154577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83450090192571435754872769 62587567644428576816154577)
            ·
              refine ⟨46940675733321432612115933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62587567644428576816154577 46940675733321432612115933)
              ·
                refine ⟨17602753399995537229543475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46940675733321432612115933 17602753399995537229543475)
                ·
                  refine ⟨26404130099993305844315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17602753399995537229543475 26404130099993305844315213)
                  ·
                    refine ⟨9901548787497489691618205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26404130099993305844315213 9901548787497489691618205)
                    ·
                      refine ⟨3713080795311558634356827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901548787497489691618205 3713080795311558634356827)
                      ·
                        rfl

theorem cell23_7231199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_7231199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231199 prefixEnd_7231199 := by exact prefixLift 7231199
  have htrace : WordTrace (prefixWord ++ tailWord_7231199) baseStart_7231199 baseEnd_7231199 := by
    simpa [prefixWord, tailWord_7231199, baseEnd_7231199] using wordTrace_append hprefix tailTrace_7231199
  have hstable : (prefixWord ++ tailWord_7231199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231199).length < 2 ^ (prefixWord ++ tailWord_7231199).sum := by decide
  have hdescent : baseEnd_7231199 < baseStart_7231199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231212 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7231212 : Nat := 118140960795 + 7231212 * 2 ^ 59
def prefixEnd_7231212 : Nat := 4983230072969 + 3 ^ 40 * 7231212 * 2
def baseEnd_7231212 : Nat := 3713087470560067083494267

theorem tailTrace_7231212 : CollatzResearch.WordTrace tailWord_7231212 prefixEnd_7231212 3713087470560067083494267 := by
  unfold tailWord_7231212
  simp only [CollatzResearch.WordTrace]
  refine ⟨131871984539280695765959945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175829312719040927687946593 131871984539280695765959945)
  ·
    refine ⟨98903988404460521824469959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131871984539280695765959945 98903988404460521824469959)
    ·
      refine ⟨148355982606690782736704939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98903988404460521824469959 148355982606690782736704939)
      ·
        refine ⟨222533973910036174105057409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148355982606690782736704939 222533973910036174105057409)
        ·
          refine ⟨166900480432527130578793057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222533973910036174105057409 166900480432527130578793057)
          ·
            refine ⟨125175360324395347934094793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166900480432527130578793057 125175360324395347934094793)
            ·
              refine ⟨93881520243296510950571095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125175360324395347934094793 93881520243296510950571095)
              ·
                refine ⟨140822280364944766425856643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93881520243296510950571095 140822280364944766425856643)
                ·
                  refine ⟨211233420547417149638784965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140822280364944766425856643 211233420547417149638784965)
                  ·
                    refine ⟨39606266352640715557272181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211233420547417149638784965 39606266352640715557272181)
                    ·
                      refine ⟨3713087470560067083494267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39606266352640715557272181 3713087470560067083494267)
                      ·
                        rfl

theorem cell23_7231212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7231212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231212 prefixEnd_7231212 := by exact prefixLift 7231212
  have htrace : WordTrace (prefixWord ++ tailWord_7231212) baseStart_7231212 baseEnd_7231212 := by
    simpa [prefixWord, tailWord_7231212, baseEnd_7231212] using wordTrace_append hprefix tailTrace_7231212
  have hstable : (prefixWord ++ tailWord_7231212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231212).length < 2 ^ (prefixWord ++ tailWord_7231212).sum := by decide
  have hdescent : baseEnd_7231212 < baseStart_7231212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231220 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7231220 : Nat := 118140960795 + 7231220 * 2 ^ 59
def prefixEnd_7231220 : Nat := 4983230072969 + 3 ^ 40 * 7231220 * 2
def baseEnd_7231220 : Nat := 3713091578405303052194231

theorem tailTrace_7231220 : CollatzResearch.WordTrace tailWord_7231220 prefixEnd_7231220 3713091578405303052194231 := by
  unfold tailWord_7231220
  simp only [CollatzResearch.WordTrace]
  refine ⟨131872130431266204449105557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175829507241688272598807409 131872130431266204449105557)
  ·
    refine ⟨6181506113965603333551823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131872130431266204449105557 6181506113965603333551823)
    ·
      refine ⟨9272259170948405000327735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181506113965603333551823 9272259170948405000327735)
      ·
        refine ⟨13908388756422607500491603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272259170948405000327735 13908388756422607500491603)
        ·
          refine ⟨20862583134633911250737405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908388756422607500491603 20862583134633911250737405)
          ·
            refine ⟨7823468675487716719026527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20862583134633911250737405 7823468675487716719026527)
            ·
              refine ⟨11735203013231575078539791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823468675487716719026527 11735203013231575078539791)
              ·
                refine ⟨17602804519847362617809687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735203013231575078539791 17602804519847362617809687)
                ·
                  refine ⟨26404206779771043926714531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17602804519847362617809687 26404206779771043926714531)
                  ·
                    refine ⟨39606310169656565890071797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26404206779771043926714531 39606310169656565890071797)
                    ·
                      refine ⟨3713091578405303052194231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39606310169656565890071797 3713091578405303052194231)
                      ·
                        rfl

theorem cell23_7231220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7231220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231220 prefixEnd_7231220 := by exact prefixLift 7231220
  have htrace : WordTrace (prefixWord ++ tailWord_7231220) baseStart_7231220 baseEnd_7231220 := by
    simpa [prefixWord, tailWord_7231220, baseEnd_7231220] using wordTrace_append hprefix tailTrace_7231220
  have hstable : (prefixWord ++ tailWord_7231220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231220).length < 2 ^ (prefixWord ++ tailWord_7231220).sum := by decide
  have hdescent : baseEnd_7231220 < baseStart_7231220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231232 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_7231232 : Nat := 118140960795 + 7231232 * 2 ^ 59
def prefixEnd_7231232 : Nat := 4983230072969 + 3 ^ 40 * 7231232 * 2
def baseEnd_7231232 : Nat := 1237699246724385668414725

theorem tailTrace_7231232 : CollatzResearch.WordTrace tailWord_7231232 prefixEnd_7231232 1237699246724385668414725 := by
  unfold tailWord_7231232
  simp only [CollatzResearch.WordTrace]
  refine ⟨131872349269244467473823975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175829799025659289965098633 131872349269244467473823975)
  ·
    refine ⟨197808523903866701210735963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131872349269244467473823975 197808523903866701210735963)
    ·
      refine ⟨296712785855800051816103945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197808523903866701210735963 296712785855800051816103945)
      ·
        refine ⟨222534589391850038862077959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296712785855800051816103945 222534589391850038862077959)
        ·
          refine ⟨333801884087775058293116939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222534589391850038862077959 333801884087775058293116939)
          ·
            refine ⟨500702826131662587439675409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333801884087775058293116939 500702826131662587439675409)
            ·
              refine ⟨375527119598746940579756557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500702826131662587439675409 375527119598746940579756557)
              ·
                refine ⟨140822669849530102717408709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375527119598746940579756557 140822669849530102717408709)
                ·
                  refine ⟨26404250596786894259514133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140822669849530102717408709 26404250596786894259514133)
                  ·
                    refine ⟨1237699246724385668414725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26404250596786894259514133 1237699246724385668414725)
                    ·
                      rfl

theorem cell23_7231232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_7231232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231232 prefixEnd_7231232 := by exact prefixLift 7231232
  have htrace : WordTrace (prefixWord ++ tailWord_7231232) baseStart_7231232 baseEnd_7231232 := by
    simpa [prefixWord, tailWord_7231232, baseEnd_7231232] using wordTrace_append hprefix tailTrace_7231232
  have hstable : (prefixWord ++ tailWord_7231232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231232).length < 2 ^ (prefixWord ++ tailWord_7231232).sum := by decide
  have hdescent : baseEnd_7231232 < baseStart_7231232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231250 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7231250 : Nat := 118140960795 + 7231250 * 2 ^ 59
def prefixEnd_7231250 : Nat := 4983230072969 + 3 ^ 40 * 7231250 * 2
def baseEnd_7231250 : Nat := 3713106982824937934819093

theorem tailTrace_7231250 : CollatzResearch.WordTrace tailWord_7231250 prefixEnd_7231250 3713106982824937934819093 := by
  unfold tailWord_7231250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65936338763105931005450801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175830236701615816014535469 65936338763105931005450801)
  ·
    refine ⟨49452254072329448254088101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65936338763105931005450801 49452254072329448254088101)
    ·
      refine ⟨9272297638561771547641519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49452254072329448254088101 9272297638561771547641519)
      ·
        refine ⟨13908446457842657321462279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272297638561771547641519 13908446457842657321462279)
        ·
          refine ⟨20862669686763985982193419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908446457842657321462279 20862669686763985982193419)
          ·
            refine ⟨31294004530145978973290129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20862669686763985982193419 31294004530145978973290129)
            ·
              refine ⟨23470503397609484229967597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31294004530145978973290129 23470503397609484229967597)
              ·
                refine ⟨8801438774103556586237849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23470503397609484229967597 8801438774103556586237849)
                ·
                  refine ⟨6601079080577667439678387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801438774103556586237849 6601079080577667439678387)
                  ·
                    refine ⟨9901618620866501159517581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6601079080577667439678387 9901618620866501159517581)
                    ·
                      refine ⟨3713106982824937934819093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901618620866501159517581 3713106982824937934819093)
                      ·
                        rfl

theorem cell23_7231250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7231250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231250 prefixEnd_7231250 := by exact prefixLift 7231250
  have htrace : WordTrace (prefixWord ++ tailWord_7231250) baseStart_7231250 baseEnd_7231250 := by
    simpa [prefixWord, tailWord_7231250, baseEnd_7231250] using wordTrace_append hprefix tailTrace_7231250
  have hstable : (prefixWord ++ tailWord_7231250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231250).length < 2 ^ (prefixWord ++ tailWord_7231250).sum := by decide
  have hdescent : baseEnd_7231250 < baseStart_7231250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231256 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7231256 : Nat := 118140960795 + 7231256 * 2 ^ 59
def prefixEnd_7231256 : Nat := 4983230072969 + 3 ^ 40 * 7231256 * 2
def baseEnd_7231256 : Nat := 3713110063708864911344065

theorem tailTrace_7231256 : CollatzResearch.WordTrace tailWord_7231256 prefixEnd_7231256 3713110063708864911344065 := by
  unfold tailWord_7231256
  simp only [CollatzResearch.WordTrace]
  refine ⟨131872786945200993523260811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175830382593601324697681081 131872786945200993523260811)
  ·
    refine ⟨197809180417801490284891217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131872786945200993523260811 197809180417801490284891217)
    ·
      refine ⟨148356885313351117713668413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197809180417801490284891217 148356885313351117713668413)
      ·
        refine ⟨55633831992506669142625655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148356885313351117713668413 55633831992506669142625655)
        ·
          refine ⟨83450747988760003713938483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55633831992506669142625655 83450747988760003713938483)
          ·
            refine ⟨125176121983140005570907725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83450747988760003713938483 125176121983140005570907725)
            ·
              refine ⟨46941045743677502089090397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125176121983140005570907725 46941045743677502089090397)
              ·
                refine ⟨17602892153879063283408899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46941045743677502089090397 17602892153879063283408899)
                ·
                  refine ⟨26404338230818594925113349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17602892153879063283408899 26404338230818594925113349)
                  ·
                    refine ⟨4950813418278486548458753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26404338230818594925113349 4950813418278486548458753)
                    ·
                      refine ⟨3713110063708864911344065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950813418278486548458753 3713110063708864911344065)
                      ·
                        rfl

theorem cell23_7231256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7231256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231256 prefixEnd_7231256 := by exact prefixLift 7231256
  have htrace : WordTrace (prefixWord ++ tailWord_7231256) baseStart_7231256 baseEnd_7231256 := by
    simpa [prefixWord, tailWord_7231256, baseEnd_7231256] using wordTrace_append hprefix tailTrace_7231256
  have hstable : (prefixWord ++ tailWord_7231256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231256).length < 2 ^ (prefixWord ++ tailWord_7231256).sum := by decide
  have hdescent : baseEnd_7231256 < baseStart_7231256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231290 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_7231290 : Nat := 118140960795 + 7231290 * 2 ^ 59
def prefixEnd_7231290 : Nat := 4983230072969 + 3 ^ 40 * 7231290 * 2
def baseEnd_7231290 : Nat := 3713127522051117778318909

theorem tailTrace_7231290 : CollatzResearch.WordTrace tailWord_7231290 prefixEnd_7231290 3713127522051117778318909 := by
  unfold tailWord_7231290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65936703493069702713314831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175831209314852540568839549 65936703493069702713314831)
  ·
    refine ⟨98905055239604554069972247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65936703493069702713314831 98905055239604554069972247)
    ·
      refine ⟨148357582859406831104958371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98905055239604554069972247 148357582859406831104958371)
      ·
        refine ⟨222536374289110246657437557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148357582859406831104958371 222536374289110246657437557)
        ·
          refine ⟨20862785089604085624134771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222536374289110246657437557 20862785089604085624134771)
          ·
            refine ⟨31294177634406128436202157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20862785089604085624134771 31294177634406128436202157)
            ·
              refine ⟨11735316612902298163575809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31294177634406128436202157 11735316612902298163575809)
              ·
                refine ⟨8801487459676723622681857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11735316612902298163575809 8801487459676723622681857)
                ·
                  refine ⟨6601115594757542717011393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801487459676723622681857 6601115594757542717011393)
                  ·
                    refine ⟨4950836696068157037758545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601115594757542717011393 4950836696068157037758545)
                    ·
                      refine ⟨3713127522051117778318909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950836696068157037758545 3713127522051117778318909)
                      ·
                        rfl

theorem cell23_7231290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_7231290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231290 prefixEnd_7231290 := by exact prefixLift 7231290
  have htrace : WordTrace (prefixWord ++ tailWord_7231290) baseStart_7231290 baseEnd_7231290 := by
    simpa [prefixWord, tailWord_7231290, baseEnd_7231290] using wordTrace_append hprefix tailTrace_7231290
  have hstable : (prefixWord ++ tailWord_7231290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231290).length < 2 ^ (prefixWord ++ tailWord_7231290).sum := by decide
  have hdescent : baseEnd_7231290 < baseStart_7231290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231329 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_7231329 : Nat := 118140960795 + 7231329 * 2 ^ 59
def prefixEnd_7231329 : Nat := 4983230072969 + 3 ^ 40 * 7231329 * 2
def baseEnd_7231329 : Nat := 3713147547796643125731229

theorem tailTrace_7231329 : CollatzResearch.WordTrace tailWord_7231329 prefixEnd_7231329 3713147547796643125731229 := by
  unfold tailWord_7231329
  simp only [CollatzResearch.WordTrace]
  refine ⟨263748236419137520513929041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175832157612758347009286027 263748236419137520513929041)
  ·
    refine ⟨197811177314353140385446781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263748236419137520513929041 197811177314353140385446781)
    ·
      refine ⟨74179191492882427644542543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197811177314353140385446781 74179191492882427644542543)
      ·
        refine ⟨111268787239323641466813815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74179191492882427644542543 111268787239323641466813815)
        ·
          refine ⟨166903180858985462200220723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111268787239323641466813815 166903180858985462200220723)
          ·
            refine ⟨250354771288478193300331085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166903180858985462200220723 250354771288478193300331085)
            ·
              refine ⟨93883039233179322487624157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250354771288478193300331085 93883039233179322487624157)
              ·
                refine ⟨35206139712442245932859059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93883039233179322487624157 35206139712442245932859059)
                ·
                  refine ⟨52809209568663368899288589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35206139712442245932859059 52809209568663368899288589)
                  ·
                    refine ⟨19803453588248763337233221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52809209568663368899288589 19803453588248763337233221)
                    ·
                      refine ⟨3713147547796643125731229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19803453588248763337233221 3713147547796643125731229)
                      ·
                        rfl

theorem cell23_7231329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_7231329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231329 prefixEnd_7231329 := by exact prefixLift 7231329
  have htrace : WordTrace (prefixWord ++ tailWord_7231329) baseStart_7231329 baseEnd_7231329 := by
    simpa [prefixWord, tailWord_7231329, baseEnd_7231329] using wordTrace_append hprefix tailTrace_7231329
  have hstable : (prefixWord ++ tailWord_7231329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231329).length < 2 ^ (prefixWord ++ tailWord_7231329).sum := by decide
  have hdescent : baseEnd_7231329 < baseStart_7231329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231330 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7231330 : Nat := 118140960795 + 7231330 * 2 ^ 59
def prefixEnd_7231330 : Nat := 4983230072969 + 3 ^ 40 * 7231330 * 2
def baseEnd_7231330 : Nat := 412572006808588624646525

theorem tailTrace_7231330 : CollatzResearch.WordTrace tailWord_7231330 prefixEnd_7231330 412572006808588624646525 := by
  unfold tailWord_7231330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65937068223033474421178861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175832181928089265123143629 65937068223033474421178861)
  ·
    refine ⟨24726400583637552907942073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65937068223033474421178861 24726400583637552907942073)
    ·
      refine ⟨18544800437728164680956555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24726400583637552907942073 18544800437728164680956555)
      ·
        refine ⟨27817200656592247021434833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18544800437728164680956555 27817200656592247021434833)
        ·
          refine ⟨20862900492444185266076125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27817200656592247021434833 20862900492444185266076125)
          ·
            refine ⟨7823587684666569474778547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20862900492444185266076125 7823587684666569474778547)
            ·
              refine ⟨11735381526999854212167821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823587684666569474778547 11735381526999854212167821)
              ·
                refine ⟨4400768072624945329562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11735381526999854212167821 4400768072624945329562933)
                ·
                  refine ⟨412572006808588624646525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400768072624945329562933 412572006808588624646525)
                  ·
                    rfl

theorem cell23_7231330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7231330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231330 prefixEnd_7231330 := by exact prefixLift 7231330
  have htrace : WordTrace (prefixWord ++ tailWord_7231330) baseStart_7231330 baseEnd_7231330 := by
    simpa [prefixWord, tailWord_7231330, baseEnd_7231330] using wordTrace_append hprefix tailTrace_7231330
  have hstable : (prefixWord ++ tailWord_7231330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231330).length < 2 ^ (prefixWord ++ tailWord_7231330).sum := by decide
  have hdescent : baseEnd_7231330 < baseStart_7231330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231383 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_7231383 : Nat := 118140960795 + 7231383 * 2 ^ 59
def prefixEnd_7231383 : Nat := 4983230072969 + 3 ^ 40 * 7231383 * 2
def baseEnd_7231383 : Nat := 3713175275751985914455981

theorem tailTrace_7231383 : CollatzResearch.WordTrace tailWord_7231383 prefixEnd_7231383 3713175275751985914455981 := by
  unfold tailWord_7231383
  simp only [CollatzResearch.WordTrace]
  refine ⟨263750205960941887736394803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175833470640627925157596535 263750205960941887736394803)
  ·
    refine ⟨395625308941412831604592205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263750205960941887736394803 395625308941412831604592205)
    ·
      refine ⟨148359490853029811851722077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395625308941412831604592205 148359490853029811851722077)
      ·
        refine ⟨55634809069886179444395779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148359490853029811851722077 55634809069886179444395779)
        ·
          refine ⟨83452213604829269166593669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55634809069886179444395779 83452213604829269166593669)
          ·
            refine ⟨15647290050905487968736313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83452213604829269166593669 15647290050905487968736313)
            ·
              refine ⟨11735467538179115976552235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647290050905487968736313 11735467538179115976552235)
              ·
                refine ⟨17603201307268673964828353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735467538179115976552235 17603201307268673964828353)
                ·
                  refine ⟨13202400980451505473621265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17603201307268673964828353 13202400980451505473621265)
                  ·
                    refine ⟨9901800735338629105215949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13202400980451505473621265 9901800735338629105215949)
                    ·
                      refine ⟨3713175275751985914455981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9901800735338629105215949 3713175275751985914455981)
                      ·
                        rfl

theorem cell23_7231383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_7231383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231383 prefixEnd_7231383 := by exact prefixLift 7231383
  have htrace : WordTrace (prefixWord ++ tailWord_7231383) baseStart_7231383 baseEnd_7231383 := by
    simpa [prefixWord, tailWord_7231383, baseEnd_7231383] using wordTrace_append hprefix tailTrace_7231383
  have hstable : (prefixWord ++ tailWord_7231383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231383).length < 2 ^ (prefixWord ++ tailWord_7231383).sum := by decide
  have hdescent : baseEnd_7231383 < baseStart_7231383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231419 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_7231419 : Nat := 118140960795 + 7231419 * 2 ^ 59
def prefixEnd_7231419 : Nat := 4983230072969 + 3 ^ 40 * 7231419 * 2
def baseEnd_7231419 : Nat := 3713193761055547773605815

theorem tailTrace_7231419 : CollatzResearch.WordTrace tailWord_7231419 prefixEnd_7231419 3713193761055547773605815 := by
  unfold tailWord_7231419
  simp only [CollatzResearch.WordTrace]
  refine ⟨263751518988811465884705311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175834345992540977256470207 263751518988811465884705311)
  ·
    refine ⟨395627278483217198827057967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263751518988811465884705311 395627278483217198827057967)
    ·
      refine ⟨593440917724825798240586951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395627278483217198827057967 593440917724825798240586951)
      ·
        refine ⟨890161376587238697360880427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593440917724825798240586951 890161376587238697360880427)
        ·
          refine ⟨1335242064880858046041320641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890161376587238697360880427 1335242064880858046041320641)
          ·
            refine ⟨1001431548660643534530990481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335242064880858046041320641 1001431548660643534530990481)
            ·
              refine ⟨751073661495482650898242861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001431548660643534530990481 751073661495482650898242861)
              ·
                refine ⟨281652623060805994086841073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751073661495482650898242861 281652623060805994086841073)
                ·
                  refine ⟨211239467295604495565130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281652623060805994086841073 211239467295604495565130805)
                  ·
                    refine ⟨19803700058962921459231013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 211239467295604495565130805 19803700058962921459231013)
                    ·
                      refine ⟨3713193761055547773605815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19803700058962921459231013 3713193761055547773605815)
                      ·
                        rfl

theorem cell23_7231419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_7231419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231419 prefixEnd_7231419 := by exact prefixLift 7231419
  have htrace : WordTrace (prefixWord ++ tailWord_7231419) baseStart_7231419 baseEnd_7231419 := by
    simpa [prefixWord, tailWord_7231419, baseEnd_7231419] using wordTrace_append hprefix tailTrace_7231419
  have hstable : (prefixWord ++ tailWord_7231419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231419).length < 2 ^ (prefixWord ++ tailWord_7231419).sum := by decide
  have hdescent : baseEnd_7231419 < baseStart_7231419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231466 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7231466 : Nat := 118140960795 + 7231466 * 2 ^ 59
def prefixEnd_7231466 : Nat := 4983230072969 + 3 ^ 40 * 7231466 * 2
def baseEnd_7231466 : Nat := 3713217894646309089718099

theorem tailTrace_7231466 : CollatzResearch.WordTrace tailWord_7231466 prefixEnd_7231466 3713217894646309089718099 := by
  unfold tailWord_7231466
  simp only [CollatzResearch.WordTrace]
  refine ⟨65938308304910298227916563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175835488813094128607777501 65938308304910298227916563)
  ·
    refine ⟨98907462457365447341874845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65938308304910298227916563 98907462457365447341874845)
    ·
      refine ⟨37090298421512042753203067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98907462457365447341874845 37090298421512042753203067)
      ·
        refine ⟨55635447632268064129804601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37090298421512042753203067 55635447632268064129804601)
        ·
          refine ⟨41726585724201048097353451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55635447632268064129804601 41726585724201048097353451)
          ·
            refine ⟨62589878586301572146030177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41726585724201048097353451 62589878586301572146030177)
            ·
              refine ⟨46942408939726179109522633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62589878586301572146030177 46942408939726179109522633)
              ·
                refine ⟨35206806704794634332141975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46942408939726179109522633 35206806704794634332141975)
                ·
                  refine ⟨52810210057191951498212963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35206806704794634332141975 52810210057191951498212963)
                  ·
                    refine ⟨79215315085787927247319445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52810210057191951498212963 79215315085787927247319445)
                    ·
                      refine ⟨3713217894646309089718099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79215315085787927247319445 3713217894646309089718099)
                      ·
                        rfl

theorem cell23_7231466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7231466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231466 prefixEnd_7231466 := by exact prefixLift 7231466
  have htrace : WordTrace (prefixWord ++ tailWord_7231466) baseStart_7231466 baseEnd_7231466 := by
    simpa [prefixWord, tailWord_7231466, baseEnd_7231466] using wordTrace_append hprefix tailTrace_7231466
  have hstable : (prefixWord ++ tailWord_7231466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231466).length < 2 ^ (prefixWord ++ tailWord_7231466).sum := by decide
  have hdescent : baseEnd_7231466 < baseStart_7231466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231473 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_7231473 : Nat := 118140960795 + 7231473 * 2 ^ 59
def prefixEnd_7231473 : Nat := 4983230072969 + 3 ^ 40 * 7231473 * 2
def baseEnd_7231473 : Nat := 3713221489010890562330567

theorem tailTrace_7231473 : CollatzResearch.WordTrace tailWord_7231473 prefixEnd_7231473 3713221489010890562330567 := by
  unfold tailWord_7231473
  simp only [CollatzResearch.WordTrace]
  refine ⟨263753488530615833107171073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175835659020410555404780715 263753488530615833107171073)
  ·
    refine ⟨197815116397961874830378305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263753488530615833107171073 197815116397961874830378305)
    ·
      refine ⟨148361337298471406122783729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197815116397961874830378305 148361337298471406122783729)
      ·
        refine ⟨111271002973853554592087797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148361337298471406122783729 111271002973853554592087797)
        ·
          refine ⟨10431656528798770743008231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111271002973853554592087797 10431656528798770743008231)
          ·
            refine ⟨15647484793198156114512347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431656528798770743008231 15647484793198156114512347)
            ·
              refine ⟨23471227189797234171768521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15647484793198156114512347 23471227189797234171768521)
              ·
                refine ⟨17603420392347925628826391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23471227189797234171768521 17603420392347925628826391)
                ·
                  refine ⟨26405130588521888443239587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17603420392347925628826391 26405130588521888443239587)
                  ·
                    refine ⟨39607695882782832664859381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26405130588521888443239587 39607695882782832664859381)
                    ·
                      refine ⟨3713221489010890562330567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39607695882782832664859381 3713221489010890562330567)
                      ·
                        rfl

theorem cell23_7231473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_7231473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231473 prefixEnd_7231473 := by exact prefixLift 7231473
  have htrace : WordTrace (prefixWord ++ tailWord_7231473) baseStart_7231473 baseEnd_7231473 := by
    simpa [prefixWord, tailWord_7231473, baseEnd_7231473] using wordTrace_append hprefix tailTrace_7231473
  have hstable : (prefixWord ++ tailWord_7231473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231473).length < 2 ^ (prefixWord ++ tailWord_7231473).sum := by decide
  have hdescent : baseEnd_7231473 < baseStart_7231473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231493 : List Nat := [1, 3, 1, 1, 2, 6, 2, 7]
def baseStart_7231493 : Nat := 118140960795 + 7231493 * 2 ^ 59
def prefixEnd_7231493 : Nat := 4983230072969 + 3 ^ 40 * 7231493 * 2
def baseEnd_7231493 : Nat := 137527102171258536447425

theorem tailTrace_7231493 : CollatzResearch.WordTrace tailWord_7231493 prefixEnd_7231493 137527102171258536447425 := by
  unfold tailWord_7231493
  simp only [CollatzResearch.WordTrace]
  refine ⟨263754217990543376522899133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175836145327028917681932755 263754217990543376522899133)
  ·
    refine ⟨98907831746453766196087175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263754217990543376522899133 98907831746453766196087175)
    ·
      refine ⟨148361747619680649294130763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98907831746453766196087175 148361747619680649294130763)
      ·
        refine ⟨222542621429520973941196145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148361747619680649294130763 222542621429520973941196145)
        ·
          refine ⟨166906966072140730455897109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222542621429520973941196145 166906966072140730455897109)
          ·
            refine ⟨7823764034631596740120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166906966072140730455897109 7823764034631596740120177)
            ·
              refine ⟨5867823025973697555090133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7823764034631596740120177 5867823025973697555090133)
              ·
                refine ⟨137527102171258536447425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5867823025973697555090133 137527102171258536447425)
                ·
                  rfl

theorem cell23_7231493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 7].length) (baseStart_7231493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231493 prefixEnd_7231493 := by exact prefixLift 7231493
  have htrace : WordTrace (prefixWord ++ tailWord_7231493) baseStart_7231493 baseEnd_7231493 := by
    simpa [prefixWord, tailWord_7231493, baseEnd_7231493] using wordTrace_append hprefix tailTrace_7231493
  have hstable : (prefixWord ++ tailWord_7231493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231493).length < 2 ^ (prefixWord ++ tailWord_7231493).sum := by decide
  have hdescent : baseEnd_7231493 < baseStart_7231493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231513 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 5, 3, 2]
def baseStart_7231513 : Nat := 118140960795 + 7231513 * 2 ^ 59
def prefixEnd_7231513 : Nat := 4983230072969 + 3 ^ 40 * 7231513 * 2
def baseEnd_7231513 : Nat := 3713242028237070405830383

theorem tailTrace_7231513 : CollatzResearch.WordTrace tailWord_7231513 prefixEnd_7231513 3713242028237070405830383 := by
  unfold tailWord_7231513
  simp only [CollatzResearch.WordTrace]
  refine ⟨263754947450470919938627193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175836631633647279959084795 263754947450470919938627193)
  ·
    refine ⟨197816210587853189953970395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263754947450470919938627193 197816210587853189953970395)
    ·
      refine ⟨296724315881779784930955593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197816210587853189953970395 296724315881779784930955593)
      ·
        refine ⟨222543236911334838698216695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296724315881779784930955593 222543236911334838698216695)
        ·
          refine ⟨333814855367002258047325043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222543236911334838698216695 333814855367002258047325043)
          ·
            refine ⟨500722283050503387070987565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333814855367002258047325043 500722283050503387070987565)
            ·
              refine ⟨187770856143938770151620337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500722283050503387070987565 187770856143938770151620337)
              ·
                refine ⟨140828142107954077613715253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187770856143938770151620337 140828142107954077613715253)
                ·
                  refine ⟨13202638322620694776285805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140828142107954077613715253 13202638322620694776285805)
                  ·
                    refine ⟨4950989370982760541107177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13202638322620694776285805 4950989370982760541107177)
                    ·
                      refine ⟨3713242028237070405830383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950989370982760541107177 3713242028237070405830383)
                      ·
                        rfl

theorem cell23_7231513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_7231513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231513 prefixEnd_7231513 := by exact prefixLift 7231513
  have htrace : WordTrace (prefixWord ++ tailWord_7231513) baseStart_7231513 baseEnd_7231513 := by
    simpa [prefixWord, tailWord_7231513, baseEnd_7231513] using wordTrace_append hprefix tailTrace_7231513
  have hstable : (prefixWord ++ tailWord_7231513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231513).length < 2 ^ (prefixWord ++ tailWord_7231513).sum := by decide
  have hdescent : baseEnd_7231513 < baseStart_7231513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231521 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7231521 : Nat := 118140960795 + 7231521 * 2 ^ 59
def prefixEnd_7231521 : Nat := 4983230072969 + 3 ^ 40 * 7231521 * 2
def baseEnd_7231521 : Nat := 3713246136082306374530347

theorem tailTrace_7231521 : CollatzResearch.WordTrace tailWord_7231521 prefixEnd_7231521 3713246136082306374530347 := by
  unfold tailWord_7231521
  simp only [CollatzResearch.WordTrace]
  refine ⟨263755239234441937304918417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175836826156294624869945611 263755239234441937304918417)
  ·
    refine ⟨197816429425831452978688813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263755239234441937304918417 197816429425831452978688813)
    ·
      refine ⟨74181161034686794867008305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197816429425831452978688813 74181161034686794867008305)
      ·
        refine ⟨55635870776015096150256229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74181161034686794867008305 55635870776015096150256229)
        ·
          refine ⟨10431725770502830528173043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55635870776015096150256229 10431725770502830528173043)
          ·
            refine ⟨15647588655754245792259565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431725770502830528173043 15647588655754245792259565)
            ·
              refine ⟨5867845745907842172097337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15647588655754245792259565 5867845745907842172097337)
              ·
                refine ⟨4400884309430881629073003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867845745907842172097337 4400884309430881629073003)
                ·
                  refine ⟨6601326464146322443609505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400884309430881629073003 6601326464146322443609505)
                  ·
                    refine ⟨4950994848109741832707129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601326464146322443609505 4950994848109741832707129)
                    ·
                      refine ⟨3713246136082306374530347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4950994848109741832707129 3713246136082306374530347)
                      ·
                        rfl

theorem cell23_7231521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7231521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231521 prefixEnd_7231521 := by exact prefixLift 7231521
  have htrace : WordTrace (prefixWord ++ tailWord_7231521) baseStart_7231521 baseEnd_7231521 := by
    simpa [prefixWord, tailWord_7231521, baseEnd_7231521] using wordTrace_append hprefix tailTrace_7231521
  have hstable : (prefixWord ++ tailWord_7231521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231521).length < 2 ^ (prefixWord ++ tailWord_7231521).sum := by decide
  have hdescent : baseEnd_7231521 < baseStart_7231521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231537 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_7231537 : Nat := 118140960795 + 7231537 * 2 ^ 59
def prefixEnd_7231537 : Nat := 4983230072969 + 3 ^ 40 * 7231537 * 2
def baseEnd_7231537 : Nat := 3713254351772778311930273

theorem tailTrace_7231537 : CollatzResearch.WordTrace tailWord_7231537 prefixEnd_7231537 3713254351772778311930273 := by
  unfold tailWord_7231537
  simp only [CollatzResearch.WordTrace]
  refine ⟨263755822802383972037500865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175837215201589314691667243 263755822802383972037500865)
  ·
    refine ⟨197816867101787979028125649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263755822802383972037500865 197816867101787979028125649)
    ·
      refine ⟨148362650326340984271094237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197816867101787979028125649 148362650326340984271094237)
      ·
        refine ⟨55635993872377869101660339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148362650326340984271094237 55635993872377869101660339)
        ·
          refine ⟨83453990808566803652490509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55635993872377869101660339 83453990808566803652490509)
          ·
            refine ⟨31295246553212551369683941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83453990808566803652490509 31295246553212551369683941)
            ·
              refine ⟨5867858728727353381815739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31295246553212551369683941 5867858728727353381815739)
              ·
                refine ⟨8801788093091030072723609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867858728727353381815739 8801788093091030072723609)
                ·
                  refine ⟨6601341069818272554542707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801788093091030072723609 6601341069818272554542707)
                  ·
                    refine ⟨9902011604727408831814061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6601341069818272554542707 9902011604727408831814061)
                    ·
                      refine ⟨3713254351772778311930273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902011604727408831814061 3713254351772778311930273)
                      ·
                        rfl

theorem cell23_7231537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_7231537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231537 prefixEnd_7231537 := by exact prefixLift 7231537
  have htrace : WordTrace (prefixWord ++ tailWord_7231537) baseStart_7231537 baseEnd_7231537 := by
    simpa [prefixWord, tailWord_7231537, baseEnd_7231537] using wordTrace_append hprefix tailTrace_7231537
  have hstable : (prefixWord ++ tailWord_7231537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231537).length < 2 ^ (prefixWord ++ tailWord_7231537).sum := by decide
  have hdescent : baseEnd_7231537 < baseStart_7231537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231560 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_7231560 : Nat := 118140960795 + 7231560 * 2 ^ 59
def prefixEnd_7231560 : Nat := 4983230072969 + 3 ^ 40 * 7231560 * 2
def baseEnd_7231560 : Nat := 3713266161827831721942667

theorem tailTrace_7231560 : CollatzResearch.WordTrace tailWord_7231560 prefixEnd_7231560 3713266161827831721942667 := by
  unfold tailWord_7231560
  simp only [CollatzResearch.WordTrace]
  refine ⟨131878330840650323482794067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175837774454200431310392089 131878330840650323482794067)
  ·
    refine ⟨197817496260975485224191101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131878330840650323482794067 197817496260975485224191101)
    ·
      refine ⟨74181561097865806959071663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197817496260975485224191101 74181561097865806959071663)
      ·
        refine ⟨111272341646798710438607495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74181561097865806959071663 111272341646798710438607495)
        ·
          refine ⟨166908512470198065657911243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111272341646798710438607495 166908512470198065657911243)
          ·
            refine ⟨250362768705297098486866865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166908512470198065657911243 250362768705297098486866865)
            ·
              refine ⟨187772076528972823865150149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250362768705297098486866865 187772076528972823865150149)
              ·
                refine ⟨35207264349182404474715653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187772076528972823865150149 35207264349182404474715653)
                ·
                  refine ⟨6601362065471700839009185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35207264349182404474715653 6601362065471700839009185)
                  ·
                    refine ⟨4951021549103775629256889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601362065471700839009185 4951021549103775629256889)
                    ·
                      refine ⟨3713266161827831721942667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951021549103775629256889 3713266161827831721942667)
                      ·
                        rfl

theorem cell23_7231560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_7231560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231560 prefixEnd_7231560 := by exact prefixLift 7231560
  have htrace : WordTrace (prefixWord ++ tailWord_7231560) baseStart_7231560 baseEnd_7231560 := by
    simpa [prefixWord, tailWord_7231560, baseEnd_7231560] using wordTrace_append hprefix tailTrace_7231560
  have hstable : (prefixWord ++ tailWord_7231560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231560).length < 2 ^ (prefixWord ++ tailWord_7231560).sum := by decide
  have hdescent : baseEnd_7231560 < baseStart_7231560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231577 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 2, 2, 2]
def baseStart_7231577 : Nat := 118140960795 + 7231577 * 2 ^ 59
def prefixEnd_7231577 : Nat := 4983230072969 + 3 ^ 40 * 7231577 * 2
def baseEnd_7231577 : Nat := 3713274890998958155430089

theorem tailTrace_7231577 : CollatzResearch.WordTrace tailWord_7231577 prefixEnd_7231577 3713274890998958155430089 := by
  unfold tailWord_7231577
  simp only [CollatzResearch.WordTrace]
  refine ⟨263757281722239058868956985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175838187814826039245971323 263757281722239058868956985)
  ·
    refine ⟨197817961291679294151717739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263757281722239058868956985 197817961291679294151717739)
    ·
      refine ⟨296726941937518941227576609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197817961291679294151717739 296726941937518941227576609)
      ·
        refine ⟨222545206453139205920682457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296726941937518941227576609 222545206453139205920682457)
        ·
          refine ⟨166908904839854404440511843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222545206453139205920682457 166908904839854404440511843)
          ·
            refine ⟨250363357259781606660767765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166908904839854404440511843 250363357259781606660767765)
            ·
              refine ⟨11735782371552262812223489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250363357259781606660767765 11735782371552262812223489)
              ·
                refine ⟨8801836778664197109167617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11735782371552262812223489 8801836778664197109167617)
                ·
                  refine ⟨6601377583998147831875713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801836778664197109167617 6601377583998147831875713)
                  ·
                    refine ⟨4951033187998610873906785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601377583998147831875713 4951033187998610873906785)
                    ·
                      refine ⟨3713274890998958155430089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951033187998610873906785 3713274890998958155430089)
                      ·
                        rfl

theorem cell23_7231577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_7231577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231577 prefixEnd_7231577 := by exact prefixLift 7231577
  have htrace : WordTrace (prefixWord ++ tailWord_7231577) baseStart_7231577 baseEnd_7231577 := by
    simpa [prefixWord, tailWord_7231577, baseEnd_7231577] using wordTrace_append hprefix tailTrace_7231577
  have hstable : (prefixWord ++ tailWord_7231577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231577).length < 2 ^ (prefixWord ++ tailWord_7231577).sum := by decide
  have hdescent : baseEnd_7231577 < baseStart_7231577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231593 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_7231593 : Nat := 118140960795 + 7231593 * 2 ^ 59
def prefixEnd_7231593 : Nat := 4983230072969 + 3 ^ 40 * 7231593 * 2
def baseEnd_7231593 : Nat := 3713283106689430092830015

theorem tailTrace_7231593 : CollatzResearch.WordTrace tailWord_7231593 prefixEnd_7231593 3713283106689430092830015 := by
  unfold tailWord_7231593
  simp only [CollatzResearch.WordTrace]
  refine ⟨263757865290181093601539433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175838576860120729067692955 263757865290181093601539433)
  ·
    refine ⟨197818398967635820201154575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263757865290181093601539433 197818398967635820201154575)
    ·
      refine ⟨296727598451453730301731863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197818398967635820201154575 296727598451453730301731863)
      ·
        refine ⟨445091397677180595452597795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296727598451453730301731863 445091397677180595452597795)
        ·
          refine ⟨667637096515770893178896693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445091397677180595452597795 667637096515770893178896693)
          ·
            refine ⟨62590977798353521235521565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 667637096515770893178896693 62590977798353521235521565)
            ·
              refine ⟨23471616674382570463320587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62590977798353521235521565 23471616674382570463320587)
              ·
                refine ⟨35207425011573855694980881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23471616674382570463320587 35207425011573855694980881)
                ·
                  refine ⟨26405568758680391771235661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35207425011573855694980881 26405568758680391771235661)
                  ·
                    refine ⟨9902088284505146914213373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26405568758680391771235661 9902088284505146914213373)
                    ·
                      refine ⟨3713283106689430092830015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902088284505146914213373 3713283106689430092830015)
                      ·
                        rfl

theorem cell23_7231593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_7231593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231593 prefixEnd_7231593 := by exact prefixLift 7231593
  have htrace : WordTrace (prefixWord ++ tailWord_7231593) baseStart_7231593 baseEnd_7231593 := by
    simpa [prefixWord, tailWord_7231593, baseEnd_7231593] using wordTrace_append hprefix tailTrace_7231593
  have hstable : (prefixWord ++ tailWord_7231593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231593).length < 2 ^ (prefixWord ++ tailWord_7231593).sum := by decide
  have hdescent : baseEnd_7231593 < baseStart_7231593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231613 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_7231613 : Nat := 118140960795 + 7231613 * 2 ^ 59
def prefixEnd_7231613 : Nat := 4983230072969 + 3 ^ 40 * 7231613 * 2
def baseEnd_7231613 : Nat := 1237764458767506671526641

theorem tailTrace_7231613 : CollatzResearch.WordTrace tailWord_7231613 prefixEnd_7231613 1237764458767506671526641 := by
  unfold tailWord_7231613
  simp only [CollatzResearch.WordTrace]
  refine ⟨263758594750108637017267493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175839063166739091344844995 263758594750108637017267493)
  ·
    refine ⟨49454736515645369440737655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263758594750108637017267493 49454736515645369440737655)
    ·
      refine ⟨74182104773468054161106483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49454736515645369440737655 74182104773468054161106483)
      ·
        refine ⟨111273157160202081241659725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74182104773468054161106483 111273157160202081241659725)
        ·
          refine ⟨41727433935075780465622397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111273157160202081241659725 41727433935075780465622397)
          ·
            refine ⟨15647787725653417674608399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41727433935075780465622397 15647787725653417674608399)
            ·
              refine ⟨23471681588480126511912599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15647787725653417674608399 23471681588480126511912599)
              ·
                refine ⟨35207522382720189767868899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23471681588480126511912599 35207522382720189767868899)
                ·
                  refine ⟨52811283574080284651803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35207522382720189767868899 52811283574080284651803349)
                  ·
                    refine ⟨1237764458767506671526641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52811283574080284651803349 1237764458767506671526641)
                    ·
                      rfl

theorem cell23_7231613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_7231613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231613 prefixEnd_7231613 := by exact prefixLift 7231613
  have htrace : WordTrace (prefixWord ++ tailWord_7231613) baseStart_7231613 baseEnd_7231613 := by
    simpa [prefixWord, tailWord_7231613, baseEnd_7231613] using wordTrace_append hprefix tailTrace_7231613
  have hstable : (prefixWord ++ tailWord_7231613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231613).length < 2 ^ (prefixWord ++ tailWord_7231613).sum := by decide
  have hdescent : baseEnd_7231613 < baseStart_7231613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231617 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 5]
def baseStart_7231617 : Nat := 118140960795 + 7231617 * 2 ^ 59
def prefixEnd_7231617 : Nat := 4983230072969 + 3 ^ 40 * 7231617 * 2
def baseEnd_7231617 : Nat := 412588381136126444325545

theorem tailTrace_7231617 : CollatzResearch.WordTrace tailWord_7231617 prefixEnd_7231617 412588381136126444325545 := by
  unfold tailWord_7231617
  simp only [CollatzResearch.WordTrace]
  refine ⟨263758740642094145700413105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175839160428062763800275403 263758740642094145700413105)
  ·
    refine ⟨197819055481570609275309829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263758740642094145700413105 197819055481570609275309829)
    ·
      refine ⟨37091072902794489239120593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197819055481570609275309829 37091072902794489239120593)
      ·
        refine ⟨27818304677095866929340445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37091072902794489239120593 27818304677095866929340445)
        ·
          refine ⟨10431864253910950098502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27818304677095866929340445 10431864253910950098502667)
          ·
            refine ⟨15647796380866425147754001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431864253910950098502667 15647796380866425147754001)
            ·
              refine ⟨11735847285649818860815501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647796380866425147754001 11735847285649818860815501)
              ·
                refine ⟨4400942732118682072805813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11735847285649818860815501 4400942732118682072805813)
                ·
                  refine ⟨412588381136126444325545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400942732118682072805813 412588381136126444325545)
                  ·
                    rfl

theorem cell23_7231617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 5].length) (baseStart_7231617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231617 prefixEnd_7231617 := by exact prefixLift 7231617
  have htrace : WordTrace (prefixWord ++ tailWord_7231617) baseStart_7231617 baseEnd_7231617 := by
    simpa [prefixWord, tailWord_7231617, baseEnd_7231617] using wordTrace_append hprefix tailTrace_7231617
  have hstable : (prefixWord ++ tailWord_7231617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231617).length < 2 ^ (prefixWord ++ tailWord_7231617).sum := by decide
  have hdescent : baseEnd_7231617 < baseStart_7231617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231650 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7231650 : Nat := 118140960795 + 7231650 * 2 ^ 59
def prefixEnd_7231650 : Nat := 4983230072969 + 3 ^ 40 * 7231650 * 2
def baseEnd_7231650 : Nat := 3713312375086736369817253

theorem tailTrace_7231650 : CollatzResearch.WordTrace tailWord_7231650 prefixEnd_7231650 3713312375086736369817253 := by
  unfold tailWord_7231650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65939986062743648084091101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175839962833983061557576269 65939986062743648084091101)
  ·
    refine ⟨24727494773528868031534163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65939986062743648084091101 24727494773528868031534163)
    ·
      refine ⟨37091242160293302047301245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727494773528868031534163 37091242160293302047301245)
      ·
        refine ⟨13909215810109988267737967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37091242160293302047301245 13909215810109988267737967)
        ·
          refine ⟨20863823715164982401606951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909215810109988267737967 20863823715164982401606951)
          ·
            refine ⟨31295735572747473602410427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20863823715164982401606951 31295735572747473602410427)
            ·
              refine ⟨46943603359121210403615641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31295735572747473602410427 46943603359121210403615641)
              ·
                refine ⟨35207702519340907802711731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46943603359121210403615641 35207702519340907802711731)
                ·
                  refine ⟨52811553779011361704067597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35207702519340907802711731 52811553779011361704067597)
                  ·
                    refine ⟨19804332667129260639025349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52811553779011361704067597 19804332667129260639025349)
                    ·
                      refine ⟨3713312375086736369817253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19804332667129260639025349 3713312375086736369817253)
                      ·
                        rfl

theorem cell23_7231650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7231650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231650 prefixEnd_7231650 := by exact prefixLift 7231650
  have htrace : WordTrace (prefixWord ++ tailWord_7231650) baseStart_7231650 baseEnd_7231650 := by
    simpa [prefixWord, tailWord_7231650, baseEnd_7231650] using wordTrace_append hprefix tailTrace_7231650
  have hstable : (prefixWord ++ tailWord_7231650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231650).length < 2 ^ (prefixWord ++ tailWord_7231650).sum := by decide
  have hdescent : baseEnd_7231650 < baseStart_7231650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231653 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_7231653 : Nat := 118140960795 + 7231653 * 2 ^ 59
def prefixEnd_7231653 : Nat := 4983230072969 + 3 ^ 40 * 7231653 * 2
def baseEnd_7231653 : Nat := 3713313915528699858079739

theorem tailTrace_7231653 : CollatzResearch.WordTrace tailWord_7231653 prefixEnd_7231653 3713313915528699858079739 := by
  unfold tailWord_7231653
  simp only [CollatzResearch.WordTrace]
  refine ⟨263760053669963723848723613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175840035779975815899149075 263760053669963723848723613)
  ·
    refine ⟨98910020126236396443271355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263760053669963723848723613 98910020126236396443271355)
    ·
      refine ⟨148365030189354594664907033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98910020126236396443271355 148365030189354594664907033)
      ·
        refine ⟨111273772642015945998680275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148365030189354594664907033 111273772642015945998680275)
        ·
          refine ⟨166910658963023918998020413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111273772642015945998680275 166910658963023918998020413)
          ·
            refine ⟨62591497111133969624257655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166910658963023918998020413 62591497111133969624257655)
            ·
              refine ⟨93887245666700954436386483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62591497111133969624257655 93887245666700954436386483)
              ·
                refine ⟨140830868500051431654579725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93887245666700954436386483 140830868500051431654579725)
                ·
                  refine ⟨52811575687519286870467397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140830868500051431654579725 52811575687519286870467397)
                  ·
                    refine ⟨9902170441409866288212637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52811575687519286870467397 9902170441409866288212637)
                    ·
                      refine ⟨3713313915528699858079739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902170441409866288212637 3713313915528699858079739)
                      ·
                        rfl

theorem cell23_7231653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_7231653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231653 prefixEnd_7231653 := by exact prefixLift 7231653
  have htrace : WordTrace (prefixWord ++ tailWord_7231653) baseStart_7231653 baseEnd_7231653 := by
    simpa [prefixWord, tailWord_7231653, baseEnd_7231653] using wordTrace_append hprefix tailTrace_7231653
  have hstable : (prefixWord ++ tailWord_7231653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231653).length < 2 ^ (prefixWord ++ tailWord_7231653).sum := by decide
  have hdescent : baseEnd_7231653 < baseStart_7231653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231668 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7231668 : Nat := 118140960795 + 7231668 * 2 ^ 59
def prefixEnd_7231668 : Nat := 4983230072969 + 3 ^ 40 * 7231668 * 2
def baseEnd_7231668 : Nat := 412591290859835255488019

theorem tailTrace_7231668 : CollatzResearch.WordTrace tailWord_7231668 prefixEnd_7231668 412591290859835255488019 := by
  unfold tailWord_7231668
  simp only [CollatzResearch.WordTrace]
  refine ⟨131880300382454690705259829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175840400509939587607013105 131880300382454690705259829)
  ·
    refine ⟨12363778160855127253618109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131880300382454690705259829 12363778160855127253618109)
    ·
      refine ⟨4636416810320672720106791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12363778160855127253618109 4636416810320672720106791)
      ·
        refine ⟨6954625215481009080160187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636416810320672720106791 6954625215481009080160187)
        ·
          refine ⟨10431937823221513620240281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954625215481009080160187 10431937823221513620240281)
          ·
            refine ⟨7823953367416135215180211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10431937823221513620240281 7823953367416135215180211)
            ·
              refine ⟨11735930051124202822770317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823953367416135215180211 11735930051124202822770317)
              ·
                refine ⟨4400973769171576058538869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11735930051124202822770317 4400973769171576058538869)
                ·
                  refine ⟨412591290859835255488019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400973769171576058538869 412591290859835255488019)
                  ·
                    rfl

theorem cell23_7231668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7231668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231668 prefixEnd_7231668 := by exact prefixLift 7231668
  have htrace : WordTrace (prefixWord ++ tailWord_7231668) baseStart_7231668 baseEnd_7231668 := by
    simpa [prefixWord, tailWord_7231668, baseEnd_7231668] using wordTrace_append hprefix tailTrace_7231668
  have hstable : (prefixWord ++ tailWord_7231668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231668).length < 2 ^ (prefixWord ++ tailWord_7231668).sum := by decide
  have hdescent : baseEnd_7231668 < baseStart_7231668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231703 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 3, 5]
def baseStart_7231703 : Nat := 118140960795 + 7231703 * 2 ^ 59
def prefixEnd_7231703 : Nat := 4983230072969 + 3 ^ 40 * 7231703 * 2
def baseEnd_7231703 : Nat := 1237779863187141554151503

theorem tailTrace_7231703 : CollatzResearch.WordTrace tailWord_7231703 prefixEnd_7231703 1237779863187141554151503 := by
  unfold tailWord_7231703
  simp only [CollatzResearch.WordTrace]
  refine ⟨263761877319782582388043763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175841251546521721592029175 263761877319782582388043763)
  ·
    refine ⟨395642815979673873582065645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263761877319782582388043763 395642815979673873582065645)
    ·
      refine ⟨148366055992377702593274617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395642815979673873582065645 148366055992377702593274617)
      ·
        refine ⟨111274541994283276944955963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148366055992377702593274617 111274541994283276944955963)
        ·
          refine ⟨166911812991424915417433945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111274541994283276944955963 166911812991424915417433945)
          ·
            refine ⟨125183859743568686563075459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166911812991424915417433945 125183859743568686563075459)
            ·
              refine ⟨187775789615353029844613189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125183859743568686563075459 187775789615353029844613189)
              ·
                refine ⟨35207960552878693095864973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187775789615353029844613189 35207960552878693095864973)
                ·
                  refine ⟨13202985207329509910949365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35207960552878693095864973 13202985207329509910949365)
                  ·
                    refine ⟨1237779863187141554151503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13202985207329509910949365 1237779863187141554151503)
                    ·
                      rfl

theorem cell23_7231703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_7231703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231703 prefixEnd_7231703 := by exact prefixLift 7231703
  have htrace : WordTrace (prefixWord ++ tailWord_7231703) baseStart_7231703 baseEnd_7231703 := by
    simpa [prefixWord, tailWord_7231703, baseEnd_7231703] using wordTrace_append hprefix tailTrace_7231703
  have hstable : (prefixWord ++ tailWord_7231703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231703).length < 2 ^ (prefixWord ++ tailWord_7231703).sum := by decide
  have hdescent : baseEnd_7231703 < baseStart_7231703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231720 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7231720 : Nat := 118140960795 + 7231720 * 2 ^ 59
def prefixEnd_7231720 : Nat := 4983230072969 + 3 ^ 40 * 7231720 * 2
def baseEnd_7231720 : Nat := 1237782772910850365313977

theorem tailTrace_7231720 : CollatzResearch.WordTrace tailWord_7231720 prefixEnd_7231720 1237782772910850365313977 := by
  unfold tailWord_7231720
  simp only [CollatzResearch.WordTrace]
  refine ⟨131881248680360497145706307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175841664907147329527608409 131881248680360497145706307)
  ·
    refine ⟨197821873020540745718559461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131881248680360497145706307 197821873020540745718559461)
    ·
      refine ⟨37091601191351389822229899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197821873020540745718559461 37091601191351389822229899)
      ·
        refine ⟨55637401787027084733344849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37091601191351389822229899 55637401787027084733344849)
        ·
          refine ⟨41728051340270313550008637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55637401787027084733344849 41728051340270313550008637)
          ·
            refine ⟨15648019252601367581253239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41728051340270313550008637 15648019252601367581253239)
            ·
              refine ⟨23472028878902051371879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648019252601367581253239 23472028878902051371879859)
              ·
                refine ⟨35208043318353077057819789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472028878902051371879859 35208043318353077057819789)
                ·
                  refine ⟨13203016244382403896682421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35208043318353077057819789 13203016244382403896682421)
                  ·
                    refine ⟨1237782772910850365313977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13203016244382403896682421 1237782772910850365313977)
                    ·
                      rfl

theorem cell23_7231720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7231720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231720 prefixEnd_7231720 := by exact prefixLift 7231720
  have htrace : WordTrace (prefixWord ++ tailWord_7231720) baseStart_7231720 baseEnd_7231720 := by
    simpa [prefixWord, tailWord_7231720, baseEnd_7231720] using wordTrace_append hprefix tailTrace_7231720
  have hstable : (prefixWord ++ tailWord_7231720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231720).length < 2 ^ (prefixWord ++ tailWord_7231720).sum := by decide
  have hdescent : baseEnd_7231720 < baseStart_7231720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231727 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 2, 3, 2]
def baseStart_7231727 : Nat := 118140960795 + 7231727 * 2 ^ 59
def prefixEnd_7231727 : Nat := 4983230072969 + 3 ^ 40 * 7231727 * 2
def baseEnd_7231727 : Nat := 3713351913097132568554399

theorem tailTrace_7231727 : CollatzResearch.WordTrace tailWord_7231727 prefixEnd_7231727 3713351913097132568554399 := by
  unfold tailWord_7231727
  simp only [CollatzResearch.WordTrace]
  refine ⟨263762752671695634486917435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175841835114463756324611623 263762752671695634486917435)
  ·
    refine ⟨395644129007543451730376153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263762752671695634486917435 395644129007543451730376153)
    ·
      refine ⟨296733096755657588797782115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395644129007543451730376153 296733096755657588797782115)
      ·
        refine ⟨445099645133486383196673173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296733096755657588797782115 445099645133486383196673173)
        ·
          refine ⟨20864045865632174212344055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445099645133486383196673173 20864045865632174212344055)
          ·
            refine ⟨31296068798448261318516083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20864045865632174212344055 31296068798448261318516083)
            ·
              refine ⟨46944103197672391977774125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31296068798448261318516083 46944103197672391977774125)
              ·
                refine ⟨17604038699127146991665297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46944103197672391977774125 17604038699127146991665297)
                ·
                  refine ⟨13203029024345360243748973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17604038699127146991665297 13203029024345360243748973)
                  ·
                    refine ⟨4951135884129510091405865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13203029024345360243748973 4951135884129510091405865)
                    ·
                      refine ⟨3713351913097132568554399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951135884129510091405865 3713351913097132568554399)
                      ·
                        rfl

theorem cell23_7231727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3, 2].length) (baseStart_7231727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231727 prefixEnd_7231727 := by exact prefixLift 7231727
  have htrace : WordTrace (prefixWord ++ tailWord_7231727) baseStart_7231727 baseEnd_7231727 := by
    simpa [prefixWord, tailWord_7231727, baseEnd_7231727] using wordTrace_append hprefix tailTrace_7231727
  have hstable : (prefixWord ++ tailWord_7231727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231727).length < 2 ^ (prefixWord ++ tailWord_7231727).sum := by decide
  have hdescent : baseEnd_7231727 < baseStart_7231727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231767 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 2, 4]
def baseStart_7231767 : Nat := 118140960795 + 7231767 * 2 ^ 59
def prefixEnd_7231767 : Nat := 4983230072969 + 3 ^ 40 * 7231767 * 2
def baseEnd_7231767 : Nat := 1237790817441104137351405

theorem tailTrace_7231767 : CollatzResearch.WordTrace tailWord_7231767 prefixEnd_7231767 1237790817441104137351405 := by
  unfold tailWord_7231767
  simp only [CollatzResearch.WordTrace]
  refine ⟨263764211591550721318373555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175842807727700480878915703 263764211591550721318373555)
  ·
    refine ⟨395646317387326081977560333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263764211591550721318373555 395646317387326081977560333)
    ·
      refine ⟨148367369020247280741585125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395646317387326081977560333 148367369020247280741585125)
      ·
        refine ⟨27818881691296365139047211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148367369020247280741585125 27818881691296365139047211)
        ·
          refine ⟨41728322536944547708570817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27818881691296365139047211 41728322536944547708570817)
          ·
            refine ⟨31296241902708410781428113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41728322536944547708570817 31296241902708410781428113)
            ·
              refine ⟨23472181427031308086071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31296241902708410781428113 23472181427031308086071085)
              ·
                refine ⟨8802068035136740532276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23472181427031308086071085 8802068035136740532276657)
                ·
                  refine ⟨6601551026352555399207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802068035136740532276657 6601551026352555399207493)
                  ·
                    refine ⟨1237790817441104137351405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601551026352555399207493 1237790817441104137351405)
                    ·
                      rfl

theorem cell23_7231767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_7231767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231767 prefixEnd_7231767 := by exact prefixLift 7231767
  have htrace : WordTrace (prefixWord ++ tailWord_7231767) baseStart_7231767 baseEnd_7231767 := by
    simpa [prefixWord, tailWord_7231767, baseEnd_7231767] using wordTrace_append hprefix tailTrace_7231767
  have hstable : (prefixWord ++ tailWord_7231767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231767).length < 2 ^ (prefixWord ++ tailWord_7231767).sum := by decide
  have hdescent : baseEnd_7231767 < baseStart_7231767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231774 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7231774 : Nat := 118140960795 + 7231774 * 2 ^ 59
def prefixEnd_7231774 : Nat := 4983230072969 + 3 ^ 40 * 7231774 * 2
def baseEnd_7231774 : Nat := 3713376046687893884666683

theorem tailTrace_7231774 : CollatzResearch.WordTrace tailWord_7231774 prefixEnd_7231774 3713376046687893884666683 := by
  unfold tailWord_7231774
  simp only [CollatzResearch.WordTrace]
  refine ⟨32970558362815670189234797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175842977935016907675918917 32970558362815670189234797)
  ·
    refine ⟨12363959386055876320963049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32970558362815670189234797 12363959386055876320963049)
    ·
      refine ⟨9272969539541907240722287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12363959386055876320963049 9272969539541907240722287)
      ·
        refine ⟨13909454309312860861083431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272969539541907240722287 13909454309312860861083431)
        ·
          refine ⟨20864181463969291291625147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909454309312860861083431 20864181463969291291625147)
          ·
            refine ⟨31296272195953936937437721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20864181463969291291625147 31296272195953936937437721)
            ·
              refine ⟨23472204146965452703078291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31296272195953936937437721 23472204146965452703078291)
              ·
                refine ⟨35208306220448179054617437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472204146965452703078291 35208306220448179054617437)
                ·
                  refine ⟨13203114832668067145481539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35208306220448179054617437 13203114832668067145481539)
                  ·
                    refine ⟨19804672249002100718222309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203114832668067145481539 19804672249002100718222309)
                    ·
                      refine ⟨3713376046687893884666683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19804672249002100718222309 3713376046687893884666683)
                      ·
                        rfl

theorem cell23_7231774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7231774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231774 prefixEnd_7231774 := by exact prefixLift 7231774
  have htrace : WordTrace (prefixWord ++ tailWord_7231774) baseStart_7231774 baseEnd_7231774 := by
    simpa [prefixWord, tailWord_7231774, baseEnd_7231774] using wordTrace_append hprefix tailTrace_7231774
  have hstable : (prefixWord ++ tailWord_7231774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231774).length < 2 ^ (prefixWord ++ tailWord_7231774).sum := by decide
  have hdescent : baseEnd_7231774 < baseStart_7231774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231794 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_7231794 : Nat := 118140960795 + 7231794 * 2 ^ 59
def prefixEnd_7231794 : Nat := 4983230072969 + 3 ^ 40 * 7231794 * 2
def baseEnd_7231794 : Nat := 3713386316300983806416591

theorem tailTrace_7231794 : CollatzResearch.WordTrace tailWord_7231794 prefixEnd_7231794 3713386316300983806416591 := by
  unfold tailWord_7231794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65941299090613226232401609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175843464241635269953070957 65941299090613226232401609)
  ·
    refine ⟨49455974317959919674301207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65941299090613226232401609 49455974317959919674301207)
    ·
      refine ⟨74183961476939879511451811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49455974317959919674301207 74183961476939879511451811)
      ·
        refine ⟨111275942215409819267177717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74183961476939879511451811 111275942215409819267177717)
        ·
          refine ⟨10432119582694670556297911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111275942215409819267177717 10432119582694670556297911)
          ·
            refine ⟨15648179374042005834446867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432119582694670556297911 15648179374042005834446867)
            ·
              refine ⟨23472269061063008751670301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648179374042005834446867 23472269061063008751670301)
              ·
                refine ⟨8802100897898628281876363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23472269061063008751670301 8802100897898628281876363)
                ·
                  refine ⟨13203151346847942422814545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802100897898628281876363 13203151346847942422814545)
                  ·
                    refine ⟨9902363510135956817110909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13203151346847942422814545 9902363510135956817110909)
                    ·
                      refine ⟨3713386316300983806416591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902363510135956817110909 3713386316300983806416591)
                      ·
                        rfl

theorem cell23_7231794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_7231794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231794 prefixEnd_7231794 := by exact prefixLift 7231794
  have htrace : WordTrace (prefixWord ++ tailWord_7231794) baseStart_7231794 baseEnd_7231794 := by
    simpa [prefixWord, tailWord_7231794, baseEnd_7231794] using wordTrace_append hprefix tailTrace_7231794
  have hstable : (prefixWord ++ tailWord_7231794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231794).length < 2 ^ (prefixWord ++ tailWord_7231794).sum := by decide
  have hdescent : baseEnd_7231794 < baseStart_7231794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231807 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_7231807 : Nat := 118140960795 + 7231807 * 2 ^ 59
def prefixEnd_7231807 : Nat := 4983230072969 + 3 ^ 40 * 7231807 * 2
def baseEnd_7231807 : Nat := 3713392991549492255554031

theorem tailTrace_7231807 : CollatzResearch.WordTrace tailWord_7231807 prefixEnd_7231807 3713392991549492255554031 := by
  unfold tailWord_7231807
  simp only [CollatzResearch.WordTrace]
  refine ⟨263765670511405808149829675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175843780340937205433219783 263765670511405808149829675)
  ·
    refine ⟨395648505767108712224744513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263765670511405808149829675 395648505767108712224744513)
    ·
      refine ⟨296736379325331534168558385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395648505767108712224744513 296736379325331534168558385)
      ·
        refine ⟨222552284493998650626418789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296736379325331534168558385 222552284493998650626418789)
        ·
          refine ⟨41728553342624746992453523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222552284493998650626418789 41728553342624746992453523)
          ·
            refine ⟨62592830013937120488680285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41728553342624746992453523 62592830013937120488680285)
            ·
              refine ⟨23472311255226420183255107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62592830013937120488680285 23472311255226420183255107)
              ·
                refine ⟨35208466882839630274882661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472311255226420183255107 35208466882839630274882661)
                ·
                  refine ⟨6601587540532430676540499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35208466882839630274882661 6601587540532430676540499)
                  ·
                    refine ⟨9902381310798646014810749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6601587540532430676540499 9902381310798646014810749)
                    ·
                      refine ⟨3713392991549492255554031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902381310798646014810749 3713392991549492255554031)
                      ·
                        rfl

theorem cell23_7231807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_7231807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231807 prefixEnd_7231807 := by exact prefixLift 7231807
  have htrace : WordTrace (prefixWord ++ tailWord_7231807) baseStart_7231807 baseEnd_7231807 := by
    simpa [prefixWord, tailWord_7231807, baseEnd_7231807] using wordTrace_append hprefix tailTrace_7231807
  have hstable : (prefixWord ++ tailWord_7231807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231807).length < 2 ^ (prefixWord ++ tailWord_7231807).sum := by decide
  have hdescent : baseEnd_7231807 < baseStart_7231807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231823 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 8]
def baseStart_7231823 : Nat := 118140960795 + 7231823 * 2 ^ 59
def prefixEnd_7231823 : Nat := 4983230072969 + 3 ^ 40 * 7231823 * 2
def baseEnd_7231823 : Nat := 1237800402413321397651319

theorem tailTrace_7231823 : CollatzResearch.WordTrace tailWord_7231823 prefixEnd_7231823 1237800402413321397651319 := by
  unfold tailWord_7231823
  simp only [CollatzResearch.WordTrace]
  refine ⟨263766254079347842882412123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175844169386231895254941415 263766254079347842882412123)
  ·
    refine ⟨395649381119021764323618185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263766254079347842882412123 395649381119021764323618185)
    ·
      refine ⟨296737035839266323242713639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395649381119021764323618185 296737035839266323242713639)
      ·
        refine ⟨445105553758899484864070459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296737035839266323242713639 445105553758899484864070459)
        ·
          refine ⟨667658330638349227296105689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445105553758899484864070459 667658330638349227296105689)
          ·
            refine ⟨500743747978761920472079267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667658330638349227296105689 500743747978761920472079267)
            ·
              refine ⟨751115621968142880708118901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500743747978761920472079267 751115621968142880708118901)
              ·
                refine ⟨70417089559513395066386147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751115621968142880708118901 70417089559513395066386147)
                ·
                  refine ⟨105625634339270092599579221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70417089559513395066386147 105625634339270092599579221)
                  ·
                    refine ⟨1237800402413321397651319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105625634339270092599579221 1237800402413321397651319)
                    ·
                      rfl

theorem cell23_7231823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_7231823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231823 prefixEnd_7231823 := by exact prefixLift 7231823
  have htrace : WordTrace (prefixWord ++ tailWord_7231823) baseStart_7231823 baseEnd_7231823 := by
    simpa [prefixWord, tailWord_7231823, baseEnd_7231823] using wordTrace_append hprefix tailTrace_7231823
  have hstable : (prefixWord ++ tailWord_7231823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231823).length < 2 ^ (prefixWord ++ tailWord_7231823).sum := by decide
  have hdescent : baseEnd_7231823 < baseStart_7231823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231881 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 2, 2, 2]
def baseStart_7231881 : Nat := 118140960795 + 7231881 * 2 ^ 59
def prefixEnd_7231881 : Nat := 4983230072969 + 3 ^ 40 * 7231881 * 2
def baseEnd_7231881 : Nat := 3713430989117924966028691

theorem tailTrace_7231881 : CollatzResearch.WordTrace tailWord_7231881 prefixEnd_7231881 3713430989117924966028691 := by
  unfold tailWord_7231881
  simp only [CollatzResearch.WordTrace]
  refine ⟨263768369513137718788023497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175845579675425145858682331 263768369513137718788023497)
  ·
    refine ⟨197826277134853289091017623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263768369513137718788023497 197826277134853289091017623)
    ·
      refine ⟨296739415702279933636526435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197826277134853289091017623 296739415702279933636526435)
      ·
        refine ⟨445109123553419900454789653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296739415702279933636526435 445109123553419900454789653)
        ·
          refine ⟨20864490166566557833818265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445109123553419900454789653 20864490166566557833818265)
          ·
            refine ⟨15648367624924918375363699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20864490166566557833818265 15648367624924918375363699)
            ·
              refine ⟨23472551437387377563045549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648367624924918375363699 23472551437387377563045549)
              ·
                refine ⟨8802206789020266586142081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23472551437387377563045549 8802206789020266586142081)
                ·
                  refine ⟨6601655091765199939606561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802206789020266586142081 6601655091765199939606561)
                  ·
                    refine ⟨4951241318823899954704921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601655091765199939606561 4951241318823899954704921)
                    ·
                      refine ⟨3713430989117924966028691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951241318823899954704921 3713430989117924966028691)
                      ·
                        rfl

theorem cell23_7231881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2, 2].length) (baseStart_7231881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231881 prefixEnd_7231881 := by exact prefixLift 7231881
  have htrace : WordTrace (prefixWord ++ tailWord_7231881) baseStart_7231881 baseEnd_7231881 := by
    simpa [prefixWord, tailWord_7231881, baseEnd_7231881] using wordTrace_append hprefix tailTrace_7231881
  have hstable : (prefixWord ++ tailWord_7231881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231881).length < 2 ^ (prefixWord ++ tailWord_7231881).sum := by decide
  have hdescent : baseEnd_7231881 < baseStart_7231881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231921 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 5]
def baseStart_7231921 : Nat := 118140960795 + 7231921 * 2 ^ 59
def prefixEnd_7231921 : Nat := 4983230072969 + 3 ^ 40 * 7231921 * 2
def baseEnd_7231921 : Nat := 412605725371567201058723

theorem tailTrace_7231921 : CollatzResearch.WordTrace tailWord_7231921 prefixEnd_7231921 412605725371567201058723 := by
  unfold tailWord_7231921
  simp only [CollatzResearch.WordTrace]
  refine ⟨263769828432992805619479617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175846552288661870412986411 263769828432992805619479617)
  ·
    refine ⟨197827371324744604214609713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263769828432992805619479617 197827371324744604214609713)
    ·
      refine ⟨148370528493558453160957285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197827371324744604214609713 148370528493558453160957285)
      ·
        refine ⟨27819474092542209967679491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148370528493558453160957285 27819474092542209967679491)
        ·
          refine ⟨41729211138813314951519237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27819474092542209967679491 41729211138813314951519237)
          ·
            refine ⟨7824227088527496553409857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41729211138813314951519237 7824227088527496553409857)
            ·
              refine ⟨5868170316395622415057393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824227088527496553409857 5868170316395622415057393)
              ·
                refine ⟨4401127737296716811293045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868170316395622415057393 4401127737296716811293045)
                ·
                  refine ⟨412605725371567201058723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4401127737296716811293045 412605725371567201058723)
                  ·
                    rfl

theorem cell23_7231921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 5].length) (baseStart_7231921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231921 prefixEnd_7231921 := by exact prefixLift 7231921
  have htrace : WordTrace (prefixWord ++ tailWord_7231921) baseStart_7231921 baseEnd_7231921 := by
    simpa [prefixWord, tailWord_7231921, baseEnd_7231921] using wordTrace_append hprefix tailTrace_7231921
  have hstable : (prefixWord ++ tailWord_7231921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231921).length < 2 ^ (prefixWord ++ tailWord_7231921).sum := by decide
  have hdescent : baseEnd_7231921 < baseStart_7231921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231960 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 8]
def baseStart_7231960 : Nat := 118140960795 + 7231960 * 2 ^ 59
def prefixEnd_7231960 : Nat := 4983230072969 + 3 ^ 40 * 7231960 * 2
def baseEnd_7231960 : Nat := 412607950454403350771203

theorem tailTrace_7231960 : CollatzResearch.WordTrace tailWord_7231960 prefixEnd_7231960 412607950454403350771203 := by
  unfold tailWord_7231960
  simp only [CollatzResearch.WordTrace]
  refine ⟨131885625439925757640074667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175847500586567676853432889 131885625439925757640074667)
  ·
    refine ⟨197828438159888636460112001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131885625439925757640074667 197828438159888636460112001)
    ·
      refine ⟨148371328619916477345084001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197828438159888636460112001 148371328619916477345084001)
      ·
        refine ⟨111278496464937358008813001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148371328619916477345084001 111278496464937358008813001)
        ·
          refine ⟨83458872348703018506609751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111278496464937358008813001 83458872348703018506609751)
          ·
            refine ⟨125188308523054527759914627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83458872348703018506609751 125188308523054527759914627)
            ·
              refine ⟨187782462784581791639871941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125188308523054527759914627 187782462784581791639871941)
              ·
                refine ⟨35209211772109085932475989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187782462784581791639871941 35209211772109085932475989)
                ·
                  refine ⟨412607950454403350771203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35209211772109085932475989 412607950454403350771203)
                  ·
                    rfl

theorem cell23_7231960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_7231960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231960 prefixEnd_7231960 := by exact prefixLift 7231960
  have htrace : WordTrace (prefixWord ++ tailWord_7231960) baseStart_7231960 baseEnd_7231960 := by
    simpa [prefixWord, tailWord_7231960, baseEnd_7231960] using wordTrace_append hprefix tailTrace_7231960
  have hstable : (prefixWord ++ tailWord_7231960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231960).length < 2 ^ (prefixWord ++ tailWord_7231960).sum := by decide
  have hdescent : baseEnd_7231960 < baseStart_7231960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231980 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7231980 : Nat := 118140960795 + 7231980 * 2 ^ 59
def prefixEnd_7231980 : Nat := 4983230072969 + 3 ^ 40 * 7231980 * 2
def baseEnd_7231980 : Nat := 3713481823702720078690735

theorem tailTrace_7231980 : CollatzResearch.WordTrace tailWord_7231980 prefixEnd_7231980 3713481823702720078690735 := by
  unfold tailWord_7231980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131885990169889529347938697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175847986893186039130584929 131885990169889529347938697)
  ·
    refine ⟨98914492627417147010954023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131885990169889529347938697 98914492627417147010954023)
    ·
      refine ⟨148371738941125720516431035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98914492627417147010954023 148371738941125720516431035)
      ·
        refine ⟨222557608411688580774646553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148371738941125720516431035 222557608411688580774646553)
        ·
          refine ⟨166918206308766435580984915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222557608411688580774646553 166918206308766435580984915)
          ·
            refine ⟨250377309463149653371477373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166918206308766435580984915 250377309463149653371477373)
            ·
              refine ⟨93891491048681120014304015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250377309463149653371477373 93891491048681120014304015)
              ·
                refine ⟨140837236573021680021456023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93891491048681120014304015 140837236573021680021456023)
                ·
                  refine ⟨211255854859532520032184035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140837236573021680021456023 211255854859532520032184035)
                  ·
                    refine ⟨316883782289298780048276053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211255854859532520032184035 316883782289298780048276053)
                    ·
                      refine ⟨3713481823702720078690735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316883782289298780048276053 3713481823702720078690735)
                      ·
                        rfl

theorem cell23_7231980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7231980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231980 prefixEnd_7231980 := by exact prefixLift 7231980
  have htrace : WordTrace (prefixWord ++ tailWord_7231980) baseStart_7231980 baseEnd_7231980 := by
    simpa [prefixWord, tailWord_7231980, baseEnd_7231980] using wordTrace_append hprefix tailTrace_7231980
  have hstable : (prefixWord ++ tailWord_7231980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231980).length < 2 ^ (prefixWord ++ tailWord_7231980).sum := by decide
  have hdescent : baseEnd_7231980 < baseStart_7231980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7231981 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7231981 : Nat := 118140960795 + 7231981 * 2 ^ 59
def prefixEnd_7231981 : Nat := 4983230072969 + 3 ^ 40 * 7231981 * 2
def baseEnd_7231981 : Nat := 1237827445727791524926077

theorem tailTrace_7231981 : CollatzResearch.WordTrace tailWord_7231981 prefixEnd_7231981 1237827445727791524926077 := by
  unfold tailWord_7231981
  simp only [CollatzResearch.WordTrace]
  refine ⟨263772016812775435866663797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175848011208516957244442531 263772016812775435866663797)
  ·
    refine ⟨24728626576197697112499731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263772016812775435866663797 24728626576197697112499731)
    ·
      refine ⟨37092939864296545668749597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24728626576197697112499731 37092939864296545668749597)
      ·
        refine ⟨13909852449111204625781099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37092939864296545668749597 13909852449111204625781099)
        ·
          refine ⟨20864778673666806938671649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909852449111204625781099 20864778673666806938671649)
          ·
            refine ⟨15648584005250105204003737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20864778673666806938671649 15648584005250105204003737)
            ·
              refine ⟨11736438003937578903002803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15648584005250105204003737 11736438003937578903002803)
              ·
                refine ⟨17604657005906368354504205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736438003937578903002803 17604657005906368354504205)
                ·
                  refine ⟨6601746377214888132939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17604657005906368354504205 6601746377214888132939077)
                  ·
                    refine ⟨1237827445727791524926077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601746377214888132939077 1237827445727791524926077)
                    ·
                      rfl

theorem cell23_7231981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7231981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7231981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7231981 prefixEnd_7231981 := by exact prefixLift 7231981
  have htrace : WordTrace (prefixWord ++ tailWord_7231981) baseStart_7231981 baseEnd_7231981 := by
    simpa [prefixWord, tailWord_7231981, baseEnd_7231981] using wordTrace_append hprefix tailTrace_7231981
  have hstable : (prefixWord ++ tailWord_7231981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7231981).length < 2 ^ (prefixWord ++ tailWord_7231981).sum := by decide
  have hdescent : baseEnd_7231981 < baseStart_7231981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7231981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232024 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_7232024 : Nat := 118140960795 + 7232024 * 2 ^ 59
def prefixEnd_7232024 : Nat := 4983230072969 + 3 ^ 40 * 7232024 * 2
def baseEnd_7232024 : Nat := 1237834805617172635513511

theorem tailTrace_7232024 : CollatzResearch.WordTrace tailWord_7232024 prefixEnd_7232024 1237834805617172635513511 := by
  unfold tailWord_7232024
  simp only [CollatzResearch.WordTrace]
  refine ⟨131886792575809827105239563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175849056767746436140319417 131886792575809827105239563)
  ·
    refine ⟨197830188863714740657859345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131886792575809827105239563 197830188863714740657859345)
    ·
      refine ⟨148372641647786055493394509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197830188863714740657859345 148372641647786055493394509)
      ·
        refine ⟨55639740617919770810022941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148372641647786055493394509 55639740617919770810022941)
        ·
          refine ⟨20864902731719914053758603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55639740617919770810022941 20864902731719914053758603)
          ·
            refine ⟨31297354097579871080637905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20864902731719914053758603 31297354097579871080637905)
            ·
              refine ⟨23473015573184903310478429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31297354097579871080637905 23473015573184903310478429)
              ·
                refine ⟨8802380839944338741429411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23473015573184903310478429 8802380839944338741429411)
                ·
                  refine ⟨13203571259916508112144117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802380839944338741429411 13203571259916508112144117)
                  ·
                    refine ⟨1237834805617172635513511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13203571259916508112144117 1237834805617172635513511)
                    ·
                      rfl

theorem cell23_7232024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_7232024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232024 prefixEnd_7232024 := by exact prefixLift 7232024
  have htrace : WordTrace (prefixWord ++ tailWord_7232024) baseStart_7232024 baseEnd_7232024 := by
    simpa [prefixWord, tailWord_7232024, baseEnd_7232024] using wordTrace_append hprefix tailTrace_7232024
  have hstable : (prefixWord ++ tailWord_7232024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232024).length < 2 ^ (prefixWord ++ tailWord_7232024).sum := by decide
  have hdescent : baseEnd_7232024 < baseStart_7232024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232057 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7232057 : Nat := 118140960795 + 7232057 * 2 ^ 59
def prefixEnd_7232057 : Nat := 4983230072969 + 3 ^ 40 * 7232057 * 2
def baseEnd_7232057 : Nat := 3713521361713116277427881

theorem tailTrace_7232057 : CollatzResearch.WordTrace tailWord_7232057 prefixEnd_7232057 3713521361713116277427881 := by
  unfold tailWord_7232057
  simp only [CollatzResearch.WordTrace]
  refine ⟨263774788760500100846430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175849859173666733897620283 263774788760500100846430425)
  ·
    refine ⟨197831091570375075634822819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263774788760500100846430425 197831091570375075634822819)
    ·
      refine ⟨296746637355562613452234229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197831091570375075634822819 296746637355562613452234229)
      ·
        refine ⟨27819997252083995011146959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296746637355562613452234229 27819997252083995011146959)
        ·
          refine ⟨41729995878125992516720439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27819997252083995011146959 41729995878125992516720439)
          ·
            refine ⟨62594993817188988775080659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41729995878125992516720439 62594993817188988775080659)
            ·
              refine ⟨93892490725783483162620989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62594993817188988775080659 93892490725783483162620989)
              ·
                refine ⟨35209684022168806185982871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93892490725783483162620989 35209684022168806185982871)
                ·
                  refine ⟨52814526033253209278974307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35209684022168806185982871 52814526033253209278974307)
                  ·
                    refine ⟨79221789049879813918461461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52814526033253209278974307 79221789049879813918461461)
                    ·
                      refine ⟨3713521361713116277427881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79221789049879813918461461 3713521361713116277427881)
                      ·
                        rfl

theorem cell23_7232057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7232057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232057 prefixEnd_7232057 := by exact prefixLift 7232057
  have htrace : WordTrace (prefixWord ++ tailWord_7232057) baseStart_7232057 baseEnd_7232057 := by
    simpa [prefixWord, tailWord_7232057, baseEnd_7232057] using wordTrace_append hprefix tailTrace_7232057
  have hstable : (prefixWord ++ tailWord_7232057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232057).length < 2 ^ (prefixWord ++ tailWord_7232057).sum := by decide
  have hdescent : baseEnd_7232057 < baseStart_7232057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232061 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_7232061 : Nat := 118140960795 + 7232061 * 2 ^ 59
def prefixEnd_7232061 : Nat := 4983230072969 + 3 ^ 40 * 7232061 * 2
def baseEnd_7232061 : Nat := 3713523415635734261777863

theorem tailTrace_7232061 : CollatzResearch.WordTrace tailWord_7232061 prefixEnd_7232061 3713523415635734261777863 := by
  unfold tailWord_7232061
  simp only [CollatzResearch.WordTrace]
  refine ⟨263774934652485609529576037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175849956434990406353050691 263774934652485609529576037)
  ·
    refine ⟨49457800247341051786795507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263774934652485609529576037 49457800247341051786795507)
    ·
      refine ⟨74186700371011577680193261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49457800247341051786795507 74186700371011577680193261)
      ·
        refine ⟨27820012639129341630072473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74186700371011577680193261 27820012639129341630072473)
        ·
          refine ⟨20865009479347006222554355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27820012639129341630072473 20865009479347006222554355)
          ·
            refine ⟨31297514219020509333831533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20865009479347006222554355 31297514219020509333831533)
            ·
              refine ⟨11736567832132691000186825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31297514219020509333831533 11736567832132691000186825)
              ·
                refine ⟨8802425874099518250140119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11736567832132691000186825 8802425874099518250140119)
                ·
                  refine ⟨13203638811149277375210179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802425874099518250140119 13203638811149277375210179)
                  ·
                    refine ⟨19805458216723916062815269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203638811149277375210179 19805458216723916062815269)
                    ·
                      refine ⟨3713523415635734261777863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805458216723916062815269 3713523415635734261777863)
                      ·
                        rfl

theorem cell23_7232061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_7232061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232061 prefixEnd_7232061 := by exact prefixLift 7232061
  have htrace : WordTrace (prefixWord ++ tailWord_7232061) baseStart_7232061 baseEnd_7232061 := by
    simpa [prefixWord, tailWord_7232061, baseEnd_7232061] using wordTrace_append hprefix tailTrace_7232061
  have hstable : (prefixWord ++ tailWord_7232061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232061).length < 2 ^ (prefixWord ++ tailWord_7232061).sum := by decide
  have hdescent : baseEnd_7232061 < baseStart_7232061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232074 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_7232074 : Nat := 118140960795 + 7232074 * 2 ^ 59
def prefixEnd_7232074 : Nat := 4983230072969 + 3 ^ 40 * 7232074 * 2
def baseEnd_7232074 : Nat := 3713530090884242710915303

theorem tailTrace_7232074 : CollatzResearch.WordTrace tailWord_7232074 prefixEnd_7232074 3713530090884242710915303 := by
  unfold tailWord_7232074
  simp only [CollatzResearch.WordTrace]
  refine ⟨65943852200359628187449819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175850272534292341833199517 65943852200359628187449819)
  ·
    refine ⟨98915778300539442281174729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65943852200359628187449819 98915778300539442281174729)
    ·
      refine ⟨74186833725404581710881047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98915778300539442281174729 74186833725404581710881047)
      ·
        refine ⟨111280250588106872566321571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74186833725404581710881047 111280250588106872566321571)
        ·
          refine ⟨166920375882160308849482357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111280250588106872566321571 166920375882160308849482357)
          ·
            refine ⟨15648785238952528954638971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166920375882160308849482357 15648785238952528954638971)
            ·
              refine ⟨23473177858428793431958457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648785238952528954638971 23473177858428793431958457)
              ·
                refine ⟨17604883393821595073968843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23473177858428793431958457 17604883393821595073968843)
                ·
                  refine ⟨26407325090732392610953265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17604883393821595073968843 26407325090732392610953265)
                  ·
                    refine ⟨19805493818049294458214949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26407325090732392610953265 19805493818049294458214949)
                    ·
                      refine ⟨3713530090884242710915303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805493818049294458214949 3713530090884242710915303)
                      ·
                        rfl

theorem cell23_7232074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_7232074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232074 prefixEnd_7232074 := by exact prefixLift 7232074
  have htrace : WordTrace (prefixWord ++ tailWord_7232074) baseStart_7232074 baseEnd_7232074 := by
    simpa [prefixWord, tailWord_7232074, baseEnd_7232074] using wordTrace_append hprefix tailTrace_7232074
  have hstable : (prefixWord ++ tailWord_7232074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232074).length < 2 ^ (prefixWord ++ tailWord_7232074).sum := by decide
  have hdescent : baseEnd_7232074 < baseStart_7232074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232097 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7232097 : Nat := 118140960795 + 7232097 * 2 ^ 59
def prefixEnd_7232097 : Nat := 4983230072969 + 3 ^ 40 * 7232097 * 2
def baseEnd_7232097 : Nat := 1237847300313098706975899

theorem tailTrace_7232097 : CollatzResearch.WordTrace tailWord_7232097 prefixEnd_7232097 1237847300313098706975899 := by
  unfold tailWord_7232097
  simp only [CollatzResearch.WordTrace]
  refine ⟨263776247680355187677886545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175850831786903458451924363 263776247680355187677886545)
  ·
    refine ⟨197832185760266390758414909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263776247680355187677886545 197832185760266390758414909)
    ·
      refine ⟨74187069660099896534405591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197832185760266390758414909 74187069660099896534405591)
      ·
        refine ⟨111280604490149844801608387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74187069660099896534405591 111280604490149844801608387)
        ·
          refine ⟨166920906735224767202412581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111280604490149844801608387 166920906735224767202412581)
          ·
            refine ⟨31297670012854643850452359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166920906735224767202412581 31297670012854643850452359)
            ·
              refine ⟨46946505019281965775678539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31297670012854643850452359 46946505019281965775678539)
              ·
                refine ⟨70419757528922948663517809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46946505019281965775678539 70419757528922948663517809)
                ·
                  refine ⟨52814818146692211497638357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70419757528922948663517809 52814818146692211497638357)
                  ·
                    refine ⟨1237847300313098706975899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52814818146692211497638357 1237847300313098706975899)
                    ·
                      rfl

theorem cell23_7232097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7232097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232097 prefixEnd_7232097 := by exact prefixLift 7232097
  have htrace : WordTrace (prefixWord ++ tailWord_7232097) baseStart_7232097 baseEnd_7232097 := by
    simpa [prefixWord, tailWord_7232097, baseEnd_7232097] using wordTrace_append hprefix tailTrace_7232097
  have hstable : (prefixWord ++ tailWord_7232097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232097).length < 2 ^ (prefixWord ++ tailWord_7232097).sum := by decide
  have hdescent : baseEnd_7232097 < baseStart_7232097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232101 : List Nat := [1, 3, 1, 3, 5, 1, 1, 8]
def baseStart_7232101 : Nat := 118140960795 + 7232101 * 2 ^ 59
def prefixEnd_7232101 : Nat := 4983230072969 + 3 ^ 40 * 7232101 * 2
def baseEnd_7232101 : Nat := 137538664994885707602877

theorem tailTrace_7232101 : CollatzResearch.WordTrace tailWord_7232101 prefixEnd_7232101 137538664994885707602877 := by
  unfold tailWord_7232101
  simp only [CollatzResearch.WordTrace]
  refine ⟨263776393572340696361032157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175850929048227130907354771 263776393572340696361032157)
  ·
    refine ⟨98916147589627761135387059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263776393572340696361032157 98916147589627761135387059)
    ·
      refine ⟨148374221384441641703080589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98916147589627761135387059 148374221384441641703080589)
      ·
        refine ⟨55640333019165615638655221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148374221384441641703080589 55640333019165615638655221)
        ·
          refine ⟨5216281220546776466123927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55640333019165615638655221 5216281220546776466123927)
          ·
            refine ⟨7824421830820164699185891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216281220546776466123927 7824421830820164699185891)
            ·
              refine ⟨11736632746230247048778837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824421830820164699185891 11736632746230247048778837)
              ·
                refine ⟨137538664994885707602877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11736632746230247048778837 137538664994885707602877)
                ·
                  rfl

theorem cell23_7232101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 8].length) (baseStart_7232101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232101 prefixEnd_7232101 := by exact prefixLift 7232101
  have htrace : WordTrace (prefixWord ++ tailWord_7232101) baseStart_7232101 baseEnd_7232101 := by
    simpa [prefixWord, tailWord_7232101, baseEnd_7232101] using wordTrace_append hprefix tailTrace_7232101
  have hstable : (prefixWord ++ tailWord_7232101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232101).length < 2 ^ (prefixWord ++ tailWord_7232101).sum := by decide
  have hdescent : baseEnd_7232101 < baseStart_7232101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232111 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_7232111 : Nat := 118140960795 + 7232111 * 2 ^ 59
def prefixEnd_7232111 : Nat := 4983230072969 + 3 ^ 40 * 7232111 * 2
def baseEnd_7232111 : Nat := 3713549089668459066152633

theorem tailTrace_7232111 : CollatzResearch.WordTrace tailWord_7232111 prefixEnd_7232111 3713549089668459066152633 := by
  unfold tailWord_7232111
  simp only [CollatzResearch.WordTrace]
  refine ⟨263776758302304468068896187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175851172201536312045930791 263776758302304468068896187)
  ·
    refine ⟨395665137453456702103344281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263776758302304468068896187 395665137453456702103344281)
    ·
      refine ⟨296748853090092526577508211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395665137453456702103344281 296748853090092526577508211)
      ·
        refine ⟨445123279635138789866262317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296748853090092526577508211 445123279635138789866262317)
        ·
          refine ⟨166921229863177046199848369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445123279635138789866262317 166921229863177046199848369)
          ·
            refine ⟨125190922397382784649886277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166921229863177046199848369 125190922397382784649886277)
            ·
              refine ⟨23473297949509272121853677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125190922397382784649886277 23473297949509272121853677)
              ·
                refine ⟨8802486731065977045695129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23473297949509272121853677 8802486731065977045695129)
                ·
                  refine ⟨6601865048299482784271347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802486731065977045695129 6601865048299482784271347)
                  ·
                    refine ⟨9902797572449224176407021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6601865048299482784271347 9902797572449224176407021)
                    ·
                      refine ⟨3713549089668459066152633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9902797572449224176407021 3713549089668459066152633)
                      ·
                        rfl

theorem cell23_7232111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_7232111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232111 prefixEnd_7232111 := by exact prefixLift 7232111
  have htrace : WordTrace (prefixWord ++ tailWord_7232111) baseStart_7232111 baseEnd_7232111 := by
    simpa [prefixWord, tailWord_7232111, baseEnd_7232111] using wordTrace_append hprefix tailTrace_7232111
  have hstable : (prefixWord ++ tailWord_7232111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232111).length < 2 ^ (prefixWord ++ tailWord_7232111).sum := by decide
  have hdescent : baseEnd_7232111 < baseStart_7232111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232121 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 3, 3, 2]
def baseStart_7232121 : Nat := 118140960795 + 7232121 * 2 ^ 59
def prefixEnd_7232121 : Nat := 4983230072969 + 3 ^ 40 * 7232121 * 2
def baseEnd_7232121 : Nat := 3713554224475004027027587

theorem tailTrace_7232121 : CollatzResearch.WordTrace tailWord_7232121 prefixEnd_7232121 3713554224475004027027587 := by
  unfold tailWord_7232121
  simp only [CollatzResearch.WordTrace]
  refine ⟨263777123032268239776760217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175851415354845493184506811 263777123032268239776760217)
  ·
    refine ⟨197832842274201179832570163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263777123032268239776760217 197832842274201179832570163)
    ·
      refine ⟨296749263411301769748855245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197832842274201179832570163 296749263411301769748855245)
      ·
        refine ⟨111280973779238163655820717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296749263411301769748855245 111280973779238163655820717)
        ·
          refine ⟨41730365167214311370932769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111280973779238163655820717 41730365167214311370932769)
          ·
            refine ⟨31297773875410733528199577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41730365167214311370932769 31297773875410733528199577)
            ·
              refine ⟨23473330406558050146149683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31297773875410733528199577 23473330406558050146149683)
              ·
                refine ⟨35209995609837075219224525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23473330406558050146149683 35209995609837075219224525)
                ·
                  refine ⟨13203748353688903207209197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35209995609837075219224525 13203748353688903207209197)
                  ·
                    refine ⟨4951405632633338702703449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13203748353688903207209197 4951405632633338702703449)
                    ·
                      refine ⟨3713554224475004027027587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951405632633338702703449 3713554224475004027027587)
                      ·
                        rfl

theorem cell23_7232121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_7232121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232121 prefixEnd_7232121 := by exact prefixLift 7232121
  have htrace : WordTrace (prefixWord ++ tailWord_7232121) baseStart_7232121 baseEnd_7232121 := by
    simpa [prefixWord, tailWord_7232121, baseEnd_7232121] using wordTrace_append hprefix tailTrace_7232121
  have hstable : (prefixWord ++ tailWord_7232121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232121).length < 2 ^ (prefixWord ++ tailWord_7232121).sum := by decide
  have hdescent : baseEnd_7232121 < baseStart_7232121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232137 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_7232137 : Nat := 118140960795 + 7232137 * 2 ^ 59
def prefixEnd_7232137 : Nat := 4983230072969 + 3 ^ 40 * 7232137 * 2
def baseEnd_7232137 : Nat := 3713562440165475964427513

theorem tailTrace_7232137 : CollatzResearch.WordTrace tailWord_7232137 prefixEnd_7232137 3713562440165475964427513 := by
  unfold tailWord_7232137
  simp only [CollatzResearch.WordTrace]
  refine ⟨263777706600210274509342665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175851804400140183006228443 263777706600210274509342665)
  ·
    refine ⟨197833279950157705882006999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263777706600210274509342665 197833279950157705882006999)
    ·
      refine ⟨296749919925236558823010499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197833279950157705882006999 296749919925236558823010499)
      ·
        refine ⟨445124879887854838234515749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296749919925236558823010499 445124879887854838234515749)
        ·
          refine ⟨83460914978972782168971703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445124879887854838234515749 83460914978972782168971703)
          ·
            refine ⟨125191372468459173253457555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83460914978972782168971703 125191372468459173253457555)
            ·
              refine ⟨187787058702688759880186333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125191372468459173253457555 187787058702688759880186333)
              ·
                refine ⟨70420147013508284955069875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187787058702688759880186333 70420147013508284955069875)
                ·
                  refine ⟨105630220520262427432604813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70420147013508284955069875 105630220520262427432604813)
                  ·
                    refine ⟨39611332695098410287226805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105630220520262427432604813 39611332695098410287226805)
                    ·
                      refine ⟨3713562440165475964427513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39611332695098410287226805 3713562440165475964427513)
                      ·
                        rfl

theorem cell23_7232137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_7232137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232137 prefixEnd_7232137 := by exact prefixLift 7232137
  have htrace : WordTrace (prefixWord ++ tailWord_7232137) baseStart_7232137 baseEnd_7232137 := by
    simpa [prefixWord, tailWord_7232137, baseEnd_7232137] using wordTrace_append hprefix tailTrace_7232137
  have hstable : (prefixWord ++ tailWord_7232137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232137).length < 2 ^ (prefixWord ++ tailWord_7232137).sum := by decide
  have hdescent : baseEnd_7232137 < baseStart_7232137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232147 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_7232147 : Nat := 118140960795 + 7232147 * 2 ^ 59
def prefixEnd_7232147 : Nat := 4983230072969 + 3 ^ 40 * 7232147 * 2
def baseEnd_7232147 : Nat := 3713567574972020925302467

theorem tailTrace_7232147 : CollatzResearch.WordTrace tailWord_7232147 prefixEnd_7232147 3713567574972020925302467 := by
  unfold tailWord_7232147
  simp only [CollatzResearch.WordTrace]
  refine ⟨263778071330174046217206695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175852047553449364144804463 263778071330174046217206695)
  ·
    refine ⟨395667106995261069325810043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263778071330174046217206695 395667106995261069325810043)
    ·
      refine ⟨593500660492891603988715065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395667106995261069325810043 593500660492891603988715065)
      ·
        refine ⟨445125495369668702991536299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593500660492891603988715065 445125495369668702991536299)
        ·
          refine ⟨667688243054503054487304449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445125495369668702991536299 667688243054503054487304449)
          ·
            refine ⟨500766182290877290865478337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667688243054503054487304449 500766182290877290865478337)
            ·
              refine ⟨375574636718157968149108753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500766182290877290865478337 375574636718157968149108753)
              ·
                refine ⟨281680977538618476111831565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375574636718157968149108753 281680977538618476111831565)
                ·
                  refine ⟨105630366576981928541936837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281680977538618476111831565 105630366576981928541936837)
                  ·
                    refine ⟨19805693733184111601613157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105630366576981928541936837 19805693733184111601613157)
                    ·
                      refine ⟨3713567574972020925302467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805693733184111601613157 3713567574972020925302467)
                      ·
                        rfl

theorem cell23_7232147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_7232147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232147 prefixEnd_7232147 := by exact prefixLift 7232147
  have htrace : WordTrace (prefixWord ++ tailWord_7232147) baseStart_7232147 baseEnd_7232147 := by
    simpa [prefixWord, tailWord_7232147, baseEnd_7232147] using wordTrace_append hprefix tailTrace_7232147
  have hstable : (prefixWord ++ tailWord_7232147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232147).length < 2 ^ (prefixWord ++ tailWord_7232147).sum := by decide
  have hdescent : baseEnd_7232147 < baseStart_7232147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232164 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7232164 : Nat := 118140960795 + 7232164 * 2 ^ 59
def prefixEnd_7232164 : Nat := 4983230072969 + 3 ^ 40 * 7232164 * 2
def baseEnd_7232164 : Nat := 3713576304143147358789889

theorem tailTrace_7232164 : CollatzResearch.WordTrace tailWord_7232164 prefixEnd_7232164 3713576304143147358789889 := by
  unfold tailWord_7232164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131889345685556229060287773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175852460914074972080383697 131889345685556229060287773)
  ·
    refine ⟨49458504632083585897607915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131889345685556229060287773 49458504632083585897607915)
    ·
      refine ⟨74187756948125378846411873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49458504632083585897607915 74187756948125378846411873)
      ·
        refine ⟨55640817711094034134808905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74187756948125378846411873 55640817711094034134808905)
        ·
          refine ⟨41730613283320525601106679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55640817711094034134808905 41730613283320525601106679)
          ·
            refine ⟨62595919924980788401660019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41730613283320525601106679 62595919924980788401660019)
            ·
              refine ⟨93893879887471182602490029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62595919924980788401660019 93893879887471182602490029)
              ·
                refine ⟨35210204957801693475933761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93893879887471182602490029 35210204957801693475933761)
                ·
                  refine ⟨26407653718351270106950321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35210204957801693475933761 26407653718351270106950321)
                  ·
                    refine ⟨19805740288763452580212741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26407653718351270106950321 19805740288763452580212741)
                    ·
                      refine ⟨3713576304143147358789889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805740288763452580212741 3713576304143147358789889)
                      ·
                        rfl

theorem cell23_7232164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7232164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232164 prefixEnd_7232164 := by exact prefixLift 7232164
  have htrace : WordTrace (prefixWord ++ tailWord_7232164) baseStart_7232164 baseEnd_7232164 := by
    simpa [prefixWord, tailWord_7232164, baseEnd_7232164] using wordTrace_append hprefix tailTrace_7232164
  have hstable : (prefixWord ++ tailWord_7232164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232164).length < 2 ^ (prefixWord ++ tailWord_7232164).sum := by decide
  have hdescent : baseEnd_7232164 < baseStart_7232164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232191 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 5]
def baseStart_7232191 : Nat := 118140960795 + 7232191 * 2 ^ 59
def prefixEnd_7232191 : Nat := 4983230072969 + 3 ^ 40 * 7232191 * 2
def baseEnd_7232191 : Nat := 412621129791202083683585

theorem tailTrace_7232191 : CollatzResearch.WordTrace tailWord_7232191 prefixEnd_7232191 412621129791202083683585 := by
  unfold tailWord_7232191
  simp only [CollatzResearch.WordTrace]
  refine ⟨263779676142014641731808427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175853117428009761154538951 263779676142014641731808427)
  ·
    refine ⟨395669514213021962597712641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263779676142014641731808427 395669514213021962597712641)
    ·
      refine ⟨296752135659766471948284481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395669514213021962597712641 296752135659766471948284481)
      ·
        refine ⟨222564101744824853961213361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296752135659766471948284481 222564101744824853961213361)
        ·
          refine ⟨166923076308618640470910021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222564101744824853961213361 166923076308618640470910021)
          ·
            refine ⟨31298076807865995088295629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166923076308618640470910021 31298076807865995088295629)
            ·
              refine ⟨11736778802949748158110861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31298076807865995088295629 11736778802949748158110861)
              ·
                refine ⟨4401292051106155559291573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11736778802949748158110861 4401292051106155559291573)
                ·
                  refine ⟨412621129791202083683585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4401292051106155559291573 412621129791202083683585)
                  ·
                    rfl

theorem cell23_7232191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 5].length) (baseStart_7232191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232191 prefixEnd_7232191 := by exact prefixLift 7232191
  have htrace : WordTrace (prefixWord ++ tailWord_7232191) baseStart_7232191 baseEnd_7232191 := by
    simpa [prefixWord, tailWord_7232191, baseEnd_7232191] using wordTrace_append hprefix tailTrace_7232191
  have hstable : (prefixWord ++ tailWord_7232191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232191).length < 2 ^ (prefixWord ++ tailWord_7232191).sum := by decide
  have hdescent : baseEnd_7232191 < baseStart_7232191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232207 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_7232207 : Nat := 118140960795 + 7232207 * 2 ^ 59
def prefixEnd_7232207 : Nat := 4983230072969 + 3 ^ 40 * 7232207 * 2
def baseEnd_7232207 : Nat := 3713598383811290690552191

theorem tailTrace_7232207 : CollatzResearch.WordTrace tailWord_7232207 prefixEnd_7232207 3713598383811290690552191 := by
  unfold tailWord_7232207
  simp only [CollatzResearch.WordTrace]
  refine ⟨263780259709956676464390875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175853506473304450976260583 263780259709956676464390875)
  ·
    refine ⟨395670389564935014696586313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263780259709956676464390875 395670389564935014696586313)
    ·
      refine ⟨296752792173701261022439735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395670389564935014696586313 296752792173701261022439735)
      ·
        refine ⟨445129188260551891533659603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296752792173701261022439735 445129188260551891533659603)
        ·
          refine ⟨667693782390827837300489405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445129188260551891533659603 667693782390827837300489405)
          ·
            refine ⟨250385168396560438987683527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667693782390827837300489405 250385168396560438987683527)
            ·
              refine ⟨375577752594840658481525291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250385168396560438987683527 375577752594840658481525291)
              ·
                refine ⟨563366628892260987722287937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375577752594840658481525291 563366628892260987722287937)
                ·
                  refine ⟨422524971669195740791715953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563366628892260987722287937 422524971669195740791715953)
                  ·
                    refine ⟨316893728751896805593786965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422524971669195740791715953 316893728751896805593786965)
                    ·
                      refine ⟨3713598383811290690552191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316893728751896805593786965 3713598383811290690552191)
                      ·
                        rfl

theorem cell23_7232207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_7232207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232207 prefixEnd_7232207 := by exact prefixLift 7232207
  have htrace : WordTrace (prefixWord ++ tailWord_7232207) baseStart_7232207 baseEnd_7232207 := by
    simpa [prefixWord, tailWord_7232207, baseEnd_7232207] using wordTrace_append hprefix tailTrace_7232207
  have hstable : (prefixWord ++ tailWord_7232207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232207).length < 2 ^ (prefixWord ++ tailWord_7232207).sum := by decide
  have hdescent : baseEnd_7232207 < baseStart_7232207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232224 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_7232224 : Nat := 118140960795 + 7232224 * 2 ^ 59
def prefixEnd_7232224 : Nat := 4983230072969 + 3 ^ 40 * 7232224 * 2
def baseEnd_7232224 : Nat := 3713607112982417124039613

theorem tailTrace_7232224 : CollatzResearch.WordTrace tailWord_7232224 prefixEnd_7232224 3713607112982417124039613 := by
  unfold tailWord_7232224
  simp only [CollatzResearch.WordTrace]
  refine ⟨131890439875447544183879863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175853919833930058911839817 131890439875447544183879863)
  ·
    refine ⟨197835659813171316275819795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131890439875447544183879863 197835659813171316275819795)
    ·
      refine ⟨296753489719756974413729693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197835659813171316275819795 296753489719756974413729693)
      ·
        refine ⟨111282558644908865405148635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296753489719756974413729693 111282558644908865405148635)
        ·
          refine ⟨166923837967363298107722953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111282558644908865405148635 166923837967363298107722953)
          ·
            refine ⟨125192878475522473580792215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166923837967363298107722953 125192878475522473580792215)
            ·
              refine ⟨187789317713283710371188323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125192878475522473580792215 187789317713283710371188323)
              ·
                refine ⟨281683976569925565556782485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187789317713283710371188323 281683976569925565556782485)
                ·
                  refine ⟨13203936401715260885474179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281683976569925565556782485 13203936401715260885474179)
                  ·
                    refine ⟨19805904602572891328211269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203936401715260885474179 19805904602572891328211269)
                    ·
                      refine ⟨3713607112982417124039613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805904602572891328211269 3713607112982417124039613)
                      ·
                        rfl

theorem cell23_7232224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_7232224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232224 prefixEnd_7232224 := by exact prefixLift 7232224
  have htrace : WordTrace (prefixWord ++ tailWord_7232224) baseStart_7232224 baseEnd_7232224 := by
    simpa [prefixWord, tailWord_7232224, baseEnd_7232224] using wordTrace_append hprefix tailTrace_7232224
  have hstable : (prefixWord ++ tailWord_7232224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232224).length < 2 ^ (prefixWord ++ tailWord_7232224).sum := by decide
  have hdescent : baseEnd_7232224 < baseStart_7232224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232241 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_7232241 : Nat := 118140960795 + 7232241 * 2 ^ 59
def prefixEnd_7232241 : Nat := 4983230072969 + 3 ^ 40 * 7232241 * 2
def baseEnd_7232241 : Nat := 3713615842153543557527035

theorem tailTrace_7232241 : CollatzResearch.WordTrace tailWord_7232241 prefixEnd_7232241 3713615842153543557527035 := by
  unfold tailWord_7232241
  simp only [CollatzResearch.WordTrace]
  refine ⟨263781499791833500271128577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175854333194555666847419051 263781499791833500271128577)
  ·
    refine ⟨197836124843875125203346433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263781499791833500271128577 197836124843875125203346433)
    ·
      refine ⟨148377093632906343902509825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197836124843875125203346433 148377093632906343902509825)
      ·
        refine ⟨111282820224679757926882369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148377093632906343902509825 111282820224679757926882369)
        ·
          refine ⟨83462115168509818445161777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111282820224679757926882369 83462115168509818445161777)
          ·
            refine ⟨62596586376382363833871333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83462115168509818445161777 62596586376382363833871333)
            ·
              refine ⟨11736859945571693218850875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62596586376382363833871333 11736859945571693218850875)
              ·
                refine ⟨17605289918357539828276313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736859945571693218850875 17605289918357539828276313)
                ·
                  refine ⟨13203967438768154871207235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17605289918357539828276313 13203967438768154871207235)
                  ·
                    refine ⟨19805951158152232306810853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203967438768154871207235 19805951158152232306810853)
                    ·
                      refine ⟨3713615842153543557527035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805951158152232306810853 3713615842153543557527035)
                      ·
                        rfl

theorem cell23_7232241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_7232241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232241 prefixEnd_7232241 := by exact prefixLift 7232241
  have htrace : WordTrace (prefixWord ++ tailWord_7232241) baseStart_7232241 baseEnd_7232241 := by
    simpa [prefixWord, tailWord_7232241, baseEnd_7232241] using wordTrace_append hprefix tailTrace_7232241
  have hstable : (prefixWord ++ tailWord_7232241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232241).length < 2 ^ (prefixWord ++ tailWord_7232241).sum := by decide
  have hdescent : baseEnd_7232241 < baseStart_7232241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232258 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7232258 : Nat := 118140960795 + 7232258 * 2 ^ 59
def prefixEnd_7232258 : Nat := 4983230072969 + 3 ^ 40 * 7232258 * 2
def baseEnd_7232258 : Nat := 3713624571324669991014457

theorem tailTrace_7232258 : CollatzResearch.WordTrace tailWord_7232258 prefixEnd_7232258 3713624571324669991014457 := by
  unfold tailWord_7232258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65945529958192978043624357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175854746555181274782998285 65945529958192978043624357)
  ·
    refine ⟨12364786867161183383179567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65945529958192978043624357 12364786867161183383179567)
    ·
      refine ⟨18547180300741775074769351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12364786867161183383179567 18547180300741775074769351)
      ·
        refine ⟨27820770451112662612154027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18547180300741775074769351 27820770451112662612154027)
        ·
          refine ⟨41731155676668993918231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27820770451112662612154027 41731155676668993918231041)
          ·
            refine ⟨31298366757501745438673281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41731155676668993918231041 31298366757501745438673281)
            ·
              refine ⟨23473775068126309079004961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31298366757501745438673281 23473775068126309079004961)
              ·
                refine ⟨17605331301094731809253721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23473775068126309079004961 17605331301094731809253721)
                ·
                  refine ⟨13203998475821048856940291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17605331301094731809253721 13203998475821048856940291)
                  ·
                    refine ⟨19805997713731573285410437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203998475821048856940291 19805997713731573285410437)
                    ·
                      refine ⟨3713624571324669991014457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19805997713731573285410437 3713624571324669991014457)
                      ·
                        rfl

theorem cell23_7232258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7232258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232258 prefixEnd_7232258 := by exact prefixLift 7232258
  have htrace : WordTrace (prefixWord ++ tailWord_7232258) baseStart_7232258 baseEnd_7232258 := by
    simpa [prefixWord, tailWord_7232258, baseEnd_7232258] using wordTrace_append hprefix tailTrace_7232258
  have hstable : (prefixWord ++ tailWord_7232258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232258).length < 2 ^ (prefixWord ++ tailWord_7232258).sum := by decide
  have hdescent : baseEnd_7232258 < baseStart_7232258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232285 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_7232285 : Nat := 118140960795 + 7232285 * 2 ^ 59
def prefixEnd_7232285 : Nat := 4983230072969 + 3 ^ 40 * 7232285 * 2
def baseEnd_7232285 : Nat := 1237879478434113795125611

theorem tailTrace_7232285 : CollatzResearch.WordTrace tailWord_7232285 prefixEnd_7232285 1237879478434113795125611 := by
  unfold tailWord_7232285
  simp only [CollatzResearch.WordTrace]
  refine ⟨263783104603674095785730309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175855403069116063857153539 263783104603674095785730309)
  ·
    refine ⟨49459332113188892959824433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263783104603674095785730309 49459332113188892959824433)
    ·
      refine ⟨37094499084891669719868325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49459332113188892959824433 37094499084891669719868325)
      ·
        refine ⟨6955218578417188072475311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37094499084891669719868325 6955218578417188072475311)
        ·
          refine ⟨10432827867625782108712967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955218578417188072475311 10432827867625782108712967)
          ·
            refine ⟨15649241801438673163069451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432827867625782108712967 15649241801438673163069451)
            ·
              refine ⟨23473862702158009744604177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15649241801438673163069451 23473862702158009744604177)
              ·
                refine ⟨17605397026618507308453133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23473862702158009744604177 17605397026618507308453133)
                ·
                  refine ⟨6602023884981940240669925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17605397026618507308453133 6602023884981940240669925)
                  ·
                    refine ⟨1237879478434113795125611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602023884981940240669925 1237879478434113795125611)
                    ·
                      rfl

theorem cell23_7232285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_7232285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232285 prefixEnd_7232285 := by exact prefixLift 7232285
  have htrace : WordTrace (prefixWord ++ tailWord_7232285) baseStart_7232285 baseEnd_7232285 := by
    simpa [prefixWord, tailWord_7232285, baseEnd_7232285] using wordTrace_append hprefix tailTrace_7232285
  have hstable : (prefixWord ++ tailWord_7232285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232285).length < 2 ^ (prefixWord ++ tailWord_7232285).sum := by decide
  have hdescent : baseEnd_7232285 < baseStart_7232285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232302 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7232302 : Nat := 118140960795 + 7232302 * 2 ^ 59
def prefixEnd_7232302 : Nat := 4983230072969 + 3 ^ 40 * 7232302 * 2
def baseEnd_7232302 : Nat := 1237882388157822606288085

theorem tailTrace_7232302 : CollatzResearch.WordTrace tailWord_7232302 prefixEnd_7232302 1237882388157822606288085 := by
  unfold tailWord_7232302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32972965580576563461137395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175855816429741671792732773 32972965580576563461137395)
  ·
    refine ⟨49459448370864845191706093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32972965580576563461137395 49459448370864845191706093)
    ·
      refine ⟨18547293139074316946889785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49459448370864845191706093 18547293139074316946889785)
      ·
        refine ⟨13910469854305737710167339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18547293139074316946889785 13910469854305737710167339)
        ·
          refine ⟨20865704781458606565251009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910469854305737710167339 20865704781458606565251009)
          ·
            refine ⟨15649278586093954923938257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20865704781458606565251009 15649278586093954923938257)
            ·
              refine ⟨11736958939570466192953693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15649278586093954923938257 11736958939570466192953693)
              ·
                refine ⟨4401359602338924822357635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11736958939570466192953693 4401359602338924822357635)
                ·
                  refine ⟨6602039403508387233536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401359602338924822357635 6602039403508387233536453)
                  ·
                    refine ⟨1237882388157822606288085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602039403508387233536453 1237882388157822606288085)
                    ·
                      rfl

theorem cell23_7232302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7232302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232302 prefixEnd_7232302 := by exact prefixLift 7232302
  have htrace : WordTrace (prefixWord ++ tailWord_7232302) baseStart_7232302 baseEnd_7232302 := by
    simpa [prefixWord, tailWord_7232302, baseEnd_7232302] using wordTrace_append hprefix tailTrace_7232302
  have hstable : (prefixWord ++ tailWord_7232302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232302).length < 2 ^ (prefixWord ++ tailWord_7232302).sum := by decide
  have hdescent : baseEnd_7232302 < baseStart_7232302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232311 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 1, 5]
def baseStart_7232311 : Nat := 118140960795 + 7232311 * 2 ^ 59
def prefixEnd_7232311 : Nat := 4983230072969 + 3 ^ 40 * 7232311 * 2
def baseEnd_7232311 : Nat := 1237883928599786094550571

theorem tailTrace_7232311 : CollatzResearch.WordTrace tailWord_7232311 prefixEnd_7232311 1237883928599786094550571 := by
  unfold tailWord_7232311
  simp only [CollatzResearch.WordTrace]
  refine ⟨263784052901579902226176787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175856035267719934817451191 263784052901579902226176787)
  ·
    refine ⟨395676079352369853339265181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263784052901579902226176787 395676079352369853339265181)
    ·
      refine ⟨148378529757138695002224443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395676079352369853339265181 148378529757138695002224443)
      ·
        refine ⟨222567794635708042503336665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148378529757138695002224443 222567794635708042503336665)
        ·
          refine ⟨166925845976781031877502499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222567794635708042503336665 166925845976781031877502499)
          ·
            refine ⟨250388768965171547816253749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166925845976781031877502499 250388768965171547816253749)
            ·
              refine ⟨23473947090484832607773789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250388768965171547816253749 23473947090484832607773789)
              ·
                refine ⟨8802730158931812227915171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23473947090484832607773789 8802730158931812227915171)
                ·
                  refine ⟨13204095238397718341872757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802730158931812227915171 13204095238397718341872757)
                  ·
                    refine ⟨1237883928599786094550571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13204095238397718341872757 1237883928599786094550571)
                    ·
                      rfl

theorem cell23_7232311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_7232311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232311 prefixEnd_7232311 := by exact prefixLift 7232311
  have htrace : WordTrace (prefixWord ++ tailWord_7232311) baseStart_7232311 baseEnd_7232311 := by
    simpa [prefixWord, tailWord_7232311, baseEnd_7232311] using wordTrace_append hprefix tailTrace_7232311
  have hstable : (prefixWord ++ tailWord_7232311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232311).length < 2 ^ (prefixWord ++ tailWord_7232311).sum := by decide
  have hdescent : baseEnd_7232311 < baseStart_7232311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232368 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_7232368 : Nat := 118140960795 + 7232368 * 2 ^ 59
def prefixEnd_7232368 : Nat := 4983230072969 + 3 ^ 40 * 7232368 * 2
def baseEnd_7232368 : Nat := 3713681054196664560638951

theorem tailTrace_7232368 : CollatzResearch.WordTrace tailWord_7232368 prefixEnd_7232368 3713681054196664560638951 := by
  unfold tailWord_7232368
  simp only [CollatzResearch.WordTrace]
  refine ⟨131893065931186700480500879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175857421241582267307334505 131893065931186700480500879)
  ·
    refine ⟨197839598896780050720751319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131893065931186700480500879 197839598896780050720751319)
    ·
      refine ⟨296759398345170076081126979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197839598896780050720751319 296759398345170076081126979)
      ·
        refine ⟨445139097517755114121690469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296759398345170076081126979 445139097517755114121690469)
        ·
          refine ⟨83463580784579083897816963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445139097517755114121690469 83463580784579083897816963)
          ·
            refine ⟨125195371176868625846725445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83463580784579083897816963 125195371176868625846725445)
            ·
              refine ⟨23474132095662867346261021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125195371176868625846725445 23474132095662867346261021)
              ·
                refine ⟨8802799535873575254847883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23474132095662867346261021 8802799535873575254847883)
                ·
                  refine ⟨13204199303810362882271825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802799535873575254847883 13204199303810362882271825)
                  ·
                    refine ⟨9903149477857772161703869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13204199303810362882271825 9903149477857772161703869)
                    ·
                      refine ⟨3713681054196664560638951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903149477857772161703869 3713681054196664560638951)
                      ·
                        rfl

theorem cell23_7232368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_7232368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232368 prefixEnd_7232368 := by exact prefixLift 7232368
  have htrace : WordTrace (prefixWord ++ tailWord_7232368) baseStart_7232368 baseEnd_7232368 := by
    simpa [prefixWord, tailWord_7232368, baseEnd_7232368] using wordTrace_append hprefix tailTrace_7232368
  have hstable : (prefixWord ++ tailWord_7232368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232368).length < 2 ^ (prefixWord ++ tailWord_7232368).sum := by decide
  have hdescent : baseEnd_7232368 < baseStart_7232368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232392 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_7232392 : Nat := 118140960795 + 7232392 * 2 ^ 59
def prefixEnd_7232392 : Nat := 4983230072969 + 3 ^ 40 * 7232392 * 2
def baseEnd_7232392 : Nat := 1237897792577457488912947

theorem tailTrace_7232392 : CollatzResearch.WordTrace tailWord_7232392 prefixEnd_7232392 1237897792577457488912947 := by
  unfold tailWord_7232392
  simp only [CollatzResearch.WordTrace]
  refine ⟨131893503607143226529937715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175858004809524302039916953 131893503607143226529937715)
  ·
    refine ⟨197840255410714839794906573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131893503607143226529937715 197840255410714839794906573)
    ·
      refine ⟨74190095779018064923089965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197840255410714839794906573 74190095779018064923089965)
      ·
        refine ⟨27821285917131774346158737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74190095779018064923089965 27821285917131774346158737)
        ·
          refine ⟨20865964437848830759619053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27821285917131774346158737 20865964437848830759619053)
          ·
            refine ⟨7824736664193311534857145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20865964437848830759619053 7824736664193311534857145)
            ·
              refine ⟨5868552498144983651142859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824736664193311534857145 5868552498144983651142859)
              ·
                refine ⟨8802828747217475476714289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868552498144983651142859 8802828747217475476714289)
                ·
                  refine ⟨6602121560413106607535717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802828747217475476714289 6602121560413106607535717)
                  ·
                    refine ⟨1237897792577457488912947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602121560413106607535717 1237897792577457488912947)
                    ·
                      rfl

theorem cell23_7232392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_7232392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232392 prefixEnd_7232392 := by exact prefixLift 7232392
  have htrace : WordTrace (prefixWord ++ tailWord_7232392) baseStart_7232392 baseEnd_7232392 := by
    simpa [prefixWord, tailWord_7232392, baseEnd_7232392] using wordTrace_append hprefix tailTrace_7232392
  have hstable : (prefixWord ++ tailWord_7232392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232392).length < 2 ^ (prefixWord ++ tailWord_7232392).sum := by decide
  have hdescent : baseEnd_7232392 < baseStart_7232392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232433 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7232433 : Nat := 118140960795 + 7232433 * 2 ^ 59
def prefixEnd_7232433 : Nat := 4983230072969 + 3 ^ 40 * 7232433 * 2
def baseEnd_7232433 : Nat := 3713714430439206806326153

theorem tailTrace_7232433 : CollatzResearch.WordTrace tailWord_7232433 prefixEnd_7232433 3713714430439206806326153 := by
  unfold tailWord_7232433
  simp only [CollatzResearch.WordTrace]
  refine ⟨263788502607137917062117953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175859001738091944708078635 263788502607137917062117953)
  ·
    refine ⟨197841376955353437796588465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263788502607137917062117953 197841376955353437796588465)
    ·
      refine ⟨148381032716515078347441349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197841376955353437796588465 148381032716515078347441349)
      ·
        refine ⟨27821443634346577190145253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148381032716515078347441349 27821443634346577190145253)
        ·
          refine ⟨5216520681439983223152235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27821443634346577190145253 5216520681439983223152235)
          ·
            refine ⟨7824781022159974834728353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216520681439983223152235 7824781022159974834728353)
            ·
              refine ⟨5868585766619981126046265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824781022159974834728353 5868585766619981126046265)
              ·
                refine ⟨4401439324964985844534699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868585766619981126046265 4401439324964985844534699)
                ·
                  refine ⟨6602158987447478766802049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401439324964985844534699 6602158987447478766802049)
                  ·
                    refine ⟨4951619240585609075101537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602158987447478766802049 4951619240585609075101537)
                    ·
                      refine ⟨3713714430439206806326153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951619240585609075101537 3713714430439206806326153)
                      ·
                        rfl

theorem cell23_7232433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7232433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232433 prefixEnd_7232433 := by exact prefixLift 7232433
  have htrace : WordTrace (prefixWord ++ tailWord_7232433) baseStart_7232433 baseEnd_7232433 := by
    simpa [prefixWord, tailWord_7232433, baseEnd_7232433] using wordTrace_append hprefix tailTrace_7232433
  have hstable : (prefixWord ++ tailWord_7232433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232433).length < 2 ^ (prefixWord ++ tailWord_7232433).sum := by decide
  have hdescent : baseEnd_7232433 < baseStart_7232433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232451 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_7232451 : Nat := 118140960795 + 7232451 * 2 ^ 59
def prefixEnd_7232451 : Nat := 4983230072969 + 3 ^ 40 * 7232451 * 2
def baseEnd_7232451 : Nat := 3713723673090987735901069

theorem tailTrace_7232451 : CollatzResearch.WordTrace tailWord_7232451 prefixEnd_7232451 3713723673090987735901069 := by
  unfold tailWord_7232451
  simp only [CollatzResearch.WordTrace]
  refine ⟨263789159121072706136273207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175859439414048470757515471 263789159121072706136273207)
  ·
    refine ⟨395683738681609059204409811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263789159121072706136273207 395683738681609059204409811)
    ·
      refine ⟨593525608022413588806614717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395683738681609059204409811 593525608022413588806614717)
      ·
        refine ⟨222572103008405095802480519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593525608022413588806614717 222572103008405095802480519)
        ·
          refine ⟨333858154512607643703720779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222572103008405095802480519 333858154512607643703720779)
          ·
            refine ⟨500787231768911465555581169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333858154512607643703720779 500787231768911465555581169)
            ·
              refine ⟨375590423826683599166685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500787231768911465555581169 375590423826683599166685877)
              ·
                refine ⟨35211602233751587421876801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375590423826683599166685877 35211602233751587421876801)
                ·
                  refine ⟨26408701675313690566407601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35211602233751587421876801 26408701675313690566407601)
                  ·
                    refine ⟨19806526256485267924805701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26408701675313690566407601 19806526256485267924805701)
                    ·
                      refine ⟨3713723673090987735901069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19806526256485267924805701 3713723673090987735901069)
                      ·
                        rfl

theorem cell23_7232451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_7232451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232451 prefixEnd_7232451 := by exact prefixLift 7232451
  have htrace : WordTrace (prefixWord ++ tailWord_7232451) baseStart_7232451 baseEnd_7232451 := by
    simpa [prefixWord, tailWord_7232451, baseEnd_7232451] using wordTrace_append hprefix tailTrace_7232451
  have hstable : (prefixWord ++ tailWord_7232451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232451).length < 2 ^ (prefixWord ++ tailWord_7232451).sum := by decide
  have hdescent : baseEnd_7232451 < baseStart_7232451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232488 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7232488 : Nat := 118140960795 + 7232488 * 2 ^ 59
def prefixEnd_7232488 : Nat := 4983230072969 + 3 ^ 40 * 7232488 * 2
def baseEnd_7232488 : Nat := 3713742671875204091138399

theorem tailTrace_7232488 : CollatzResearch.WordTrace tailWord_7232488 prefixEnd_7232488 3713742671875204091138399 := by
  unfold tailWord_7232488
  simp only [CollatzResearch.WordTrace]
  refine ⟨131895254310969330727685059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175860339081292440970246745 131895254310969330727685059)
  ·
    refine ⟨197842881466453996091527589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131895254310969330727685059 197842881466453996091527589)
    ·
      refine ⟨37095540274960124267161423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197842881466453996091527589 37095540274960124267161423)
      ·
        refine ⟨55643310412440186400742135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37095540274960124267161423 55643310412440186400742135)
        ·
          refine ⟨83464965618660279601113203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55643310412440186400742135 83464965618660279601113203)
          ·
            refine ⟨125197448427990419401669805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83464965618660279601113203 125197448427990419401669805)
            ·
              refine ⟨46949043160496407275626177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125197448427990419401669805 46949043160496407275626177)
              ·
                refine ⟨35211782370372305456719633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46949043160496407275626177 35211782370372305456719633)
                ·
                  refine ⟨26408836777779229092539725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35211782370372305456719633 26408836777779229092539725)
                  ·
                    refine ⟨9903313791667210909702397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26408836777779229092539725 9903313791667210909702397)
                    ·
                      refine ⟨3713742671875204091138399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903313791667210909702397 3713742671875204091138399)
                      ·
                        rfl

theorem cell23_7232488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7232488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232488 prefixEnd_7232488 := by exact prefixLift 7232488
  have htrace : WordTrace (prefixWord ++ tailWord_7232488) baseStart_7232488 baseEnd_7232488 := by
    simpa [prefixWord, tailWord_7232488, baseEnd_7232488] using wordTrace_append hprefix tailTrace_7232488
  have hstable : (prefixWord ++ tailWord_7232488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232488).length < 2 ^ (prefixWord ++ tailWord_7232488).sum := by decide
  have hdescent : baseEnd_7232488 < baseStart_7232488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232500 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7232500 : Nat := 118140960795 + 7232500 * 2 ^ 59
def prefixEnd_7232500 : Nat := 4983230072969 + 3 ^ 40 * 7232500 * 2
def baseEnd_7232500 : Nat := 3713748833643058044188345

theorem tailTrace_7232500 : CollatzResearch.WordTrace tailWord_7232500 prefixEnd_7232500 3713748833643058044188345 := by
  unfold tailWord_7232500
  simp only [CollatzResearch.WordTrace]
  refine ⟨131895473148947593752403477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175860630865263458336537969 131895473148947593752403477)
  ·
    refine ⟨6182600303856918457143913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131895473148947593752403477 6182600303856918457143913)
    ·
      refine ⟨4636950227892688842857935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6182600303856918457143913 4636950227892688842857935)
      ·
        refine ⟨6955425341839033264286903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636950227892688842857935 6955425341839033264286903)
        ·
          refine ⟨10433138012758549896430355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955425341839033264286903 10433138012758549896430355)
          ·
            refine ⟨15649707019137824844645533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10433138012758549896430355 15649707019137824844645533)
            ·
              refine ⟨5868640132176684316742075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15649707019137824844645533 5868640132176684316742075)
              ·
                refine ⟨8802960198265026475113113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868640132176684316742075 8802960198265026475113113)
                ·
                  refine ⟨6602220148698769856334835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802960198265026475113113 6602220148698769856334835)
                  ·
                    refine ⟨9903330223048154784502253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6602220148698769856334835 9903330223048154784502253)
                    ·
                      refine ⟨3713748833643058044188345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903330223048154784502253 3713748833643058044188345)
                      ·
                        rfl

theorem cell23_7232500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7232500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232500 prefixEnd_7232500 := by exact prefixLift 7232500
  have htrace : WordTrace (prefixWord ++ tailWord_7232500) baseStart_7232500 baseEnd_7232500 := by
    simpa [prefixWord, tailWord_7232500, baseEnd_7232500] using wordTrace_append hprefix tailTrace_7232500
  have hstable : (prefixWord ++ tailWord_7232500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232500).length < 2 ^ (prefixWord ++ tailWord_7232500).sum := by decide
  have hdescent : baseEnd_7232500 < baseStart_7232500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232531 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_7232531 : Nat := 118140960795 + 7232531 * 2 ^ 59
def prefixEnd_7232531 : Nat := 4983230072969 + 3 ^ 40 * 7232531 * 2
def baseEnd_7232531 : Nat := 3713764751543347422900701

theorem tailTrace_7232531 : CollatzResearch.WordTrace tailWord_7232531 prefixEnd_7232531 3713764751543347422900701 := by
  unfold tailWord_7232531
  simp only [CollatzResearch.WordTrace]
  refine ⟨263792076960782879799185447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175861384640521919866123631 263792076960782879799185447)
  ·
    refine ⟨395688115441174319698778171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263792076960782879799185447 395688115441174319698778171)
    ·
      refine ⟨593532173161761479548167257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395688115441174319698778171 593532173161761479548167257)
      ·
        refine ⟨445149129871321109661125443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593532173161761479548167257 445149129871321109661125443)
        ·
          refine ⟨667723694806981664491688165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445149129871321109661125443 667723694806981664491688165)
          ·
            refine ⟨125198192776309062092191531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 667723694806981664491688165 125198192776309062092191531)
            ·
              refine ⟨187797289164463593138287297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125198192776309062092191531 187797289164463593138287297)
              ·
                refine ⟨140847966873347694853715473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187797289164463593138287297 140847966873347694853715473)
                ·
                  refine ⟨105635975155010771140286605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140847966873347694853715473 105635975155010771140286605)
                  ·
                    refine ⟨39613490683129039177607477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105635975155010771140286605 39613490683129039177607477)
                    ·
                      refine ⟨3713764751543347422900701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39613490683129039177607477 3713764751543347422900701)
                      ·
                        rfl

theorem cell23_7232531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_7232531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232531 prefixEnd_7232531 := by exact prefixLift 7232531
  have htrace : WordTrace (prefixWord ++ tailWord_7232531) baseStart_7232531 baseEnd_7232531 := by
    simpa [prefixWord, tailWord_7232531, baseEnd_7232531] using wordTrace_append hprefix tailTrace_7232531
  have hstable : (prefixWord ++ tailWord_7232531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232531).length < 2 ^ (prefixWord ++ tailWord_7232531).sum := by decide
  have hdescent : baseEnd_7232531 < baseStart_7232531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232545 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7232545 : Nat := 118140960795 + 7232545 * 2 ^ 59
def prefixEnd_7232545 : Nat := 4983230072969 + 3 ^ 40 * 7232545 * 2
def baseEnd_7232545 : Nat := 3713771940272510368125637

theorem tailTrace_7232545 : CollatzResearch.WordTrace tailWord_7232545 prefixEnd_7232545 3713771940272510368125637 := by
  unfold tailWord_7232545
  simp only [CollatzResearch.WordTrace]
  refine ⟨263792587582732160190195089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175861725055154773460130059 263792587582732160190195089)
  ·
    refine ⟨197844440687049120142646317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263792587582732160190195089 197844440687049120142646317)
    ·
      refine ⟨74191665257643420053492369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197844440687049120142646317 74191665257643420053492369)
      ·
        refine ⟨55643748943232565040119277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74191665257643420053492369 55643748943232565040119277)
        ·
          refine ⟨20866405853712211890044729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55643748943232565040119277 20866405853712211890044729)
          ·
            refine ⟨15649804390284158917533547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20866405853712211890044729 15649804390284158917533547)
            ·
              refine ⟨23474706585426238376300321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15649804390284158917533547 23474706585426238376300321)
              ·
                refine ⟨17606029939069678782225241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23474706585426238376300321 17606029939069678782225241)
                ·
                  refine ⟨13204522454302259086668931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17606029939069678782225241 13204522454302259086668931)
                  ·
                    refine ⟨19806783681453388630003397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13204522454302259086668931 19806783681453388630003397)
                    ·
                      refine ⟨3713771940272510368125637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19806783681453388630003397 3713771940272510368125637)
                      ·
                        rfl

theorem cell23_7232545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7232545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232545 prefixEnd_7232545 := by exact prefixLift 7232545
  have htrace : WordTrace (prefixWord ++ tailWord_7232545) baseStart_7232545 baseEnd_7232545 := by
    simpa [prefixWord, tailWord_7232545, baseEnd_7232545] using wordTrace_append hprefix tailTrace_7232545
  have hstable : (prefixWord ++ tailWord_7232545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232545).length < 2 ^ (prefixWord ++ tailWord_7232545).sum := by decide
  have hdescent : baseEnd_7232545 < baseStart_7232545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232669 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_7232669 : Nat := 118140960795 + 7232669 * 2 ^ 59
def prefixEnd_7232669 : Nat := 4983230072969 + 3 ^ 40 * 7232669 * 2
def baseEnd_7232669 : Nat := 3713835611873667882975067

theorem tailTrace_7232669 : CollatzResearch.WordTrace tailWord_7232669 prefixEnd_7232669 3713835611873667882975067 := by
  unfold tailWord_7232669
  simp only [CollatzResearch.WordTrace]
  refine ⟨263797110234282929367709061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175864740156188619578472707 263797110234282929367709061)
  ·
    refine ⟨49461958168928049256445449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263797110234282929367709061 49461958168928049256445449)
    ·
      refine ⟨37096468626696036942334087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49461958168928049256445449 37096468626696036942334087)
      ·
        refine ⟨55644702940044055413501131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096468626696036942334087 55644702940044055413501131)
        ·
          refine ⟨83467054410066083120251697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55644702940044055413501131 83467054410066083120251697)
          ·
            refine ⟨62600290807549562340188773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83467054410066083120251697 62600290807549562340188773)
            ·
              refine ⟨11737554526415542938785395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62600290807549562340188773 11737554526415542938785395)
              ·
                refine ⟨17606331789623314408178093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11737554526415542938785395 17606331789623314408178093)
                ·
                  refine ⟨6602374421108742903066785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17606331789623314408178093 6602374421108742903066785)
                  ·
                    refine ⟨4951780815831557177300089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602374421108742903066785 4951780815831557177300089)
                    ·
                      refine ⟨3713835611873667882975067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951780815831557177300089 3713835611873667882975067)
                      ·
                        rfl

theorem cell23_7232669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_7232669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232669 prefixEnd_7232669 := by exact prefixLift 7232669
  have htrace : WordTrace (prefixWord ++ tailWord_7232669) baseStart_7232669 baseEnd_7232669 := by
    simpa [prefixWord, tailWord_7232669, baseEnd_7232669] using wordTrace_append hprefix tailTrace_7232669
  have hstable : (prefixWord ++ tailWord_7232669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232669).length < 2 ^ (prefixWord ++ tailWord_7232669).sum := by decide
  have hdescent : baseEnd_7232669 < baseStart_7232669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232682 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7232682 : Nat := 118140960795 + 7232682 * 2 ^ 59
def prefixEnd_7232682 : Nat := 4983230072969 + 3 ^ 40 * 7232682 * 2
def baseEnd_7232682 : Nat := 3713842287122176332112507

theorem tailTrace_7232682 : CollatzResearch.WordTrace tailWord_7232682 prefixEnd_7232682 3713842287122176332112507 := by
  unfold tailWord_7232682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949396095808958146983075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175865056255490555058621533 65949396095808958146983075)
  ·
    refine ⟨98924094143713437220474613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65949396095808958146983075 98924094143713437220474613)
    ·
      refine ⟨9274133825973134739419495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98924094143713437220474613 9274133825973134739419495)
      ·
        refine ⟨13911200738959702109129243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9274133825973134739419495 13911200738959702109129243)
        ·
          refine ⟨20866801108439553163693865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13911200738959702109129243 20866801108439553163693865)
          ·
            refine ⟨15650100831329664872770399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20866801108439553163693865 15650100831329664872770399)
            ·
              refine ⟨23475151246994497309155599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15650100831329664872770399 23475151246994497309155599)
              ·
                refine ⟨35212726870491745963733399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23475151246994497309155599 35212726870491745963733399)
                ·
                  refine ⟨52819090305737618945600099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35212726870491745963733399 52819090305737618945600099)
                  ·
                    refine ⟨79228635458606428418400149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52819090305737618945600099 79228635458606428418400149)
                    ·
                      refine ⟨3713842287122176332112507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79228635458606428418400149 3713842287122176332112507)
                      ·
                        rfl

theorem cell23_7232682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7232682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232682 prefixEnd_7232682 := by exact prefixLift 7232682
  have htrace : WordTrace (prefixWord ++ tailWord_7232682) baseStart_7232682 baseEnd_7232682 := by
    simpa [prefixWord, tailWord_7232682, baseEnd_7232682] using wordTrace_append hprefix tailTrace_7232682
  have hstable : (prefixWord ++ tailWord_7232682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232682).length < 2 ^ (prefixWord ++ tailWord_7232682).sum := by decide
  have hdescent : baseEnd_7232682 < baseStart_7232682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232689 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7232689 : Nat := 118140960795 + 7232689 * 2 ^ 59
def prefixEnd_7232689 : Nat := 4983230072969 + 3 ^ 40 * 7232689 * 2
def baseEnd_7232689 : Nat := 3713845881486757804724975

theorem tailTrace_7232689 : CollatzResearch.WordTrace tailWord_7232689 prefixEnd_7232689 3713845881486757804724975 := by
  unfold tailWord_7232689
  simp only [CollatzResearch.WordTrace]
  refine ⟨263797839694210472783437121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175865226462806981855624747 263797839694210472783437121)
  ·
    refine ⟨197848379770657854587577841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263797839694210472783437121 197848379770657854587577841)
    ·
      refine ⟨148386284827993390940683381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197848379770657854587577841 148386284827993390940683381)
      ·
        refine ⟨13911214202624380400689067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148386284827993390940683381 13911214202624380400689067)
        ·
          refine ⟨20866821303936570601033601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13911214202624380400689067 20866821303936570601033601)
          ·
            refine ⟨15650115977952427950775201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20866821303936570601033601 15650115977952427950775201)
            ·
              refine ⟨11737586983464320963081401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15650115977952427950775201 11737586983464320963081401)
              ·
                refine ⟨8803190237598240722311051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11737586983464320963081401 8803190237598240722311051)
                ·
                  refine ⟨13204785356397361083466577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803190237598240722311051 13204785356397361083466577)
                  ·
                    refine ⟨9903589017298020812599933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13204785356397361083466577 9903589017298020812599933)
                    ·
                      refine ⟨3713845881486757804724975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903589017298020812599933 3713845881486757804724975)
                      ·
                        rfl

theorem cell23_7232689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7232689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232689 prefixEnd_7232689 := by exact prefixLift 7232689
  have htrace : WordTrace (prefixWord ++ tailWord_7232689) baseStart_7232689 baseEnd_7232689 := by
    simpa [prefixWord, tailWord_7232689, baseEnd_7232689] using wordTrace_append hprefix tailTrace_7232689
  have hstable : (prefixWord ++ tailWord_7232689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232689).length < 2 ^ (prefixWord ++ tailWord_7232689).sum := by decide
  have hdescent : baseEnd_7232689 < baseStart_7232689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232706 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7232706 : Nat := 118140960795 + 7232706 * 2 ^ 59
def prefixEnd_7232706 : Nat := 4983230072969 + 3 ^ 40 * 7232706 * 2
def baseEnd_7232706 : Nat := 3713854610657884238212397

theorem tailTrace_7232706 : CollatzResearch.WordTrace tailWord_7232706 prefixEnd_7232706 3713854610657884238212397 := by
  unfold tailWord_7232706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949614933787221171701493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175865639823432589791203981 65949614933787221171701493)
  ·
    refine ⟨6182776400042551984847015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65949614933787221171701493 6182776400042551984847015)
    ·
      refine ⟨9274164600063827977270523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6182776400042551984847015 9274164600063827977270523)
      ·
        refine ⟨13911246900095741965905785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9274164600063827977270523 13911246900095741965905785)
        ·
          refine ⟨10433435175071806474429339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13911246900095741965905785 10433435175071806474429339)
          ·
            refine ⟨15650152762607709711644009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10433435175071806474429339 15650152762607709711644009)
            ·
              refine ⟨11737614571955782283733007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15650152762607709711644009 11737614571955782283733007)
              ·
                refine ⟨17606421857933673425599511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11737614571955782283733007 17606421857933673425599511)
                ·
                  refine ⟨26409632786900510138399267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17606421857933673425599511 26409632786900510138399267)
                  ·
                    refine ⟨39614449180350765207598901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26409632786900510138399267 39614449180350765207598901)
                    ·
                      refine ⟨3713854610657884238212397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39614449180350765207598901 3713854610657884238212397)
                      ·
                        rfl

theorem cell23_7232706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7232706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232706 prefixEnd_7232706 := by exact prefixLift 7232706
  have htrace : WordTrace (prefixWord ++ tailWord_7232706) baseStart_7232706 baseEnd_7232706 := by
    simpa [prefixWord, tailWord_7232706, baseEnd_7232706] using wordTrace_append hprefix tailTrace_7232706
  have hstable : (prefixWord ++ tailWord_7232706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232706).length < 2 ^ (prefixWord ++ tailWord_7232706).sum := by decide
  have hdescent : baseEnd_7232706 < baseStart_7232706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232736 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3]
def baseStart_7232736 : Nat := 118140960795 + 7232736 * 2 ^ 59
def prefixEnd_7232736 : Nat := 4983230072969 + 3 ^ 40 * 7232736 * 2
def baseEnd_7232736 : Nat := 3713870015077519120837259

theorem tailTrace_7232736 : CollatzResearch.WordTrace tailWord_7232736 prefixEnd_7232736 3713870015077519120837259 := by
  unfold tailWord_7232736
  simp only [CollatzResearch.WordTrace]
  refine ⟨131899776962520099905199031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175866369283360133206932041 131899776962520099905199031)
  ·
    refine ⟨197849665443780149857798547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131899776962520099905199031 197849665443780149857798547)
    ·
      refine ⟨296774498165670224786697821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197849665443780149857798547 296774498165670224786697821)
      ·
        refine ⟨111290436812126334295011683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296774498165670224786697821 111290436812126334295011683)
        ·
          refine ⟨166935655218189501442517525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111290436812126334295011683 166935655218189501442517525)
          ·
            refine ⟨7825108838352632880118009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166935655218189501442517525 7825108838352632880118009)
            ·
              refine ⟨5868831628764474660088507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825108838352632880118009 5868831628764474660088507)
              ·
                refine ⟨8803247443146711990132761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868831628764474660088507 8803247443146711990132761)
                ·
                  refine ⟨6602435582360033992599571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8803247443146711990132761 6602435582360033992599571)
                  ·
                    refine ⟨9903653373540050988899357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6602435582360033992599571 9903653373540050988899357)
                    ·
                      refine ⟨3713870015077519120837259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903653373540050988899357 3713870015077519120837259)
                      ·
                        rfl

theorem cell23_7232736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_7232736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232736 prefixEnd_7232736 := by exact prefixLift 7232736
  have htrace : WordTrace (prefixWord ++ tailWord_7232736) baseStart_7232736 baseEnd_7232736 := by
    simpa [prefixWord, tailWord_7232736, baseEnd_7232736] using wordTrace_append hprefix tailTrace_7232736
  have hstable : (prefixWord ++ tailWord_7232736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232736).length < 2 ^ (prefixWord ++ tailWord_7232736).sum := by decide
  have hdescent : baseEnd_7232736 < baseStart_7232736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232746 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_7232746 : Nat := 118140960795 + 7232746 * 2 ^ 59
def prefixEnd_7232746 : Nat := 4983230072969 + 3 ^ 40 * 7232746 * 2
def baseEnd_7232746 : Nat := 3713875149884064081712213

theorem tailTrace_7232746 : CollatzResearch.WordTrace tailWord_7232746 prefixEnd_7232746 3713875149884064081712213 := by
  unfold tailWord_7232746
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949979663750992879565523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175866612436669314345508061 65949979663750992879565523)
  ·
    refine ⟨98924969495626489319348285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65949979663750992879565523 98924969495626489319348285)
    ·
      refine ⟨37096863560859933494755607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98924969495626489319348285 37096863560859933494755607)
      ·
        refine ⟨55645295341289900242133411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096863560859933494755607 55645295341289900242133411)
        ·
          refine ⟨83467943011934850363200117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55645295341289900242133411 83467943011934850363200117)
          ·
            refine ⟨7825119657368892221550011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83467943011934850363200117 7825119657368892221550011)
            ·
              refine ⟨11737679486053338332325017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825119657368892221550011 11737679486053338332325017)
              ·
                refine ⟨8803259614540003749243763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11737679486053338332325017 8803259614540003749243763)
                ·
                  refine ⟨13204889421810005623865645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803259614540003749243763 13204889421810005623865645)
                  ·
                    refine ⟨4951833533178752108949617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13204889421810005623865645 4951833533178752108949617)
                    ·
                      refine ⟨3713875149884064081712213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951833533178752108949617 3713875149884064081712213)
                      ·
                        rfl

theorem cell23_7232746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_7232746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232746 prefixEnd_7232746 := by exact prefixLift 7232746
  have htrace : WordTrace (prefixWord ++ tailWord_7232746) baseStart_7232746 baseEnd_7232746 := by
    simpa [prefixWord, tailWord_7232746, baseEnd_7232746] using wordTrace_append hprefix tailTrace_7232746
  have hstable : (prefixWord ++ tailWord_7232746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232746).length < 2 ^ (prefixWord ++ tailWord_7232746).sum := by decide
  have hdescent : baseEnd_7232746 < baseStart_7232746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232792 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7232792 : Nat := 118140960795 + 7232792 * 2 ^ 59
def prefixEnd_7232792 : Nat := 4983230072969 + 3 ^ 40 * 7232792 * 2
def baseEnd_7232792 : Nat := 3713898769994170901737001

theorem tailTrace_7232792 : CollatzResearch.WordTrace tailWord_7232792 prefixEnd_7232792 3713898769994170901737001 := by
  unfold tailWord_7232792
  simp only [CollatzResearch.WordTrace]
  refine ⟨131900798206418660687218315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175867730941891547582957753 131900798206418660687218315)
  ·
    refine ⟨197851197309627991030827473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131900798206418660687218315 197851197309627991030827473)
    ·
      refine ⟨148388397982220993273120605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197851197309627991030827473 148388397982220993273120605)
      ·
        refine ⟨55645649243332872477420227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148388397982220993273120605 55645649243332872477420227)
        ·
          refine ⟨83468473864999308716130341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55645649243332872477420227 83468473864999308716130341)
          ·
            refine ⟨15650338849687370384274439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83468473864999308716130341 15650338849687370384274439)
            ·
              refine ⟨23475508274531055576411659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15650338849687370384274439 23475508274531055576411659)
              ·
                refine ⟨35213262411796583364617489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23475508274531055576411659 35213262411796583364617489)
                ·
                  refine ⟨26409946808847437523463117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35213262411796583364617489 26409946808847437523463117)
                  ·
                    refine ⟨9903730053317789071298669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26409946808847437523463117 9903730053317789071298669)
                    ·
                      refine ⟨3713898769994170901737001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903730053317789071298669 3713898769994170901737001)
                      ·
                        rfl

theorem cell23_7232792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7232792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232792 prefixEnd_7232792 := by exact prefixLift 7232792
  have htrace : WordTrace (prefixWord ++ tailWord_7232792) baseStart_7232792 baseEnd_7232792 := by
    simpa [prefixWord, tailWord_7232792, baseEnd_7232792] using wordTrace_append hprefix tailTrace_7232792
  have hstable : (prefixWord ++ tailWord_7232792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232792).length < 2 ^ (prefixWord ++ tailWord_7232792).sum := by decide
  have hdescent : baseEnd_7232792 < baseStart_7232792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232832 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2]
def baseStart_7232832 : Nat := 118140960795 + 7232832 * 2 ^ 59
def prefixEnd_7232832 : Nat := 4983230072969 + 3 ^ 40 * 7232832 * 2
def baseEnd_7232832 : Nat := 3713919309220350745236817

theorem tailTrace_7232832 : CollatzResearch.WordTrace tailWord_7232832 prefixEnd_7232832 3713919309220350745236817 := by
  unfold tailWord_7232832
  simp only [CollatzResearch.WordTrace]
  refine ⟨131901527666346204102946375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175868703555128272137261833 131901527666346204102946375)
  ·
    refine ⟨197852291499519306154419563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131901527666346204102946375 197852291499519306154419563)
    ·
      refine ⟨296778437249278959231629345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197852291499519306154419563 296778437249278959231629345)
      ·
        refine ⟨222583827936959219423722009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296778437249278959231629345 222583827936959219423722009)
        ·
          refine ⟨166937870952719414567791507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222583827936959219423722009 166937870952719414567791507)
          ·
            refine ⟨250406806429079121851687261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166937870952719414567791507 250406806429079121851687261)
            ·
              refine ⟨93902552410904670694382723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250406806429079121851687261 93902552410904670694382723)
              ·
                refine ⟨140853828616357006041574085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93902552410904670694382723 140853828616357006041574085)
                ·
                  refine ⟨26410092865566938632795141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140853828616357006041574085 26410092865566938632795141)
                  ·
                    refine ⟨4951892412293800993649089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26410092865566938632795141 4951892412293800993649089)
                    ·
                      refine ⟨3713919309220350745236817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4951892412293800993649089 3713919309220350745236817)
                      ·
                        rfl

theorem cell23_7232832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_7232832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232832 prefixEnd_7232832 := by exact prefixLift 7232832
  have htrace : WordTrace (prefixWord ++ tailWord_7232832) baseStart_7232832 baseEnd_7232832 := by
    simpa [prefixWord, tailWord_7232832, baseEnd_7232832] using wordTrace_append hprefix tailTrace_7232832
  have hstable : (prefixWord ++ tailWord_7232832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232832).length < 2 ^ (prefixWord ++ tailWord_7232832).sum := by decide
  have hdescent : baseEnd_7232832 < baseStart_7232832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232852 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_7232852 : Nat := 118140960795 + 7232852 * 2 ^ 59
def prefixEnd_7232852 : Nat := 4983230072969 + 3 ^ 40 * 7232852 * 2
def baseEnd_7232852 : Nat := 3713929578833440666986725

theorem tailTrace_7232852 : CollatzResearch.WordTrace tailWord_7232852 prefixEnd_7232852 3713929578833440666986725 := by
  unfold tailWord_7232852
  simp only [CollatzResearch.WordTrace]
  refine ⟨131901892396309975810810405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175869189861746634414413873 131901892396309975810810405)
  ·
    refine ⟨24731604824308120464526951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131901892396309975810810405 24731604824308120464526951)
    ·
      refine ⟨37097407236462180696790427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24731604824308120464526951 37097407236462180696790427)
      ·
        refine ⟨55646110854693271045185641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37097407236462180696790427 55646110854693271045185641)
        ·
          refine ⟨41734583141019953283889231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55646110854693271045185641 41734583141019953283889231)
          ·
            refine ⟨62601874711529929925833847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41734583141019953283889231 62601874711529929925833847)
            ·
              refine ⟨93902812067294894888750771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62601874711529929925833847 93902812067294894888750771)
              ·
                refine ⟨140854218100942342333126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93902812067294894888750771 140854218100942342333126157)
                ·
                  refine ⟨52820331787853378374922309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140854218100942342333126157 52820331787853378374922309)
                  ·
                    refine ⟨9903812210222508445297933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52820331787853378374922309 9903812210222508445297933)
                    ·
                      refine ⟨3713929578833440666986725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9903812210222508445297933 3713929578833440666986725)
                      ·
                        rfl

theorem cell23_7232852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_7232852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232852 prefixEnd_7232852 := by exact prefixLift 7232852
  have htrace : WordTrace (prefixWord ++ tailWord_7232852) baseStart_7232852 baseEnd_7232852 := by
    simpa [prefixWord, tailWord_7232852, baseEnd_7232852] using wordTrace_append hprefix tailTrace_7232852
  have hstable : (prefixWord ++ tailWord_7232852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232852).length < 2 ^ (prefixWord ++ tailWord_7232852).sum := by decide
  have hdescent : baseEnd_7232852 < baseStart_7232852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232876 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_7232876 : Nat := 118140960795 + 7232876 * 2 ^ 59
def prefixEnd_7232876 : Nat := 4983230072969 + 3 ^ 40 * 7232876 * 2
def baseEnd_7232876 : Nat := 1237980634123049524362205

theorem tailTrace_7232876 : CollatzResearch.WordTrace tailWord_7232876 prefixEnd_7232876 1237980634123049524362205 := by
  unfold tailWord_7232876
  simp only [CollatzResearch.WordTrace]
  refine ⟨131902330072266501860247241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175869773429688669146996321 131902330072266501860247241)
  ·
    refine ⟨98926747554199876395185431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131902330072266501860247241 98926747554199876395185431)
    ·
      refine ⟨148390121331299814592778147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98926747554199876395185431 148390121331299814592778147)
      ·
        refine ⟨222585181996949721889167221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148390121331299814592778147 222585181996949721889167221)
        ·
          refine ⟨20867360812214036427109427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222585181996949721889167221 20867360812214036427109427)
          ·
            refine ⟨31301041218321054640664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20867360812214036427109427 31301041218321054640664141)
            ·
              refine ⟨11737890456870395490249053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31301041218321054640664141 11737890456870395490249053)
              ·
                refine ⟨4401708921326398308843395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11737890456870395490249053 4401708921326398308843395)
                ·
                  refine ⟨6602563381989597463265093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401708921326398308843395 6602563381989597463265093)
                  ·
                    refine ⟨1237980634123049524362205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602563381989597463265093 1237980634123049524362205)
                    ·
                      rfl

theorem cell23_7232876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_7232876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232876 prefixEnd_7232876 := by exact prefixLift 7232876
  have htrace : WordTrace (prefixWord ++ tailWord_7232876) baseStart_7232876 baseEnd_7232876 := by
    simpa [prefixWord, tailWord_7232876, baseEnd_7232876] using wordTrace_append hprefix tailTrace_7232876
  have hstable : (prefixWord ++ tailWord_7232876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232876).length < 2 ^ (prefixWord ++ tailWord_7232876).sum := by decide
  have hdescent : baseEnd_7232876 < baseStart_7232876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232915 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 6]
def baseStart_7232915 : Nat := 118140960795 + 7232915 * 2 ^ 59
def prefixEnd_7232915 : Nat := 4983230072969 + 3 ^ 40 * 7232915 * 2
def baseEnd_7232915 : Nat := 1237987309371557973499645

theorem tailTrace_7232915 : CollatzResearch.WordTrace tailWord_7232915 prefixEnd_7232915 1237987309371557973499645 := by
  unfold tailWord_7232915
  simp only [CollatzResearch.WordTrace]
  refine ⟨263806082591391713381164199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175870721727594475587442799 263806082591391713381164199)
  ·
    refine ⟨395709123887087570071746299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263806082591391713381164199 395709123887087570071746299)
    ·
      refine ⟨593563685830631355107619449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395709123887087570071746299 593563685830631355107619449)
      ·
        refine ⟨445172764372973516330714587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593563685830631355107619449 445172764372973516330714587)
        ·
          refine ⟨667759146559460274496071881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445172764372973516330714587 667759146559460274496071881)
          ·
            refine ⟨500819359919595205872053911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667759146559460274496071881 500819359919595205872053911)
            ·
              refine ⟨751229039879392808808080867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500819359919595205872053911 751229039879392808808080867)
              ·
                refine ⟨1126843559819089213212121301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751229039879392808808080867 1126843559819089213212121301)
                ·
                  refine ⟨26410395933259903434659093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1126843559819089213212121301 26410395933259903434659093)
                  ·
                    refine ⟨1237987309371557973499645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26410395933259903434659093 1237987309371557973499645)
                    ·
                      rfl

theorem cell23_7232915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_7232915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232915 prefixEnd_7232915 := by exact prefixLift 7232915
  have htrace : WordTrace (prefixWord ++ tailWord_7232915) baseStart_7232915 baseEnd_7232915 := by
    simpa [prefixWord, tailWord_7232915, baseEnd_7232915] using wordTrace_append hprefix tailTrace_7232915
  have hstable : (prefixWord ++ tailWord_7232915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232915).length < 2 ^ (prefixWord ++ tailWord_7232915).sum := by decide
  have hdescent : baseEnd_7232915 < baseStart_7232915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7232993 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_7232993 : Nat := 118140960795 + 7232993 * 2 ^ 59
def prefixEnd_7232993 : Nat := 4983230072969 + 3 ^ 40 * 7232993 * 2
def baseEnd_7232993 : Nat := 3714001979605724615323577

theorem tailTrace_7232993 : CollatzResearch.WordTrace tailWord_7232993 prefixEnd_7232993 3714001979605724615323577 := by
  unfold tailWord_7232993
  simp only [CollatzResearch.WordTrace]
  refine ⟨263808927485109132702503633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175872618323406088468335755 263808927485109132702503633)
  ·
    refine ⟨197856695613831849526877725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263808927485109132702503633 197856695613831849526877725)
    ·
      refine ⟨74196260855186943572579147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197856695613831849526877725 74196260855186943572579147)
      ·
        refine ⟨111294391282780415358868721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74196260855186943572579147 111294391282780415358868721)
        ·
          refine ⟨83470793462085311519151541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111294391282780415358868721 83470793462085311519151541)
          ·
            refine ⟨7825386887070497954920457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83470793462085311519151541 7825386887070497954920457)
            ·
              refine ⟨5869040165302873466190343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825386887070497954920457 5869040165302873466190343)
              ·
                refine ⟨8803560247954310199285515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869040165302873466190343 8803560247954310199285515)
                ·
                  refine ⟨13205340371931465298928273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803560247954310199285515 13205340371931465298928273)
                  ·
                    refine ⟨9904005278948598974196205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13205340371931465298928273 9904005278948598974196205)
                    ·
                      refine ⟨3714001979605724615323577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9904005278948598974196205 3714001979605724615323577)
                      ·
                        rfl

theorem cell23_7232993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_7232993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7232993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7232993 prefixEnd_7232993 := by exact prefixLift 7232993
  have htrace : WordTrace (prefixWord ++ tailWord_7232993) baseStart_7232993 baseEnd_7232993 := by
    simpa [prefixWord, tailWord_7232993, baseEnd_7232993] using wordTrace_append hprefix tailTrace_7232993
  have hstable : (prefixWord ++ tailWord_7232993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7232993).length < 2 ^ (prefixWord ++ tailWord_7232993).sum := by decide
  have hdescent : baseEnd_7232993 < baseStart_7232993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7232993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233006 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_7233006 : Nat := 118140960795 + 7233006 * 2 ^ 59
def prefixEnd_7233006 : Nat := 4983230072969 + 3 ^ 40 * 7233006 * 2
def baseEnd_7233006 : Nat := 3714008654854233064461017

theorem tailTrace_7233006 : CollatzResearch.WordTrace tailWord_7233006 prefixEnd_7233006 3714008654854233064461017 := by
  unfold tailWord_7233006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32976175204257754490340859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175872934422708023948484581 32976175204257754490340859)
  ·
    refine ⟨49464262806386631735511289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32976175204257754490340859 49464262806386631735511289)
    ·
      refine ⟨37098197104789973801633467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49464262806386631735511289 37098197104789973801633467)
      ·
        refine ⟨55647295657184960702450201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37098197104789973801633467 55647295657184960702450201)
        ·
          refine ⟨41735471742888720526837651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55647295657184960702450201 41735471742888720526837651)
          ·
            refine ⟨62603207614333080790256477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41735471742888720526837651 62603207614333080790256477)
            ·
              refine ⟨23476202855374905296346179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62603207614333080790256477 23476202855374905296346179)
              ·
                refine ⟨35214304283062357944519269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23476202855374905296346179 35214304283062357944519269)
                ·
                  refine ⟨6602682053074192114597363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35214304283062357944519269 6602682053074192114597363)
                  ·
                    refine ⟨9904023079611288171896045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6602682053074192114597363 9904023079611288171896045)
                    ·
                      refine ⟨3714008654854233064461017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9904023079611288171896045 3714008654854233064461017)
                      ·
                        rfl

theorem cell23_7233006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_7233006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233006 prefixEnd_7233006 := by exact prefixLift 7233006
  have htrace : WordTrace (prefixWord ++ tailWord_7233006) baseStart_7233006 baseEnd_7233006 := by
    simpa [prefixWord, tailWord_7233006, baseEnd_7233006] using wordTrace_append hprefix tailTrace_7233006
  have hstable : (prefixWord ++ tailWord_7233006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233006).length < 2 ^ (prefixWord ++ tailWord_7233006).sum := by decide
  have hdescent : baseEnd_7233006 < baseStart_7233006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233080 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_7233080 : Nat := 118140960795 + 7233080 * 2 ^ 59
def prefixEnd_7233080 : Nat := 4983230072969 + 3 ^ 40 * 7233080 * 2
def baseEnd_7233080 : Nat := 3714046652422665774935677

theorem tailTrace_7233080 : CollatzResearch.WordTrace tailWord_7233080 prefixEnd_7233080 3714046652422665774935677 := by
  unfold tailWord_7233080
  simp only [CollatzResearch.WordTrace]
  refine ⟨131906050317896973280460347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175874733757195964373947129 131906050317896973280460347)
  ·
    refine ⟨197859075476845459920690521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131906050317896973280460347 197859075476845459920690521)
    ·
      refine ⟨148394306607634094940517891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197859075476845459920690521 148394306607634094940517891)
      ·
        refine ⟨222591459911451142410776837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148394306607634094940517891 222591459911451142410776837)
        ·
          refine ⟨41735898733397089202020657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222591459911451142410776837 41735898733397089202020657)
          ·
            refine ⟨31301924050047816901515493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41735898733397089202020657 31301924050047816901515493)
            ·
              refine ⟨5869110759383965669034155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31301924050047816901515493 5869110759383965669034155)
              ·
                refine ⟨8803666139075948503551233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869110759383965669034155 8803666139075948503551233)
                ·
                  refine ⟨6602749604306961377663425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8803666139075948503551233 6602749604306961377663425)
                  ·
                    refine ⟨4952062203230221033247569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602749604306961377663425 4952062203230221033247569)
                    ·
                      refine ⟨3714046652422665774935677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952062203230221033247569 3714046652422665774935677)
                      ·
                        rfl

theorem cell23_7233080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_7233080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233080 prefixEnd_7233080 := by exact prefixLift 7233080
  have htrace : WordTrace (prefixWord ++ tailWord_7233080) baseStart_7233080 baseEnd_7233080 := by
    simpa [prefixWord, tailWord_7233080, baseEnd_7233080] using wordTrace_append hprefix tailTrace_7233080
  have hstable : (prefixWord ++ tailWord_7233080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233080).length < 2 ^ (prefixWord ++ tailWord_7233080).sum := by decide
  have hdescent : baseEnd_7233080 < baseStart_7233080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233116 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7233116 : Nat := 118140960795 + 7233116 * 2 ^ 59
def prefixEnd_7233116 : Nat := 4983230072969 + 3 ^ 40 * 7233116 * 2
def baseEnd_7233116 : Nat := 1238021712575409211361837

theorem tailTrace_7233116 : CollatzResearch.WordTrace tailWord_7233116 prefixEnd_7233116 1238021712575409211361837 := by
  unfold tailWord_7233116
  simp only [CollatzResearch.WordTrace]
  refine ⟨131906706831831762354615601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175875609109109016472820801 131906706831831762354615601)
  ·
    refine ⟨98930030123873821765961701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131906706831831762354615601 98930030123873821765961701)
    ·
      refine ⟨18549380648226341581117819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98930030123873821765961701 18549380648226341581117819)
      ·
        refine ⟨27824070972339512371676729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549380648226341581117819 27824070972339512371676729)
        ·
          refine ⟨20868053229254634278757547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27824070972339512371676729 20868053229254634278757547)
          ·
            refine ⟨31302079843881951418136321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20868053229254634278757547 31302079843881951418136321)
            ·
              refine ⟨23476559882911463563602241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31302079843881951418136321 23476559882911463563602241)
              ·
                refine ⟨17607419912183597672701681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23476559882911463563602241 17607419912183597672701681)
                ·
                  refine ⟨13205564934137698254526261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17607419912183597672701681 13205564934137698254526261)
                  ·
                    refine ⟨1238021712575409211361837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13205564934137698254526261 1238021712575409211361837)
                    ·
                      rfl

theorem cell23_7233116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7233116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233116 prefixEnd_7233116 := by exact prefixLift 7233116
  have htrace : WordTrace (prefixWord ++ tailWord_7233116) baseStart_7233116 baseEnd_7233116 := by
    simpa [prefixWord, tailWord_7233116, baseEnd_7233116] using wordTrace_append hprefix tailTrace_7233116
  have hstable : (prefixWord ++ tailWord_7233116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233116).length < 2 ^ (prefixWord ++ tailWord_7233116).sum := by decide
  have hdescent : baseEnd_7233116 < baseStart_7233116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233136 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2]
def baseStart_7233136 : Nat := 118140960795 + 7233136 * 2 ^ 59
def prefixEnd_7233136 : Nat := 4983230072969 + 3 ^ 40 * 7233136 * 2
def baseEnd_7233136 : Nat := 3714075407339317555835419

theorem tailTrace_7233136 : CollatzResearch.WordTrace tailWord_7233136 prefixEnd_7233136 3714075407339317555835419 := by
  unfold tailWord_7233136
  simp only [CollatzResearch.WordTrace]
  refine ⟨131907071561795534062479631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175876095415727378749972841 131907071561795534062479631)
  ·
    refine ⟨197860607342693301093719447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131907071561795534062479631 197860607342693301093719447)
    ·
      refine ⟨296790911014039951640579171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197860607342693301093719447 296790911014039951640579171)
      ·
        refine ⟨445186366521059927460868757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296790911014039951640579171 445186366521059927460868757)
        ·
          refine ⟨20868110930674684099728223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445186366521059927460868757 20868110930674684099728223)
          ·
            refine ⟨31302166396012026149592335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20868110930674684099728223 31302166396012026149592335)
            ·
              refine ⟨46953249594018039224388503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31302166396012026149592335 46953249594018039224388503)
              ·
                refine ⟨70429874391027058836582755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46953249594018039224388503 70429874391027058836582755)
                ·
                  refine ⟨105644811586540588254874133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70429874391027058836582755 105644811586540588254874133)
                  ·
                    refine ⟨4952100543119090074447225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105644811586540588254874133 4952100543119090074447225)
                    ·
                      refine ⟨3714075407339317555835419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952100543119090074447225 3714075407339317555835419)
                      ·
                        rfl

theorem cell23_7233136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2].length) (baseStart_7233136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233136 prefixEnd_7233136 := by exact prefixLift 7233136
  have htrace : WordTrace (prefixWord ++ tailWord_7233136) baseStart_7233136 baseEnd_7233136 := by
    simpa [prefixWord, tailWord_7233136, baseEnd_7233136] using wordTrace_append hprefix tailTrace_7233136
  have hstable : (prefixWord ++ tailWord_7233136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233136).length < 2 ^ (prefixWord ++ tailWord_7233136).sum := by decide
  have hdescent : baseEnd_7233136 < baseStart_7233136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233153 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_7233153 : Nat := 118140960795 + 7233153 * 2 ^ 59
def prefixEnd_7233153 : Nat := 4983230072969 + 3 ^ 40 * 7233153 * 2
def baseEnd_7233153 : Nat := 3714084136510443989322841

theorem tailTrace_7233153 : CollatzResearch.WordTrace tailWord_7233153 prefixEnd_7233153 3714084136510443989322841 := by
  unfold tailWord_7233153
  simp only [CollatzResearch.WordTrace]
  refine ⟨263814763164529480028328113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175876508776352986685552075 263814763164529480028328113)
  ·
    refine ⟨197861072373397110021246085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263814763164529480028328113 197861072373397110021246085)
    ·
      refine ⟨37098951070011958128983641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197861072373397110021246085 37098951070011958128983641)
      ·
        refine ⟨27824213302508968596737731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37098951070011958128983641 27824213302508968596737731)
        ·
          refine ⟨41736319953763452895106597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27824213302508968596737731 41736319953763452895106597)
          ·
            refine ⟨7825559991330647417832487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41736319953763452895106597 7825559991330647417832487)
            ·
              refine ⟨11738339986995971126748731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825559991330647417832487 11738339986995971126748731)
              ·
                refine ⟨17607509980493956690123097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11738339986995971126748731 17607509980493956690123097)
                ·
                  refine ⟨13205632485370467517592323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17607509980493956690123097 13205632485370467517592323)
                  ·
                    refine ⟨19808448728055701276388485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13205632485370467517592323 19808448728055701276388485)
                    ·
                      refine ⟨3714084136510443989322841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19808448728055701276388485 3714084136510443989322841)
                      ·
                        rfl

theorem cell23_7233153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_7233153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233153 prefixEnd_7233153 := by exact prefixLift 7233153
  have htrace : WordTrace (prefixWord ++ tailWord_7233153) baseStart_7233153 baseEnd_7233153 := by
    simpa [prefixWord, tailWord_7233153, baseEnd_7233153] using wordTrace_append hprefix tailTrace_7233153
  have hstable : (prefixWord ++ tailWord_7233153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233153).length < 2 ^ (prefixWord ++ tailWord_7233153).sum := by decide
  have hdescent : baseEnd_7233153 < baseStart_7233153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233163 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 1, 4]
def baseStart_7233163 : Nat := 118140960795 + 7233163 * 2 ^ 59
def prefixEnd_7233163 : Nat := 4983230072969 + 3 ^ 40 * 7233163 * 2
def baseEnd_7233163 : Nat := 1238029757105662983399265

theorem tailTrace_7233163 : CollatzResearch.WordTrace tailWord_7233163 prefixEnd_7233163 1238029757105662983399265 := by
  unfold tailWord_7233163
  simp only [CollatzResearch.WordTrace]
  refine ⟨263815127894493251736192143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175876751929662167824128095 263815127894493251736192143)
  ·
    refine ⟨395722691841739877604288215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263815127894493251736192143 395722691841739877604288215)
    ·
      refine ⟨593584037762609816406432323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395722691841739877604288215 593584037762609816406432323)
      ·
        refine ⟨890376056643914724609648485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593584037762609816406432323 890376056643914724609648485)
        ·
          refine ⟨166945510620734010864309091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 890376056643914724609648485 166945510620734010864309091)
          ·
            refine ⟨250418265931101016296463637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166945510620734010864309091 250418265931101016296463637)
            ·
              refine ⟨11738356215520360138896733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250418265931101016296463637 11738356215520360138896733)
              ·
                refine ⟨4401883580820135052086275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11738356215520360138896733 4401883580820135052086275)
                ·
                  refine ⟨6602825371230202578129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401883580820135052086275 6602825371230202578129413)
                  ·
                    refine ⟨1238029757105662983399265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602825371230202578129413 1238029757105662983399265)
                    ·
                      rfl

theorem cell23_7233163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 4].length) (baseStart_7233163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233163 prefixEnd_7233163 := by exact prefixLift 7233163
  have htrace : WordTrace (prefixWord ++ tailWord_7233163) baseStart_7233163 baseEnd_7233163 := by
    simpa [prefixWord, tailWord_7233163, baseEnd_7233163] using wordTrace_append hprefix tailTrace_7233163
  have hstable : (prefixWord ++ tailWord_7233163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233163).length < 2 ^ (prefixWord ++ tailWord_7233163).sum := by decide
  have hdescent : baseEnd_7233163 < baseStart_7233163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233176 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 6]
def baseStart_7233176 : Nat := 118140960795 + 7233176 * 2 ^ 59
def prefixEnd_7233176 : Nat := 4983230072969 + 3 ^ 40 * 7233176 * 2
def baseEnd_7233176 : Nat := 412677327396166377703915

theorem tailTrace_7233176 : CollatzResearch.WordTrace tailWord_7233176 prefixEnd_7233176 412677327396166377703915 := by
  unfold tailWord_7233176
  simp only [CollatzResearch.WordTrace]
  refine ⟨131907801021723077478207691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175877068028964103304276921 131907801021723077478207691)
  ·
    refine ⟨197861701532584616217311537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131907801021723077478207691 197861701532584616217311537)
    ·
      refine ⟨148396276149438462162983653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197861701532584616217311537 148396276149438462162983653)
      ·
        refine ⟨27824301778019711655559435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148396276149438462162983653 27824301778019711655559435)
        ·
          refine ⟨41736452667029567483339153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27824301778019711655559435 41736452667029567483339153)
          ·
            refine ⟨31302339500272175612504365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41736452667029567483339153 31302339500272175612504365)
            ·
              refine ⟨11738377312602065854689137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31302339500272175612504365 11738377312602065854689137)
              ·
                refine ⟨8803782984451549391016853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11738377312602065854689137 8803782984451549391016853)
                ·
                  refine ⟨412677327396166377703915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8803782984451549391016853 412677327396166377703915)
                  ·
                    rfl

theorem cell23_7233176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_7233176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233176 prefixEnd_7233176 := by exact prefixLift 7233176
  have htrace : WordTrace (prefixWord ++ tailWord_7233176) baseStart_7233176 baseEnd_7233176 := by
    simpa [prefixWord, tailWord_7233176, baseEnd_7233176] using wordTrace_append hprefix tailTrace_7233176
  have hstable : (prefixWord ++ tailWord_7233176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233176).length < 2 ^ (prefixWord ++ tailWord_7233176).sum := by decide
  have hdescent : baseEnd_7233176 < baseStart_7233176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233189 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_7233189 : Nat := 118140960795 + 7233189 * 2 ^ 59
def prefixEnd_7233189 : Nat := 4983230072969 + 3 ^ 40 * 7233189 * 2
def baseEnd_7233189 : Nat := 1238034207271335282824225

theorem tailTrace_7233189 : CollatzResearch.WordTrace tailWord_7233189 prefixEnd_7233189 1238034207271335282824225 := by
  unfold tailWord_7233189
  simp only [CollatzResearch.WordTrace]
  refine ⟨263816076192399058176638621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175877384128266038784425747 263816076192399058176638621)
  ·
    refine ⟨98931028572149646816239483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263816076192399058176638621 98931028572149646816239483)
    ·
      refine ⟨148396542858224470224359225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98931028572149646816239483 148396542858224470224359225)
      ·
        refine ⟨111297407143668352668269419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148396542858224470224359225 111297407143668352668269419)
        ·
          refine ⟨166946110715502529002404129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111297407143668352668269419 166946110715502529002404129)
          ·
            refine ⟨125209583036626896751803097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166946110715502529002404129 125209583036626896751803097)
            ·
              refine ⟨93907187277470172563852323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125209583036626896751803097 93907187277470172563852323)
              ·
                refine ⟨140860780916205258845778485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93907187277470172563852323 140860780916205258845778485)
                ·
                  refine ⟨13205698210894243016791733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140860780916205258845778485 13205698210894243016791733)
                  ·
                    refine ⟨1238034207271335282824225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13205698210894243016791733 1238034207271335282824225)
                    ·
                      rfl

theorem cell23_7233189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_7233189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233189 prefixEnd_7233189 := by exact prefixLift 7233189
  have htrace : WordTrace (prefixWord ++ tailWord_7233189) baseStart_7233189 baseEnd_7233189 := by
    simpa [prefixWord, tailWord_7233189, baseEnd_7233189] using wordTrace_append hprefix tailTrace_7233189
  have hstable : (prefixWord ++ tailWord_7233189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233189).length < 2 ^ (prefixWord ++ tailWord_7233189).sum := by decide
  have hdescent : baseEnd_7233189 < baseStart_7233189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233213 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_7233213 : Nat := 118140960795 + 7233213 * 2 ^ 59
def prefixEnd_7233213 : Nat := 4983230072969 + 3 ^ 40 * 7233213 * 2
def baseEnd_7233213 : Nat := 3714114945349713754572565

theorem tailTrace_7233213 : CollatzResearch.WordTrace tailWord_7233213 prefixEnd_7233213 3714114945349713754572565 := by
  unfold tailWord_7233213
  simp only [CollatzResearch.WordTrace]
  refine ⟨263816951544312110275512293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175877967696208073517008195 263816951544312110275512293)
  ·
    refine ⟨49465678414558520676658555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263816951544312110275512293 49465678414558520676658555)
    ·
      refine ⟨74198517621837781014987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49465678414558520676658555 74198517621837781014987833)
      ·
        refine ⟨55648888216378335761240875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74198517621837781014987833 55648888216378335761240875)
        ·
          refine ⟨83473332324567503641861313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55648888216378335761240875 83473332324567503641861313)
          ·
            refine ⟨62604999243425627731395985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83473332324567503641861313 62604999243425627731395985)
            ·
              refine ⟨46953749432569220798546989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62604999243425627731395985 46953749432569220798546989)
              ·
                refine ⟨17607656037213457799455121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46953749432569220798546989 17607656037213457799455121)
                ·
                  refine ⟨13205742027910093349591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17607656037213457799455121 13205742027910093349591341)
                  ·
                    refine ⟨4952153260466285006096753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13205742027910093349591341 4952153260466285006096753)
                    ·
                      refine ⟨3714114945349713754572565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952153260466285006096753 3714114945349713754572565)
                      ·
                        rfl

theorem cell23_7233213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_7233213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233213 prefixEnd_7233213 := by exact prefixLift 7233213
  have htrace : WordTrace (prefixWord ++ tailWord_7233213) baseStart_7233213 baseEnd_7233213 := by
    simpa [prefixWord, tailWord_7233213, baseEnd_7233213] using wordTrace_append hprefix tailTrace_7233213
  have hstable : (prefixWord ++ tailWord_7233213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233213).length < 2 ^ (prefixWord ++ tailWord_7233213).sum := by decide
  have hdescent : baseEnd_7233213 < baseStart_7233213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233239 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_7233239 : Nat := 118140960795 + 7233239 * 2 ^ 59
def prefixEnd_7233239 : Nat := 4983230072969 + 3 ^ 40 * 7233239 * 2
def baseEnd_7233239 : Nat := 3714128295846730652847445

theorem tailTrace_7233239 : CollatzResearch.WordTrace tailWord_7233239 prefixEnd_7233239 3714128295846730652847445 := by
  unfold tailWord_7233239
  simp only [CollatzResearch.WordTrace]
  refine ⟨263817899842217916715958771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175878599894811944477305847 263817899842217916715958771)
  ·
    refine ⟨395726849763326875073938157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263817899842217916715958771 395726849763326875073938157)
    ·
      refine ⟨148397568661247578152726809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395726849763326875073938157 148397568661247578152726809)
      ·
        refine ⟨111298176495935683614545107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148397568661247578152726809 111298176495935683614545107)
        ·
          refine ⟨166947264743903525421817661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111298176495935683614545107 166947264743903525421817661)
          ·
            refine ⟨62605224278963822033181623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166947264743903525421817661 62605224278963822033181623)
            ·
              refine ⟨93907836418445733049772435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62605224278963822033181623 93907836418445733049772435)
              ·
                refine ⟨140861754627668599574658653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93907836418445733049772435 140861754627668599574658653)
                ·
                  refine ⟨52823157985375724840496995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140861754627668599574658653 52823157985375724840496995)
                  ·
                    refine ⟨79234736978063587260745493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52823157985375724840496995 79234736978063587260745493)
                    ·
                      refine ⟨3714128295846730652847445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79234736978063587260745493 3714128295846730652847445)
                      ·
                        rfl

theorem cell23_7233239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_7233239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233239 prefixEnd_7233239 := by exact prefixLift 7233239
  have htrace : WordTrace (prefixWord ++ tailWord_7233239) baseStart_7233239 baseEnd_7233239 := by
    simpa [prefixWord, tailWord_7233239, baseEnd_7233239] using wordTrace_append hprefix tailTrace_7233239
  have hstable : (prefixWord ++ tailWord_7233239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233239).length < 2 ^ (prefixWord ++ tailWord_7233239).sum := by decide
  have hdescent : baseEnd_7233239 < baseStart_7233239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233253 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_7233253 : Nat := 118140960795 + 7233253 * 2 ^ 59
def prefixEnd_7233253 : Nat := 4983230072969 + 3 ^ 40 * 7233253 * 2
def baseEnd_7233253 : Nat := 1238045161525297866024127

theorem tailTrace_7233253 : CollatzResearch.WordTrace tailWord_7233253 prefixEnd_7233253 1238045161525297866024127 := by
  unfold tailWord_7233253
  simp only [CollatzResearch.WordTrace]
  refine ⟨263818410464167197106968413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175878940309444798071312275 263818410464167197106968413)
  ·
    refine ⟨98931903924062698915113155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263818410464167197106968413 98931903924062698915113155)
    ·
      refine ⟨148397855886094048372669733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98931903924062698915113155 148397855886094048372669733)
      ·
        refine ⟨27824597978642634069875575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148397855886094048372669733 27824597978642634069875575)
        ·
          refine ⟨41736896967963951104813363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27824597978642634069875575 41736896967963951104813363)
          ·
            refine ⟨62605345451945926657220045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41736896967963951104813363 62605345451945926657220045)
            ·
              refine ⟨23477004544479722496457517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62605345451945926657220045 23477004544479722496457517)
              ·
                refine ⟨8803876704179895936171569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23477004544479722496457517 8803876704179895936171569)
                ·
                  refine ⟨6602907528134921952128677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8803876704179895936171569 6602907528134921952128677)
                  ·
                    refine ⟨1238045161525297866024127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602907528134921952128677 1238045161525297866024127)
                    ·
                      rfl

theorem cell23_7233253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_7233253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233253 prefixEnd_7233253 := by exact prefixLift 7233253
  have htrace : WordTrace (prefixWord ++ tailWord_7233253) baseStart_7233253 baseEnd_7233253 := by
    simpa [prefixWord, tailWord_7233253, baseEnd_7233253] using wordTrace_append hprefix tailTrace_7233253
  have hstable : (prefixWord ++ tailWord_7233253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233253).length < 2 ^ (prefixWord ++ tailWord_7233253).sum := by decide
  have hdescent : baseEnd_7233253 < baseStart_7233253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233256 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7233256 : Nat := 118140960795 + 7233256 * 2 ^ 59
def prefixEnd_7233256 : Nat := 4983230072969 + 3 ^ 40 * 7233256 * 2
def baseEnd_7233256 : Nat := 3714137025017857086334867

theorem tailTrace_7233256 : CollatzResearch.WordTrace tailWord_7233256 prefixEnd_7233256 3714137025017857086334867 := by
  unfold tailWord_7233256
  simp only [CollatzResearch.WordTrace]
  refine ⟨131909259941578164309663811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175879013255437552412885081 131909259941578164309663811)
  ·
    refine ⟨197863889912367246464495717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131909259941578164309663811 197863889912367246464495717)
    ·
      refine ⟨37099479358568858712092947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197863889912367246464495717 37099479358568858712092947)
      ·
        refine ⟨55649219037853288068139421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37099479358568858712092947 55649219037853288068139421)
        ·
          refine ⟨20868457139194983025552283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55649219037853288068139421 20868457139194983025552283)
          ·
            refine ⟨31302685708792474538328425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20868457139194983025552283 31302685708792474538328425)
            ·
              refine ⟨23477014281594355903746319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31302685708792474538328425 23477014281594355903746319)
              ·
                refine ⟨35215521422391533855619479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23477014281594355903746319 35215521422391533855619479)
                ·
                  refine ⟨52823282133587300783429219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35215521422391533855619479 52823282133587300783429219)
                  ·
                    refine ⟨79234923200380951175143829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52823282133587300783429219 79234923200380951175143829)
                    ·
                      refine ⟨3714137025017857086334867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79234923200380951175143829 3714137025017857086334867)
                      ·
                        rfl

theorem cell23_7233256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7233256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233256 prefixEnd_7233256 := by exact prefixLift 7233256
  have htrace : WordTrace (prefixWord ++ tailWord_7233256) baseStart_7233256 baseEnd_7233256 := by
    simpa [prefixWord, tailWord_7233256, baseEnd_7233256] using wordTrace_append hprefix tailTrace_7233256
  have hstable : (prefixWord ++ tailWord_7233256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233256).length < 2 ^ (prefixWord ++ tailWord_7233256).sum := by decide
  have hdescent : baseEnd_7233256 < baseStart_7233256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233294 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7233294 : Nat := 118140960795 + 7233294 * 2 ^ 59
def prefixEnd_7233294 : Nat := 4983230072969 + 3 ^ 40 * 7233294 * 2
def baseEnd_7233294 : Nat := 3714156537282727937659693

theorem tailTrace_7233294 : CollatzResearch.WordTrace tailWord_7233294 prefixEnd_7233294 3714156537282727937659693 := by
  unfold tailWord_7233294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977488232127332638651367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175879937238012440739473957 32977488232127332638651367)
  ·
    refine ⟨49466232348190998957977051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977488232127332638651367 49466232348190998957977051)
    ·
      refine ⟨74199348522286498436965577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49466232348190998957977051 74199348522286498436965577)
      ·
        refine ⟨55649511391714873827724183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74199348522286498436965577 55649511391714873827724183)
        ·
          refine ⟨83474267087572310741586275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55649511391714873827724183 83474267087572310741586275)
          ·
            refine ⟨125211400631358466112379413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83474267087572310741586275 125211400631358466112379413)
            ·
              refine ⟨5869284404594928099017785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125211400631358466112379413 5869284404594928099017785)
              ·
                refine ⟨4401963303446196074263339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869284404594928099017785 4401963303446196074263339)
                ·
                  refine ⟨6602944955169294111395009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401963303446196074263339 6602944955169294111395009)
                  ·
                    refine ⟨4952208716376970583546257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602944955169294111395009 4952208716376970583546257)
                    ·
                      refine ⟨3714156537282727937659693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952208716376970583546257 3714156537282727937659693)
                      ·
                        rfl

theorem cell23_7233294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7233294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233294 prefixEnd_7233294 := by exact prefixLift 7233294
  have htrace : WordTrace (prefixWord ++ tailWord_7233294) baseStart_7233294 baseEnd_7233294 := by
    simpa [prefixWord, tailWord_7233294, baseEnd_7233294] using wordTrace_append hprefix tailTrace_7233294
  have hstable : (prefixWord ++ tailWord_7233294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233294).length < 2 ^ (prefixWord ++ tailWord_7233294).sum := by decide
  have hdescent : baseEnd_7233294 < baseStart_7233294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233320 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7233320 : Nat := 118140960795 + 7233320 * 2 ^ 59
def prefixEnd_7233320 : Nat := 4983230072969 + 3 ^ 40 * 7233320 * 2
def baseEnd_7233320 : Nat := 3714169887779744835934573

theorem tailTrace_7233320 : CollatzResearch.WordTrace tailWord_7233320 prefixEnd_7233320 3714169887779744835934573 := by
  unfold tailWord_7233320
  simp only [CollatzResearch.WordTrace]
  refine ⟨131910427077462233774828707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175880569436616311699771609 131910427077462233774828707)
  ·
    refine ⟨197865640616193350662243061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131910427077462233774828707 197865640616193350662243061)
    ·
      refine ⟨18549903807768126624585287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197865640616193350662243061 18549903807768126624585287)
      ·
        refine ⟨27824855711652189936877931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549903807768126624585287 27824855711652189936877931)
        ·
          refine ⟨41737283567478284905316897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27824855711652189936877931 41737283567478284905316897)
          ·
            refine ⟨31302962675608713678987673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41737283567478284905316897 31302962675608713678987673)
            ·
              refine ⟨23477222006706535259240755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31302962675608713678987673 23477222006706535259240755)
              ·
                refine ⟨35215833010059802888861133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23477222006706535259240755 35215833010059802888861133)
                ·
                  refine ⟨13205937378772426083322925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35215833010059802888861133 13205937378772426083322925)
                  ·
                    refine ⟨4952226517039659781246097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13205937378772426083322925 4952226517039659781246097)
                    ·
                      refine ⟨3714169887779744835934573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952226517039659781246097 3714169887779744835934573)
                      ·
                        rfl

theorem cell23_7233320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7233320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233320 prefixEnd_7233320 := by exact prefixLift 7233320
  have htrace : WordTrace (prefixWord ++ tailWord_7233320) baseStart_7233320 baseEnd_7233320 := by
    simpa [prefixWord, tailWord_7233320, baseEnd_7233320] using wordTrace_append hprefix tailTrace_7233320
  have hstable : (prefixWord ++ tailWord_7233320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233320).length < 2 ^ (prefixWord ++ tailWord_7233320).sum := by decide
  have hdescent : baseEnd_7233320 < baseStart_7233320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233367 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_7233367 : Nat := 118140960795 + 7233367 * 2 ^ 59
def prefixEnd_7233367 : Nat := 4983230072969 + 3 ^ 40 * 7233367 * 2
def baseEnd_7233367 : Nat := 3714194021370506152046857

theorem tailTrace_7233367 : CollatzResearch.WordTrace tailWord_7233367 prefixEnd_7233367 3714194021370506152046857 := by
  unfold tailWord_7233367
  simp only [CollatzResearch.WordTrace]
  refine ⟨263822568385754194576618355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175881712257169463051078903 263822568385754194576618355)
  ·
    refine ⟨395733852578631291864927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263822568385754194576618355 395733852578631291864927533)
    ·
      refine ⟨148400194716986734449347825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395733852578631291864927533 148400194716986734449347825)
      ·
        refine ⟨111300146037740050837010869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148400194716986734449347825 111300146037740050837010869)
        ·
          refine ⟨10434388691038129765969769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111300146037740050837010869 10434388691038129765969769)
          ·
            refine ⟨7825791518278597324477327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10434388691038129765969769 7825791518278597324477327)
            ·
              refine ⟨11738687277417895986715991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825791518278597324477327 11738687277417895986715991)
              ·
                refine ⟨17608030916126843980073987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11738687277417895986715991 17608030916126843980073987)
                ·
                  refine ⟨26412046374190265970110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17608030916126843980073987 26412046374190265970110981)
                  ·
                    refine ⟨4952258695160674869395809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26412046374190265970110981 4952258695160674869395809)
                    ·
                      refine ⟨3714194021370506152046857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952258695160674869395809 3714194021370506152046857)
                      ·
                        rfl

theorem cell23_7233367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_7233367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233367 prefixEnd_7233367 := by exact prefixLift 7233367
  have htrace : WordTrace (prefixWord ++ tailWord_7233367) baseStart_7233367 baseEnd_7233367 := by
    simpa [prefixWord, tailWord_7233367, baseEnd_7233367] using wordTrace_append hprefix tailTrace_7233367
  have hstable : (prefixWord ++ tailWord_7233367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233367).length < 2 ^ (prefixWord ++ tailWord_7233367).sum := by decide
  have hdescent : baseEnd_7233367 < baseStart_7233367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233418 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7233418 : Nat := 118140960795 + 7233418 * 2 ^ 59
def prefixEnd_7233418 : Nat := 4983230072969 + 3 ^ 40 * 7233418 * 2
def baseEnd_7233418 : Nat := 3714220208883885452509123

theorem tailTrace_7233418 : CollatzResearch.WordTrace tailWord_7233418 prefixEnd_7233418 3714220208883885452509123 := by
  unfold tailWord_7233418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65956107127142357571681227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175882952339046286857816605 65956107127142357571681227)
  ·
    refine ⟨98934160690713536357521841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65956107127142357571681227 98934160690713536357521841)
    ·
      refine ⟨74200620518035152268141381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98934160690713536357521841 74200620518035152268141381)
      ·
        refine ⟨13912616347131591050276509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74200620518035152268141381 13912616347131591050276509)
        ·
          refine ⟨5217231130174346643853691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13912616347131591050276509 5217231130174346643853691)
          ·
            refine ⟨7825846695261519965780537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217231130174346643853691 7825846695261519965780537)
            ·
              refine ⟨5869385021446139974335403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825846695261519965780537 5869385021446139974335403)
              ·
                refine ⟨8804077532169209961503105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869385021446139974335403 8804077532169209961503105)
                ·
                  refine ⟨6603058149126907471127329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8804077532169209961503105 6603058149126907471127329)
                  ·
                    refine ⟨4952293611845180603345497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6603058149126907471127329 4952293611845180603345497)
                    ·
                      refine ⟨3714220208883885452509123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952293611845180603345497 3714220208883885452509123)
                      ·
                        rfl

theorem cell23_7233418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7233418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233418 prefixEnd_7233418 := by exact prefixLift 7233418
  have htrace : WordTrace (prefixWord ++ tailWord_7233418) baseStart_7233418 baseEnd_7233418 := by
    simpa [prefixWord, tailWord_7233418, baseEnd_7233418] using wordTrace_append hprefix tailTrace_7233418
  have hstable : (prefixWord ++ tailWord_7233418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233418).length < 2 ^ (prefixWord ++ tailWord_7233418).sum := by decide
  have hdescent : baseEnd_7233418 < baseStart_7233418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 4, 2]
def baseStart_7233423 : Nat := 118140960795 + 7233423 * 2 ^ 59
def prefixEnd_7233423 : Nat := 4983230072969 + 3 ^ 40 * 7233423 * 2
def baseEnd_7233423 : Nat := 3714222776287157932946599

theorem tailTrace_7233423 : CollatzResearch.WordTrace tailWord_7233423 prefixEnd_7233423 3714222776287157932946599 := by
  unfold tailWord_7233423
  simp only [CollatzResearch.WordTrace]
  refine ⟨263824610873551316140656923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175883073915700877427104615 263824610873551316140656923)
  ·
    refine ⟨395736916310326974210985385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263824610873551316140656923 395736916310326974210985385)
    ·
      refine ⟨296802687232745230658239039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395736916310326974210985385 296802687232745230658239039)
      ·
        refine ⟨445204030849117845987358559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296802687232745230658239039 445204030849117845987358559)
        ·
          refine ⟨667806046273676768981037839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445204030849117845987358559 667806046273676768981037839)
          ·
            refine ⟨1001709069410515153471556759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667806046273676768981037839 1001709069410515153471556759)
            ·
              refine ⟨1502563604115772730207335139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001709069410515153471556759 1502563604115772730207335139)
              ·
                refine ⟨2253845406173659095311002709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502563604115772730207335139 2253845406173659095311002709)
                ·
                  refine ⟨26412250853597567523175813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2253845406173659095311002709 26412250853597567523175813)
                  ·
                    refine ⟨4952297035049543910595465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26412250853597567523175813 4952297035049543910595465)
                    ·
                      refine ⟨3714222776287157932946599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952297035049543910595465 3714222776287157932946599)
                      ·
                        rfl

theorem cell23_7233423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4, 2].length) (baseStart_7233423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233423 prefixEnd_7233423 := by exact prefixLift 7233423
  have htrace : WordTrace (prefixWord ++ tailWord_7233423) baseStart_7233423 baseEnd_7233423 := by
    simpa [prefixWord, tailWord_7233423, baseEnd_7233423] using wordTrace_append hprefix tailTrace_7233423
  have hstable : (prefixWord ++ tailWord_7233423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233423).length < 2 ^ (prefixWord ++ tailWord_7233423).sum := by decide
  have hdescent : baseEnd_7233423 < baseStart_7233423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233433 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_7233433 : Nat := 118140960795 + 7233433 * 2 ^ 59
def prefixEnd_7233433 : Nat := 4983230072969 + 3 ^ 40 * 7233433 * 2
def baseEnd_7233433 : Nat := 1238075970364567631273851

theorem tailTrace_7233433 : CollatzResearch.WordTrace tailWord_7233433 prefixEnd_7233433 1238075970364567631273851 := by
  unfold tailWord_7233433
  simp only [CollatzResearch.WordTrace]
  refine ⟨263824975603515087848520953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175883317069010058565680635 263824975603515087848520953)
  ·
    refine ⟨197868731702636315886390715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263824975603515087848520953 197868731702636315886390715)
    ·
      refine ⟨296803097553954473829586073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197868731702636315886390715 296803097553954473829586073)
      ·
        refine ⟨222602323165465855372189555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296803097553954473829586073 222602323165465855372189555)
        ·
          refine ⟨333903484748198783058284333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222602323165465855372189555 333903484748198783058284333)
          ·
            refine ⟨125213806780574543646856625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333903484748198783058284333 125213806780574543646856625)
            ·
              refine ⟨93910355085430907735142469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125213806780574543646856625 93910355085430907735142469)
              ·
                refine ⟨17608191578518295200339213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93910355085430907735142469 17608191578518295200339213)
                ·
                  refine ⟨6603071841944360700127205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17608191578518295200339213 6603071841944360700127205)
                  ·
                    refine ⟨1238075970364567631273851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603071841944360700127205 1238075970364567631273851)
                    ·
                      rfl

theorem cell23_7233433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_7233433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233433 prefixEnd_7233433 := by exact prefixLift 7233433
  have htrace : WordTrace (prefixWord ++ tailWord_7233433) baseStart_7233433 baseEnd_7233433 := by
    simpa [prefixWord, tailWord_7233433, baseEnd_7233433] using wordTrace_append hprefix tailTrace_7233433
  have hstable : (prefixWord ++ tailWord_7233433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233433).length < 2 ^ (prefixWord ++ tailWord_7233433).sum := by decide
  have hdescent : baseEnd_7233433 < baseStart_7233433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233533 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_7233533 : Nat := 118140960795 + 7233533 * 2 ^ 59
def prefixEnd_7233533 : Nat := 4983230072969 + 3 ^ 40 * 7233533 * 2
def baseEnd_7233533 : Nat := 3714279259159152502571093

theorem tailTrace_7233533 : CollatzResearch.WordTrace tailWord_7233533 prefixEnd_7233533 3714279259159152502571093 := by
  unfold tailWord_7233533
  simp only [CollatzResearch.WordTrace]
  refine ⟨263828622903152804927161253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175885748602101869951440835 263828622903152804927161253)
  ·
    refine ⟨49467866794341150923842735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263828622903152804927161253 49467866794341150923842735)
    ·
      refine ⟨74201800191511726385764103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49467866794341150923842735 74201800191511726385764103)
      ·
        refine ⟨111302700287267589578646155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74201800191511726385764103 111302700287267589578646155)
        ·
          refine ⟨166954050430901384367969233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111302700287267589578646155 166954050430901384367969233)
          ·
            refine ⟨125215537823176038275976925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166954050430901384367969233 125215537823176038275976925)
            ·
              refine ⟨46955826683691014353491347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125215537823176038275976925 46955826683691014353491347)
              ·
                refine ⟨70433740025536521530237021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46955826683691014353491347 70433740025536521530237021)
                ·
                  refine ⟨26412652509576195573838883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70433740025536521530237021 26412652509576195573838883)
                  ·
                    refine ⟨39618978764364293360758325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26412652509576195573838883 39618978764364293360758325)
                    ·
                      refine ⟨3714279259159152502571093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39618978764364293360758325 3714279259159152502571093)
                      ·
                        rfl

theorem cell23_7233533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_7233533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233533 prefixEnd_7233533 := by exact prefixLift 7233533
  have htrace : WordTrace (prefixWord ++ tailWord_7233533) baseStart_7233533 baseEnd_7233533 := by
    simpa [prefixWord, tailWord_7233533, baseEnd_7233533] using wordTrace_append hprefix tailTrace_7233533
  have hstable : (prefixWord ++ tailWord_7233533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233533).length < 2 ^ (prefixWord ++ tailWord_7233533).sum := by decide
  have hdescent : baseEnd_7233533 < baseStart_7233533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233547 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 3, 2, 2]
def baseStart_7233547 : Nat := 118140960795 + 7233547 * 2 ^ 59
def prefixEnd_7233547 : Nat := 4983230072969 + 3 ^ 40 * 7233547 * 2
def baseEnd_7233547 : Nat := 3714286447888315447796029

theorem tailTrace_7233547 : CollatzResearch.WordTrace tailWord_7233547 prefixEnd_7233547 3714286447888315447796029 := by
  unfold tailWord_7233547
  simp only [CollatzResearch.WordTrace]
  refine ⟨263829133525102085318170895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175886089016734723545447263 263829133525102085318170895)
  ·
    refine ⟨395743700287653127977256343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263829133525102085318170895 395743700287653127977256343)
    ·
      refine ⟨593615550431479691965884515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395743700287653127977256343 593615550431479691965884515)
      ·
        refine ⟨890423325647219537948826773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593615550431479691965884515 890423325647219537948826773)
        ·
          refine ⟨41738593389713415841351255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 890423325647219537948826773 41738593389713415841351255)
          ·
            refine ⟨62607890084570123762026883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41738593389713415841351255 62607890084570123762026883)
            ·
              refine ⟨93911835126855185643040325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62607890084570123762026883 93911835126855185643040325)
              ·
                refine ⟨17608469086285347308070061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93911835126855185643040325 17608469086285347308070061)
                ·
                  refine ⟨6603175907357005240526273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17608469086285347308070061 6603175907357005240526273)
                  ·
                    refine ⟨4952381930517753930394705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6603175907357005240526273 4952381930517753930394705)
                    ·
                      refine ⟨3714286447888315447796029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952381930517753930394705 3714286447888315447796029)
                      ·
                        rfl

theorem cell23_7233547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2, 2].length) (baseStart_7233547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233547 prefixEnd_7233547 := by exact prefixLift 7233547
  have htrace : WordTrace (prefixWord ++ tailWord_7233547) baseStart_7233547 baseEnd_7233547 := by
    simpa [prefixWord, tailWord_7233547, baseEnd_7233547] using wordTrace_append hprefix tailTrace_7233547
  have hstable : (prefixWord ++ tailWord_7233547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233547).length < 2 ^ (prefixWord ++ tailWord_7233547).sum := by decide
  have hdescent : baseEnd_7233547 < baseStart_7233547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233590 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7233590 : Nat := 118140960795 + 7233590 * 2 ^ 59
def prefixEnd_7233590 : Nat := 4983230072969 + 3 ^ 40 * 7233590 * 2
def baseEnd_7233590 : Nat := 3714308527556458779558331

theorem tailTrace_7233590 : CollatzResearch.WordTrace tailWord_7233590 prefixEnd_7233590 3714308527556458779558331 := by
  unfold tailWord_7233590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489418866496643978874139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175887134575964202441324149 16489418866496643978874139)
  ·
    refine ⟨24734128299744965968311209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16489418866496643978874139 24734128299744965968311209)
    ·
      refine ⟨18550596224808724476233407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24734128299744965968311209 18550596224808724476233407)
      ·
        refine ⟨27825894337213086714350111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18550596224808724476233407 27825894337213086714350111)
        ·
          refine ⟨41738841505819630071525167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27825894337213086714350111 41738841505819630071525167)
          ·
            refine ⟨62608262258729445107287751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41738841505819630071525167 62608262258729445107287751)
            ·
              refine ⟨93912393388094167660931627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62608262258729445107287751 93912393388094167660931627)
              ·
                refine ⟨140868590082141251491397441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93912393388094167660931627 140868590082141251491397441)
                ·
                  refine ⟨105651442561605938618548081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140868590082141251491397441 105651442561605938618548081)
                  ·
                    refine ⟨79238581921204453963911061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105651442561605938618548081 79238581921204453963911061)
                    ·
                      refine ⟨3714308527556458779558331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79238581921204453963911061 3714308527556458779558331)
                      ·
                        rfl

theorem cell23_7233590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7233590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233590 prefixEnd_7233590 := by exact prefixLift 7233590
  have htrace : WordTrace (prefixWord ++ tailWord_7233590) baseStart_7233590 baseEnd_7233590 := by
    simpa [prefixWord, tailWord_7233590, baseEnd_7233590] using wordTrace_append hprefix tailTrace_7233590
  have hstable : (prefixWord ++ tailWord_7233590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233590).length < 2 ^ (prefixWord ++ tailWord_7233590).sum := by decide
  have hdescent : baseEnd_7233590 < baseStart_7233590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233603 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_7233603 : Nat := 118140960795 + 7233603 * 2 ^ 59
def prefixEnd_7233603 : Nat := 4983230072969 + 3 ^ 40 * 7233603 * 2
def baseEnd_7233603 : Nat := 3714315202804967228695771

theorem tailTrace_7233603 : CollatzResearch.WordTrace tailWord_7233603 prefixEnd_7233603 3714315202804967228695771 := by
  unfold tailWord_7233603
  simp only [CollatzResearch.WordTrace]
  refine ⟨263831176012899206882209463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175887450675266137921472975 263831176012899206882209463)
  ·
    refine ⟨395746764019348810323314195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263831176012899206882209463 395746764019348810323314195)
    ·
      refine ⟨593620146029023215484971293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395746764019348810323314195 593620146029023215484971293)
      ·
        refine ⟨222607554760883705806864235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593620146029023215484971293 222607554760883705806864235)
        ·
          refine ⟨333911332141325558710296353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222607554760883705806864235 333911332141325558710296353)
          ·
            refine ⟨250433499105994169032722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333911332141325558710296353 250433499105994169032722265)
            ·
              refine ⟨187825124329495626774541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250433499105994169032722265 187825124329495626774541699)
              ·
                refine ⟨281737686494243440161812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187825124329495626774541699 281737686494243440161812549)
                ·
                  refine ⟨52825816217670645030339853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281737686494243440161812549 52825816217670645030339853)
                  ·
                    refine ⟨19809681081626491886377445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52825816217670645030339853 19809681081626491886377445)
                    ·
                      refine ⟨3714315202804967228695771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19809681081626491886377445 3714315202804967228695771)
                      ·
                        rfl

theorem cell23_7233603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_7233603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233603 prefixEnd_7233603 := by exact prefixLift 7233603
  have htrace : WordTrace (prefixWord ++ tailWord_7233603) baseStart_7233603 baseEnd_7233603 := by
    simpa [prefixWord, tailWord_7233603, baseEnd_7233603] using wordTrace_append hprefix tailTrace_7233603
  have hstable : (prefixWord ++ tailWord_7233603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233603).length < 2 ^ (prefixWord ++ tailWord_7233603).sum := by decide
  have hdescent : baseEnd_7233603 < baseStart_7233603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233607 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_7233607 : Nat := 118140960795 + 7233607 * 2 ^ 59
def prefixEnd_7233607 : Nat := 4983230072969 + 3 ^ 40 * 7233607 * 2
def baseEnd_7233607 : Nat := 3714317256727585213045753

theorem tailTrace_7233607 : CollatzResearch.WordTrace tailWord_7233607 prefixEnd_7233607 3714317256727585213045753 := by
  unfold tailWord_7233607
  simp only [CollatzResearch.WordTrace]
  refine ⟨263831321904884715565355075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175887547936589810376903383 263831321904884715565355075)
  ·
    refine ⟨395746982857327073348032613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263831321904884715565355075 395746982857327073348032613)
    ·
      refine ⟨74202559285748826252756115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395746982857327073348032613 74202559285748826252756115)
      ·
        refine ⟨111303838928623239379134173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74202559285748826252756115 111303838928623239379134173)
        ·
          refine ⟨41738939598233714767175315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111303838928623239379134173 41738939598233714767175315)
          ·
            refine ⟨62608409397350572150762973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41738939598233714767175315 62608409397350572150762973)
            ·
              refine ⟨23478153524006464556536115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62608409397350572150762973 23478153524006464556536115)
              ·
                refine ⟨35217230286009696834804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23478153524006464556536115 35217230286009696834804173)
                ·
                  refine ⟨13206461357253636313051565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35217230286009696834804173 13206461357253636313051565)
                  ·
                    refine ⟨4952423008970113617394337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13206461357253636313051565 4952423008970113617394337)
                    ·
                      refine ⟨3714317256727585213045753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952423008970113617394337 3714317256727585213045753)
                      ·
                        rfl

theorem cell23_7233607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_7233607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233607 prefixEnd_7233607 := by exact prefixLift 7233607
  have htrace : WordTrace (prefixWord ++ tailWord_7233607) baseStart_7233607 baseEnd_7233607 := by
    simpa [prefixWord, tailWord_7233607, baseEnd_7233607] using wordTrace_append hprefix tailTrace_7233607
  have hstable : (prefixWord ++ tailWord_7233607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233607).length < 2 ^ (prefixWord ++ tailWord_7233607).sum := by decide
  have hdescent : baseEnd_7233607 < baseStart_7233607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233633 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_7233633 : Nat := 118140960795 + 7233633 * 2 ^ 59
def prefixEnd_7233633 : Nat := 4983230072969 + 3 ^ 40 * 7233633 * 2
def baseEnd_7233633 : Nat := 3714330607224602111320633

theorem tailTrace_7233633 : CollatzResearch.WordTrace tailWord_7233633 prefixEnd_7233633 3714330607224602111320633 := by
  unfold tailWord_7233633
  simp only [CollatzResearch.WordTrace]
  refine ⟨263832270202790522005801553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175888180135193681337201035 263832270202790522005801553)
  ·
    refine ⟨197874202652092891504351165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263832270202790522005801553 197874202652092891504351165)
    ·
      refine ⟨74202825994534834314131687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197874202652092891504351165 74202825994534834314131687)
      ·
        refine ⟨111304238991802251471197531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74202825994534834314131687 111304238991802251471197531)
        ·
          refine ⟨166956358487703377206796297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111304238991802251471197531 166956358487703377206796297)
          ·
            refine ⟨125217268865777532905097223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166956358487703377206796297 125217268865777532905097223)
            ·
              refine ⟨187825903298666299357645835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125217268865777532905097223 187825903298666299357645835)
              ·
                refine ⟨281738854947999449036468753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187825903298666299357645835 281738854947999449036468753)
                ·
                  refine ⟨211304141210999586777351565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281738854947999449036468753 211304141210999586777351565)
                  ·
                    refine ⟨79239052954124845041506837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211304141210999586777351565 79239052954124845041506837)
                    ·
                      refine ⟨3714330607224602111320633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79239052954124845041506837 3714330607224602111320633)
                      ·
                        rfl

theorem cell23_7233633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_7233633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233633 prefixEnd_7233633 := by exact prefixLift 7233633
  have htrace : WordTrace (prefixWord ++ tailWord_7233633) baseStart_7233633 baseEnd_7233633 := by
    simpa [prefixWord, tailWord_7233633, baseEnd_7233633] using wordTrace_append hprefix tailTrace_7233633
  have hstable : (prefixWord ++ tailWord_7233633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233633).length < 2 ^ (prefixWord ++ tailWord_7233633).sum := by decide
  have hdescent : baseEnd_7233633 < baseStart_7233633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233650 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7233650 : Nat := 118140960795 + 7233650 * 2 ^ 59
def prefixEnd_7233650 : Nat := 4983230072969 + 3 ^ 40 * 7233650 * 2
def baseEnd_7233650 : Nat := 3714339336395728544808055

theorem tailTrace_7233650 : CollatzResearch.WordTrace tailWord_7233650 prefixEnd_7233650 3714339336395728544808055 := by
  unfold tailWord_7233650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65958222560932233477292601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175888593495819289272780269 65958222560932233477292601)
  ·
    refine ⟨49468666920699175107969451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65958222560932233477292601 49468666920699175107969451)
    ·
      refine ⟨74203000381048762661954177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49468666920699175107969451 74203000381048762661954177)
      ·
        refine ⟨55652250285786571996465633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74203000381048762661954177 55652250285786571996465633)
        ·
          refine ⟨41739187714339928997349225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55652250285786571996465633 41739187714339928997349225)
          ·
            refine ⟨31304390785754946748011919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41739187714339928997349225 31304390785754946748011919)
            ·
              refine ⟨46956586178632420122017879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31304390785754946748011919 46956586178632420122017879)
              ·
                refine ⟨70434879267948630183026819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46956586178632420122017879 70434879267948630183026819)
                ·
                  refine ⟨105652318901922945274540229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70434879267948630183026819 105652318901922945274540229)
                  ·
                    refine ⟨19809809794110552238976293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105652318901922945274540229 19809809794110552238976293)
                    ·
                      refine ⟨3714339336395728544808055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19809809794110552238976293 3714339336395728544808055)
                      ·
                        rfl

theorem cell23_7233650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7233650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233650 prefixEnd_7233650 := by exact prefixLift 7233650
  have htrace : WordTrace (prefixWord ++ tailWord_7233650) baseStart_7233650 baseEnd_7233650 := by
    simpa [prefixWord, tailWord_7233650, baseEnd_7233650] using wordTrace_append hprefix tailTrace_7233650
  have hstable : (prefixWord ++ tailWord_7233650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233650).length < 2 ^ (prefixWord ++ tailWord_7233650).sum := by decide
  have hdescent : baseEnd_7233650 < baseStart_7233650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233654 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7233654 : Nat := 118140960795 + 7233654 * 2 ^ 59
def prefixEnd_7233654 : Nat := 4983230072969 + 3 ^ 40 * 7233654 * 2
def baseEnd_7233654 : Nat := 3714341390318346529158037

theorem tailTrace_7233654 : CollatzResearch.WordTrace tailWord_7233654 prefixEnd_7233654 3714341390318346529158037 := by
  unfold tailWord_7233654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489564758482152662019751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175888690757142961728210677 16489564758482152662019751)
  ·
    refine ⟨24734347137723228993029627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16489564758482152662019751 24734347137723228993029627)
    ·
      refine ⟨37101520706584843489544441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24734347137723228993029627 37101520706584843489544441)
      ·
        refine ⟨27826140529938632617158331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37101520706584843489544441 27826140529938632617158331)
        ·
          refine ⟨41739210794907948925737497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27826140529938632617158331 41739210794907948925737497)
          ·
            refine ⟨31304408096180961694303123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41739210794907948925737497 31304408096180961694303123)
            ·
              refine ⟨46956612144271442541454685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31304408096180961694303123 46956612144271442541454685)
              ·
                refine ⟨17608729554101790953045507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46956612144271442541454685 17608729554101790953045507)
                ·
                  refine ⟨26413094331152686429568261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17608729554101790953045507 26413094331152686429568261)
                  ·
                    refine ⟨4952455187091128705544049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26413094331152686429568261 4952455187091128705544049)
                    ·
                      refine ⟨3714341390318346529158037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952455187091128705544049 3714341390318346529158037)
                      ·
                        rfl

theorem cell23_7233654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7233654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233654 prefixEnd_7233654 := by exact prefixLift 7233654
  have htrace : WordTrace (prefixWord ++ tailWord_7233654) baseStart_7233654 baseEnd_7233654 := by
    simpa [prefixWord, tailWord_7233654, baseEnd_7233654] using wordTrace_append hprefix tailTrace_7233654
  have hstable : (prefixWord ++ tailWord_7233654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233654).length < 2 ^ (prefixWord ++ tailWord_7233654).sum := by decide
  have hdescent : baseEnd_7233654 < baseStart_7233654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233660 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 7]
def baseStart_7233660 : Nat := 118140960795 + 7233660 * 2 ^ 59
def prefixEnd_7233660 : Nat := 4983230072969 + 3 ^ 40 * 7233660 * 2
def baseEnd_7233660 : Nat := 412704941244697056187001

theorem tailTrace_7233660 : CollatzResearch.WordTrace tailWord_7233660 prefixEnd_7233660 412704941244697056187001 := by
  unfold tailWord_7233660
  simp only [CollatzResearch.WordTrace]
  refine ⟨131916627486846352808517217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175888836649128470411356289 131916627486846352808517217)
  ·
    refine ⟨98937470615134764606387913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131916627486846352808517217 98937470615134764606387913)
    ·
      refine ⟨74203102961351073454790935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98937470615134764606387913 74203102961351073454790935)
      ·
        refine ⟨111304654442026610182186403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74203102961351073454790935 111304654442026610182186403)
        ·
          refine ⟨166956981663039915273279605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111304654442026610182186403 166956981663039915273279605)
          ·
            refine ⟨15652217030909992056869963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166956981663039915273279605 15652217030909992056869963)
            ·
              refine ⟨23478325546364988085304945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15652217030909992056869963 23478325546364988085304945)
              ·
                refine ⟨17608744159773741063978709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23478325546364988085304945 17608744159773741063978709)
                ·
                  refine ⟨412704941244697056187001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17608744159773741063978709 412704941244697056187001)
                  ·
                    rfl

theorem cell23_7233660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_7233660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233660 prefixEnd_7233660 := by exact prefixLift 7233660
  have htrace : WordTrace (prefixWord ++ tailWord_7233660) baseStart_7233660 baseEnd_7233660 := by
    simpa [prefixWord, tailWord_7233660, baseEnd_7233660] using wordTrace_append hprefix tailTrace_7233660
  have hstable : (prefixWord ++ tailWord_7233660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233660).length < 2 ^ (prefixWord ++ tailWord_7233660).sum := by decide
  have hdescent : baseEnd_7233660 < baseStart_7233660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233688 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7233688 : Nat := 118140960795 + 7233688 * 2 ^ 59
def prefixEnd_7233688 : Nat := 4983230072969 + 3 ^ 40 * 7233688 * 2
def baseEnd_7233688 : Nat := 3714358848660599396132881

theorem tailTrace_7233688 : CollatzResearch.WordTrace tailWord_7233688 prefixEnd_7233688 3714358848660599396132881 := by
  unfold tailWord_7233688
  simp only [CollatzResearch.WordTrace]
  refine ⟨131917138108795633199526859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175889517478394177599369145 131917138108795633199526859)
  ·
    refine ⟨197875707163193449799290289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131917138108795633199526859 197875707163193449799290289)
    ·
      refine ⟨148406780372395087349467717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197875707163193449799290289 148406780372395087349467717)
      ·
        refine ⟨27826271319824078878025197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148406780372395087349467717 27826271319824078878025197)
        ·
          refine ⟨10434851744934029579259449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27826271319824078878025197 10434851744934029579259449)
          ·
            refine ⟨7826138808700522184444587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10434851744934029579259449 7826138808700522184444587)
            ·
              refine ⟨11739208213050783276666881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826138808700522184444587 11739208213050783276666881)
              ·
                refine ⟨8804406159788087457500161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11739208213050783276666881 8804406159788087457500161)
                ·
                  refine ⟨6603304619841065593125121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8804406159788087457500161 6603304619841065593125121)
                  ·
                    refine ⟨4952478464880799194843841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6603304619841065593125121 4952478464880799194843841)
                    ·
                      refine ⟨3714358848660599396132881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952478464880799194843841 3714358848660599396132881)
                      ·
                        rfl

theorem cell23_7233688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7233688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233688 prefixEnd_7233688 := by exact prefixLift 7233688
  have htrace : WordTrace (prefixWord ++ tailWord_7233688) baseStart_7233688 baseEnd_7233688 := by
    simpa [prefixWord, tailWord_7233688, baseEnd_7233688] using wordTrace_append hprefix tailTrace_7233688
  have hstable : (prefixWord ++ tailWord_7233688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233688).length < 2 ^ (prefixWord ++ tailWord_7233688).sum := by decide
  have hdescent : baseEnd_7233688 < baseStart_7233688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233694 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_7233694 : Nat := 118140960795 + 7233694 * 2 ^ 59
def prefixEnd_7233694 : Nat := 4983230072969 + 3 ^ 40 * 7233694 * 2
def baseEnd_7233694 : Nat := 412706881060502930295317

theorem tailTrace_7233694 : CollatzResearch.WordTrace tailWord_7233694 prefixEnd_7233694 412706881060502930295317 := by
  unfold tailWord_7233694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979311881946191177971517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175889663370379686282514757 32979311881946191177971517)
  ·
    refine ⟨12367241955729821691739319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32979311881946191177971517 12367241955729821691739319)
    ·
      refine ⟨18550862933594732537608979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367241955729821691739319 18550862933594732537608979)
      ·
        refine ⟨27826294400392098806413469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18550862933594732537608979 27826294400392098806413469)
        ·
          refine ⟨10434860400147037052405051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27826294400392098806413469 10434860400147037052405051)
          ·
            refine ⟨15652290600220555578607577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434860400147037052405051 15652290600220555578607577)
            ·
              refine ⟨11739217950165416683955683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15652290600220555578607577 11739217950165416683955683)
              ·
                refine ⟨17608826925248125025933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11739217950165416683955683 17608826925248125025933525)
                ·
                  refine ⟨412706881060502930295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17608826925248125025933525 412706881060502930295317)
                  ·
                    rfl

theorem cell23_7233694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_7233694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233694 prefixEnd_7233694 := by exact prefixLift 7233694
  have htrace : WordTrace (prefixWord ++ tailWord_7233694) baseStart_7233694 baseEnd_7233694 := by
    simpa [prefixWord, tailWord_7233694, baseEnd_7233694] using wordTrace_append hprefix tailTrace_7233694
  have hstable : (prefixWord ++ tailWord_7233694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233694).length < 2 ^ (prefixWord ++ tailWord_7233694).sum := by decide
  have hdescent : baseEnd_7233694 < baseStart_7233694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233754 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_7233754 : Nat := 118140960795 + 7233754 * 2 ^ 59
def prefixEnd_7233754 : Nat := 4983230072969 + 3 ^ 40 * 7233754 * 2
def baseEnd_7233754 : Nat := 1238130912794598712635859

theorem tailTrace_7233754 : CollatzResearch.WordTrace tailWord_7233754 prefixEnd_7233754 1238130912794598712635859 := by
  unfold tailWord_7233754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65959170858838039917739079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175891122290234773113970877 65959170858838039917739079)
  ·
    refine ⟨98938756288257059876608619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65959170858838039917739079 98938756288257059876608619)
    ·
      refine ⟨148408134432385589814912929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98938756288257059876608619 148408134432385589814912929)
      ·
        refine ⟨111306100824289192361184697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148408134432385589814912929 111306100824289192361184697)
        ·
          refine ⟨83479575618216894270888523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111306100824289192361184697 83479575618216894270888523)
          ·
            refine ⟨125219363427325341406332785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83479575618216894270888523 125219363427325341406332785)
            ·
              refine ⟨93914522570494006054749589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125219363427325341406332785 93914522570494006054749589)
              ·
                refine ⟨4402243245491906533816387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93914522570494006054749589 4402243245491906533816387)
                ·
                  refine ⟨6603364868237859800724581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402243245491906533816387 6603364868237859800724581)
                  ·
                    refine ⟨1238130912794598712635859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603364868237859800724581 1238130912794598712635859)
                    ·
                      rfl

theorem cell23_7233754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_7233754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233754 prefixEnd_7233754 := by exact prefixLift 7233754
  have htrace : WordTrace (prefixWord ++ tailWord_7233754) baseStart_7233754 baseEnd_7233754 := by
    simpa [prefixWord, tailWord_7233754, baseEnd_7233754] using wordTrace_append hprefix tailTrace_7233754
  have hstable : (prefixWord ++ tailWord_7233754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233754).length < 2 ^ (prefixWord ++ tailWord_7233754).sum := by decide
  have hdescent : baseEnd_7233754 < baseStart_7233754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233804 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_7233804 : Nat := 118140960795 + 7233804 * 2 ^ 59
def prefixEnd_7233804 : Nat := 4983230072969 + 3 ^ 40 * 7233804 * 2
def baseEnd_7233804 : Nat := 3714418412416520942282347

theorem tailTrace_7233804 : CollatzResearch.WordTrace tailWord_7233804 prefixEnd_7233804 3714418412416520942282347 := by
  unfold tailWord_7233804
  simp only [CollatzResearch.WordTrace]
  refine ⟨131919253542585509105138233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175892338056780678806850977 131919253542585509105138233)
  ·
    refine ⟨98939440156939131828853675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131919253542585509105138233 98939440156939131828853675)
    ·
      refine ⟨148409160235408697743280513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98939440156939131828853675 148409160235408697743280513)
      ·
        refine ⟨111306870176556523307460385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148409160235408697743280513 111306870176556523307460385)
        ·
          refine ⟨83480152632417392480595289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111306870176556523307460385 83480152632417392480595289)
          ·
            refine ⟨62610114474313044360446467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83480152632417392480595289 62610114474313044360446467)
            ·
              refine ⟨93915171711469566540669701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62610114474313044360446467 93915171711469566540669701)
              ·
                refine ⟨17609094695900543726375569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93915171711469566540669701 17609094695900543726375569)
                ·
                  refine ⟨13206821021925407794781677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17609094695900543726375569 13206821021925407794781677)
                  ·
                    refine ⟨4952557883222027923043129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13206821021925407794781677 4952557883222027923043129)
                    ·
                      refine ⟨3714418412416520942282347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952557883222027923043129 3714418412416520942282347)
                      ·
                        rfl

theorem cell23_7233804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_7233804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233804 prefixEnd_7233804 := by exact prefixLift 7233804
  have htrace : WordTrace (prefixWord ++ tailWord_7233804) baseStart_7233804 baseEnd_7233804 := by
    simpa [prefixWord, tailWord_7233804, baseEnd_7233804] using wordTrace_append hprefix tailTrace_7233804
  have hstable : (prefixWord ++ tailWord_7233804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233804).length < 2 ^ (prefixWord ++ tailWord_7233804).sum := by decide
  have hdescent : baseEnd_7233804 < baseStart_7233804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233827 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 6]
def baseStart_7233827 : Nat := 118140960795 + 7233827 * 2 ^ 59
def prefixEnd_7233827 : Nat := 4983230072969 + 3 ^ 40 * 7233827 * 2
def baseEnd_7233827 : Nat := 1238143407490524784098247

theorem tailTrace_7233827 : CollatzResearch.WordTrace tailWord_7233827 prefixEnd_7233827 1238143407490524784098247 := by
  unfold tailWord_7233827
  simp only [CollatzResearch.WordTrace]
  refine ⟨263839345964087693138363735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175892897309391795425575823 263839345964087693138363735)
  ·
    refine ⟨395759018946131539707545603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263839345964087693138363735 395759018946131539707545603)
    ·
      refine ⟨593638528419197309561318405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395759018946131539707545603 593638528419197309561318405)
      ·
        refine ⟨111307224078599495542747201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593638528419197309561318405 111307224078599495542747201)
        ·
          refine ⟨83480418058949621657060401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111307224078599495542747201 83480418058949621657060401)
          ·
            refine ⟨62610313544212216242795301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83480418058949621657060401 62610313544212216242795301)
            ·
              refine ⟨11739433789539790545524119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62610313544212216242795301 11739433789539790545524119)
              ·
                refine ⟨17609150684309685818286179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11739433789539790545524119 17609150684309685818286179)
                ·
                  refine ⟨26413726026464528727429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17609150684309685818286179 26413726026464528727429269)
                  ·
                    refine ⟨1238143407490524784098247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26413726026464528727429269 1238143407490524784098247)
                    ·
                      rfl

theorem cell23_7233827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].length) (baseStart_7233827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233827 prefixEnd_7233827 := by exact prefixLift 7233827
  have htrace : WordTrace (prefixWord ++ tailWord_7233827) baseStart_7233827 baseEnd_7233827 := by
    simpa [prefixWord, tailWord_7233827, baseEnd_7233827] using wordTrace_append hprefix tailTrace_7233827
  have hstable : (prefixWord ++ tailWord_7233827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233827).length < 2 ^ (prefixWord ++ tailWord_7233827).sum := by decide
  have hdescent : baseEnd_7233827 < baseStart_7233827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233838 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7233838 : Nat := 118140960795 + 7233838 * 2 ^ 59
def prefixEnd_7233838 : Nat := 4983230072969 + 3 ^ 40 * 7233838 * 2
def baseEnd_7233838 : Nat := 3714435870758773809257191

theorem tailTrace_7233838 : CollatzResearch.WordTrace tailWord_7233838 prefixEnd_7233838 3714435870758773809257191 := by
  unfold tailWord_7233838
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979968395880980252126771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175893164778031894678009445 32979968395880980252126771)
  ·
    refine ⟨49469952593821470378190157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32979968395880980252126771 49469952593821470378190157)
    ·
      refine ⟨18551232222683051391821309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49469952593821470378190157 18551232222683051391821309)
      ·
        refine ⟨6956712083506144271932991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18551232222683051391821309 6956712083506144271932991)
        ·
          refine ⟨10435068125259216407899487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956712083506144271932991 10435068125259216407899487)
          ·
            refine ⟨15652602187888824611849231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435068125259216407899487 15652602187888824611849231)
            ·
              refine ⟨23478903281833236917773847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15652602187888824611849231 23478903281833236917773847)
              ·
                refine ⟨35218354922749855376660771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23478903281833236917773847 35218354922749855376660771)
                ·
                  refine ⟨52827532384124783064991157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35218354922749855376660771 52827532384124783064991157)
                  ·
                    refine ⟨4952581161011698412342921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52827532384124783064991157 4952581161011698412342921)
                    ·
                      refine ⟨3714435870758773809257191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952581161011698412342921 3714435870758773809257191)
                      ·
                        rfl

theorem cell23_7233838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7233838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233838 prefixEnd_7233838 := by exact prefixLift 7233838
  have htrace : WordTrace (prefixWord ++ tailWord_7233838) baseStart_7233838 baseEnd_7233838 := by
    simpa [prefixWord, tailWord_7233838, baseEnd_7233838] using wordTrace_append hprefix tailTrace_7233838
  have hstable : (prefixWord ++ tailWord_7233838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233838).length < 2 ^ (prefixWord ++ tailWord_7233838).sum := by decide
  have hdescent : baseEnd_7233838 < baseStart_7233838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233844 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7233844 : Nat := 118140960795 + 7233844 * 2 ^ 59
def prefixEnd_7233844 : Nat := 4983230072969 + 3 ^ 40 * 7233844 * 2
def baseEnd_7233844 : Nat := 1238146317214233595260721

theorem tailTrace_7233844 : CollatzResearch.WordTrace tailWord_7233844 prefixEnd_7233844 1238146317214233595260721 := by
  unfold tailWord_7233844
  simp only [CollatzResearch.WordTrace]
  refine ⟨131919983002513052520866293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175893310670017403361155057 131919983002513052520866293)
  ·
    refine ⟨12367498406485598673831215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131919983002513052520866293 12367498406485598673831215)
    ·
      refine ⟨18551247609728398010746823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367498406485598673831215 18551247609728398010746823)
      ·
        refine ⟨27826871414592597016120235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551247609728398010746823 27826871414592597016120235)
        ·
          refine ⟨41740307121888895524180353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27826871414592597016120235 41740307121888895524180353)
          ·
            refine ⟨31305230341416671643135265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41740307121888895524180353 31305230341416671643135265)
            ·
              refine ⟨23478922756062503732351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31305230341416671643135265 23478922756062503732351449)
              ·
                refine ⟨17609192067046877799263587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23478922756062503732351449 17609192067046877799263587)
                ·
                  refine ⟨26413788100570316698895381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17609192067046877799263587 26413788100570316698895381)
                  ·
                    refine ⟨1238146317214233595260721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26413788100570316698895381 1238146317214233595260721)
                    ·
                      rfl

theorem cell23_7233844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7233844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233844 prefixEnd_7233844 := by exact prefixLift 7233844
  have htrace : WordTrace (prefixWord ++ tailWord_7233844) baseStart_7233844 baseEnd_7233844 := by
    simpa [prefixWord, tailWord_7233844, baseEnd_7233844] using wordTrace_append hprefix tailTrace_7233844
  have hstable : (prefixWord ++ tailWord_7233844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233844).length < 2 ^ (prefixWord ++ tailWord_7233844).sum := by decide
  have hdescent : baseEnd_7233844 < baseStart_7233844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233868 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7233868 : Nat := 118140960795 + 7233868 * 2 ^ 59
def prefixEnd_7233868 : Nat := 4983230072969 + 3 ^ 40 * 7233868 * 2
def baseEnd_7233868 : Nat := 3714451275178408691882053

theorem tailTrace_7233868 : CollatzResearch.WordTrace tailWord_7233868 prefixEnd_7233868 3714451275178408691882053 := by
  unfold tailWord_7233868
  simp only [CollatzResearch.WordTrace]
  refine ⟨131920420678469578570303129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175893894237959438093737505 131920420678469578570303129)
  ·
    refine ⟨98940315508852183927727347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131920420678469578570303129 98940315508852183927727347)
    ·
      refine ⟨148410473263278275891591021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98940315508852183927727347 148410473263278275891591021)
      ·
        refine ⟨55653927473729353459346633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148410473263278275891591021 55653927473729353459346633)
        ·
          refine ⟨41740445605297015094509975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55653927473729353459346633 41740445605297015094509975)
          ·
            refine ⟨62610668407945522641764963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41740445605297015094509975 62610668407945522641764963)
            ·
              refine ⟨93916002611918283962647445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62610668407945522641764963 93916002611918283962647445)
              ·
                refine ⟨4402312622433669560749099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93916002611918283962647445 4402312622433669560749099)
                ·
                  refine ⟨6603468933650504341123649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402312622433669560749099 6603468933650504341123649)
                  ·
                    refine ⟨4952601700237878255842737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6603468933650504341123649 4952601700237878255842737)
                    ·
                      refine ⟨3714451275178408691882053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952601700237878255842737 3714451275178408691882053)
                      ·
                        rfl

theorem cell23_7233868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7233868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233868 prefixEnd_7233868 := by exact prefixLift 7233868
  have htrace : WordTrace (prefixWord ++ tailWord_7233868) baseStart_7233868 baseEnd_7233868 := by
    simpa [prefixWord, tailWord_7233868, baseEnd_7233868] using wordTrace_append hprefix tailTrace_7233868
  have hstable : (prefixWord ++ tailWord_7233868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233868).length < 2 ^ (prefixWord ++ tailWord_7233868).sum := by decide
  have hdescent : baseEnd_7233868 < baseStart_7233868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233927 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_7233927 : Nat := 118140960795 + 7233927 * 2 ^ 59
def prefixEnd_7233927 : Nat := 4983230072969 + 3 ^ 40 * 7233927 * 2
def baseEnd_7233927 : Nat := 3714481570537023961044281

theorem tailTrace_7233927 : CollatzResearch.WordTrace tailWord_7233927 prefixEnd_7233927 3714481570537023961044281 := by
  unfold tailWord_7233927
  simp only [CollatzResearch.WordTrace]
  refine ⟨263842993263725410217004035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175895328842483606811336023 263842993263725410217004035)
  ·
    refine ⟨395764489895588115325506053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263842993263725410217004035 395764489895588115325506053)
    ·
      refine ⟨74205841855422771623532385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395764489895588115325506053 74205841855422771623532385)
      ·
        refine ⟨55654381391567078717649289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74205841855422771623532385 55654381391567078717649289)
        ·
          refine ⟨41740786043675309038236967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55654381391567078717649289 41740786043675309038236967)
          ·
            refine ⟨62611179065512963557355451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41740786043675309038236967 62611179065512963557355451)
            ·
              refine ⟨93916768598269445336033177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62611179065512963557355451 93916768598269445336033177)
              ·
                refine ⟨70437576448702084002024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93916768598269445336033177 70437576448702084002024883)
                ·
                  refine ⟨105656364673053126003037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70437576448702084002024883 105656364673053126003037325)
                  ·
                    refine ⟨39621136752394922251138997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105656364673053126003037325 39621136752394922251138997)
                    ·
                      refine ⟨3714481570537023961044281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39621136752394922251138997 3714481570537023961044281)
                      ·
                        rfl

theorem cell23_7233927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_7233927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233927 prefixEnd_7233927 := by exact prefixLift 7233927
  have htrace : WordTrace (prefixWord ++ tailWord_7233927) baseStart_7233927 baseEnd_7233927 := by
    simpa [prefixWord, tailWord_7233927, baseEnd_7233927] using wordTrace_append hprefix tailTrace_7233927
  have hstable : (prefixWord ++ tailWord_7233927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233927).length < 2 ^ (prefixWord ++ tailWord_7233927).sum := by decide
  have hdescent : baseEnd_7233927 < baseStart_7233927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233944 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7233944 : Nat := 118140960795 + 7233944 * 2 ^ 59
def prefixEnd_7233944 : Nat := 4983230072969 + 3 ^ 40 * 7233944 * 2
def baseEnd_7233944 : Nat := 3714490299708150394531703

theorem tailTrace_7233944 : CollatzResearch.WordTrace tailWord_7233944 prefixEnd_7233944 3714490299708150394531703 := by
  unfold tailWord_7233944
  simp only [CollatzResearch.WordTrace]
  refine ⟨131921806652331911060186443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175895742203109214746915257 131921806652331911060186443)
  ·
    refine ⟨197882709978497866590279665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131921806652331911060186443 197882709978497866590279665)
    ·
      refine ⟨148412032483873399942709749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197882709978497866590279665 148412032483873399942709749)
      ·
        refine ⟨13913628045363131244629039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148412032483873399942709749 13913628045363131244629039)
        ·
          refine ⟨20870442068044696866943559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913628045363131244629039 20870442068044696866943559)
          ·
            refine ⟨31305663102067045300415339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870442068044696866943559 31305663102067045300415339)
            ·
              refine ⟨46958494653100567950623009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31305663102067045300415339 46958494653100567950623009)
              ·
                refine ⟨35218870989825425962967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46958494653100567950623009 35218870989825425962967257)
                ·
                  refine ⟨26414153242369069472225443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35218870989825425962967257 26414153242369069472225443)
                  ·
                    refine ⟨39621229863553604208338165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26414153242369069472225443 39621229863553604208338165)
                    ·
                      refine ⟨3714490299708150394531703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39621229863553604208338165 3714490299708150394531703)
                      ·
                        rfl

theorem cell23_7233944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7233944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233944 prefixEnd_7233944 := by exact prefixLift 7233944
  have htrace : WordTrace (prefixWord ++ tailWord_7233944) baseStart_7233944 baseEnd_7233944 := by
    simpa [prefixWord, tailWord_7233944, baseEnd_7233944] using wordTrace_append hprefix tailTrace_7233944
  have hstable : (prefixWord ++ tailWord_7233944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233944).length < 2 ^ (prefixWord ++ tailWord_7233944).sum := by decide
  have hdescent : baseEnd_7233944 < baseStart_7233944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233964 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 5]
def baseStart_7233964 : Nat := 118140960795 + 7233964 * 2 ^ 59
def prefixEnd_7233964 : Nat := 4983230072969 + 3 ^ 40 * 7233964 * 2
def baseEnd_7233964 : Nat := 412722285480137812920179

theorem tailTrace_7233964 : CollatzResearch.WordTrace tailWord_7233964 prefixEnd_7233964 412722285480137812920179 := by
  unfold tailWord_7233964
  simp only [CollatzResearch.WordTrace]
  refine ⟨131922171382295682768050473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175896228509727577024067297 131922171382295682768050473)
  ·
    refine ⟨98941628536721762076037855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131922171382295682768050473 98941628536721762076037855)
    ·
      refine ⟨148412442805082643114056783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98941628536721762076037855 148412442805082643114056783)
      ·
        refine ⟨222618664207623964671085175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148412442805082643114056783 222618664207623964671085175)
        ·
          refine ⟨333927996311435947006627763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222618664207623964671085175 333927996311435947006627763)
          ·
            refine ⟨500891994467153920509941645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333927996311435947006627763 500891994467153920509941645)
            ·
              refine ⟨187834497925182720191228117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500891994467153920509941645 187834497925182720191228117)
              ·
                refine ⟨4402371045121470004481909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187834497925182720191228117 4402371045121470004481909)
                ·
                  refine ⟨412722285480137812920179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402371045121470004481909 412722285480137812920179)
                  ·
                    rfl

theorem cell23_7233964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_7233964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233964 prefixEnd_7233964 := by exact prefixLift 7233964
  have htrace : WordTrace (prefixWord ++ tailWord_7233964) baseStart_7233964 baseEnd_7233964 := by
    simpa [prefixWord, tailWord_7233964, baseEnd_7233964] using wordTrace_append hprefix tailTrace_7233964
  have hstable : (prefixWord ++ tailWord_7233964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233964).length < 2 ^ (prefixWord ++ tailWord_7233964).sum := by decide
  have hdescent : baseEnd_7233964 < baseStart_7233964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7233981 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 5]
def baseStart_7233981 : Nat := 118140960795 + 7233981 * 2 ^ 59
def prefixEnd_7233981 : Nat := 4983230072969 + 3 ^ 40 * 7233981 * 2
def baseEnd_7233981 : Nat := 412723255388040749974337

theorem tailTrace_7233981 : CollatzResearch.WordTrace tailWord_7233981 prefixEnd_7233981 412723255388040749974337 := by
  unfold tailWord_7233981
  simp only [CollatzResearch.WordTrace]
  refine ⟨263844962805529777439469797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175896641870353184959646531 263844962805529777439469797)
  ·
    refine ⟨49470930526036833269900587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263844962805529777439469797 49470930526036833269900587)
    ·
      refine ⟨74206395789055249904850881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49470930526036833269900587 74206395789055249904850881)
      ·
        refine ⟨55654796841791437428638161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74206395789055249904850881 55654796841791437428638161)
        ·
          refine ⟨41741097631343578071478621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55654796841791437428638161 41741097631343578071478621)
          ·
            refine ⟨15652911611753841776804483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41741097631343578071478621 15652911611753841776804483)
            ·
              refine ⟨23479367417630762665206725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15652911611753841776804483 23479367417630762665206725)
              ·
                refine ⟨4402381390805767999726261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23479367417630762665206725 4402381390805767999726261)
                ·
                  refine ⟨412723255388040749974337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402381390805767999726261 412723255388040749974337)
                  ·
                    rfl

theorem cell23_7233981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_7233981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7233981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7233981 prefixEnd_7233981 := by exact prefixLift 7233981
  have htrace : WordTrace (prefixWord ++ tailWord_7233981) baseStart_7233981 baseEnd_7233981 := by
    simpa [prefixWord, tailWord_7233981, baseEnd_7233981] using wordTrace_append hprefix tailTrace_7233981
  have hstable : (prefixWord ++ tailWord_7233981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7233981).length < 2 ^ (prefixWord ++ tailWord_7233981).sum := by decide
  have hdescent : baseEnd_7233981 < baseStart_7233981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7233981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234027 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_7234027 : Nat := 118140960795 + 7234027 * 2 ^ 59
def prefixEnd_7234027 : Nat := 4983230072969 + 3 ^ 40 * 7234027 * 2
def baseEnd_7234027 : Nat := 3714532918602473569793821

theorem tailTrace_7234027 : CollatzResearch.WordTrace tailWord_7234027 prefixEnd_7234027 3714532918602473569793821 := by
  unfold tailWord_7234027
  simp only [CollatzResearch.WordTrace]
  refine ⟨263846640563363127295644335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175897760375575418197096223 263846640563363127295644335)
  ·
    refine ⟨395769960845044690943466503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263846640563363127295644335 395769960845044690943466503)
    ·
      refine ⟨593654941267567036415199755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395769960845044690943466503 593654941267567036415199755)
      ·
        refine ⟨890482411901350554622799633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593654941267567036415199755 890482411901350554622799633)
        ·
          refine ⟨667861808926012915967099725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890482411901350554622799633 667861808926012915967099725)
          ·
            refine ⟨250448178347254843487662397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667861808926012915967099725 250448178347254843487662397)
            ·
              refine ⟨93918066880220566307873399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250448178347254843487662397 93918066880220566307873399)
              ·
                refine ⟨140877100320330849461810099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93918066880220566307873399 140877100320330849461810099)
                ·
                  refine ⟨211315650480496274192715149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140877100320330849461810099 211315650480496274192715149)
                  ·
                    refine ⟨79243368930186102822268181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211315650480496274192715149 79243368930186102822268181)
                    ·
                      refine ⟨3714532918602473569793821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79243368930186102822268181 3714532918602473569793821)
                      ·
                        rfl

theorem cell23_7234027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_7234027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234027 prefixEnd_7234027 := by exact prefixLift 7234027
  have htrace : WordTrace (prefixWord ++ tailWord_7234027) baseStart_7234027 baseEnd_7234027 := by
    simpa [prefixWord, tailWord_7234027, baseEnd_7234027] using wordTrace_append hprefix tailTrace_7234027
  have hstable : (prefixWord ++ tailWord_7234027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234027).length < 2 ^ (prefixWord ++ tailWord_7234027).sum := by decide
  have hdescent : baseEnd_7234027 < baseStart_7234027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234068 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7234068 : Nat := 118140960795 + 7234068 * 2 ^ 59
def prefixEnd_7234068 : Nat := 4983230072969 + 3 ^ 40 * 7234068 * 2
def baseEnd_7234068 : Nat := 3714553971309307909381133

theorem tailTrace_7234068 : CollatzResearch.WordTrace tailWord_7234068 prefixEnd_7234068 3714553971309307909381133 := by
  unfold tailWord_7234068
  simp only [CollatzResearch.WordTrace]
  refine ⟨131924067978107295648943429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175898757304143060865257905 131924067978107295648943429)
  ·
    refine ⟨24735762745895117934176893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131924067978107295648943429 24735762745895117934176893)
    ·
      refine ⟨9275911029710669225316335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24735762745895117934176893 9275911029710669225316335)
      ·
        refine ⟨13913866544566003837974503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275911029710669225316335 13913866544566003837974503)
        ·
          refine ⟨20870799816849005756961755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913866544566003837974503 20870799816849005756961755)
          ·
            refine ⟨31306199725273508635442633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870799816849005756961755 31306199725273508635442633)
            ·
              refine ⟨23479649793955131476581975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31306199725273508635442633 23479649793955131476581975)
              ·
                refine ⟨35219474690932697214872963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23479649793955131476581975 35219474690932697214872963)
                ·
                  refine ⟨52829212036399045822309445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35219474690932697214872963 52829212036399045822309445)
                  ·
                    refine ⟨9905477256824821091683021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52829212036399045822309445 9905477256824821091683021)
                    ·
                      refine ⟨3714553971309307909381133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905477256824821091683021 3714553971309307909381133)
                      ·
                        rfl

theorem cell23_7234068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7234068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234068 prefixEnd_7234068 := by exact prefixLift 7234068
  have htrace : WordTrace (prefixWord ++ tailWord_7234068) baseStart_7234068 baseEnd_7234068 := by
    simpa [prefixWord, tailWord_7234068, baseEnd_7234068] using wordTrace_append hprefix tailTrace_7234068
  have hstable : (prefixWord ++ tailWord_7234068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234068).length < 2 ^ (prefixWord ++ tailWord_7234068).sum := by decide
  have hdescent : baseEnd_7234068 < baseStart_7234068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234098 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_7234098 : Nat := 118140960795 + 7234098 * 2 ^ 59
def prefixEnd_7234098 : Nat := 4983230072969 + 3 ^ 40 * 7234098 * 2
def baseEnd_7234098 : Nat := 3714569375728942792005995

theorem tailTrace_7234098 : CollatzResearch.WordTrace tailWord_7234098 prefixEnd_7234098 3714569375728942792005995 := by
  unfold tailWord_7234098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65962307536526476605369737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175899486764070604280985965 65962307536526476605369737)
  ·
    refine ⟨49471730652394857454027303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65962307536526476605369737 49471730652394857454027303)
    ·
      refine ⟨74207595978592286181040955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49471730652394857454027303 74207595978592286181040955)
      ·
        refine ⟨111311393967888429271561433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74207595978592286181040955 111311393967888429271561433)
        ·
          refine ⟨83483545475916321953671075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111311393967888429271561433 83483545475916321953671075)
          ·
            refine ⟨125225318213874482930506613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83483545475916321953671075 125225318213874482930506613)
            ·
              refine ⟨11739873582550732774734995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125225318213874482930506613 11739873582550732774734995)
              ·
                refine ⟨17609810373826099162102493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11739873582550732774734995 17609810373826099162102493)
                ·
                  refine ⟨6603678890184787185788435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17609810373826099162102493 6603678890184787185788435)
                  ·
                    refine ⟨9905518335277180778682653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6603678890184787185788435 9905518335277180778682653)
                    ·
                      refine ⟨3714569375728942792005995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905518335277180778682653 3714569375728942792005995)
                      ·
                        rfl

theorem cell23_7234098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_7234098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234098 prefixEnd_7234098 := by exact prefixLift 7234098
  have htrace : WordTrace (prefixWord ++ tailWord_7234098) baseStart_7234098 baseEnd_7234098 := by
    simpa [prefixWord, tailWord_7234098, baseEnd_7234098] using wordTrace_append hprefix tailTrace_7234098
  have hstable : (prefixWord ++ tailWord_7234098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234098).length < 2 ^ (prefixWord ++ tailWord_7234098).sum := by decide
  have hdescent : baseEnd_7234098 < baseStart_7234098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234125 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7234125 : Nat := 118140960795 + 7234125 * 2 ^ 59
def prefixEnd_7234125 : Nat := 4983230072969 + 3 ^ 40 * 7234125 * 2
def baseEnd_7234125 : Nat := 3714583239706614186368371

theorem tailTrace_7234125 : CollatzResearch.WordTrace tailWord_7234125 prefixEnd_7234125 3714583239706614186368371 := by
  unfold tailWord_7234125
  simp only [CollatzResearch.WordTrace]
  refine ⟨263850214917008090032711829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175900143278005393355141219 263850214917008090032711829)
  ·
    refine ⟨12367978824234754220283367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263850214917008090032711829 12367978824234754220283367)
    ·
      refine ⟨18551968236352131330425051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367978824234754220283367 18551968236352131330425051)
      ·
        refine ⟨27827952354528196995637577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551968236352131330425051 27827952354528196995637577)
        ·
          refine ⟨20870964265896147746728183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27827952354528196995637577 20870964265896147746728183)
          ·
            refine ⟨31306446398844221620092275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870964265896147746728183 31306446398844221620092275)
            ·
              refine ⟨46959669598266332430138413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31306446398844221620092275 46959669598266332430138413)
              ·
                refine ⟨17609876099349874661301905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46959669598266332430138413 17609876099349874661301905)
                ·
                  refine ⟨13207407074512405995976429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17609876099349874661301905 13207407074512405995976429)
                  ·
                    refine ⟨4952777652942152248491161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13207407074512405995976429 4952777652942152248491161)
                    ·
                      refine ⟨3714583239706614186368371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952777652942152248491161 3714583239706614186368371)
                      ·
                        rfl

theorem cell23_7234125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7234125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234125 prefixEnd_7234125 := by exact prefixLift 7234125
  have htrace : WordTrace (prefixWord ++ tailWord_7234125) baseStart_7234125 baseEnd_7234125 := by
    simpa [prefixWord, tailWord_7234125, baseEnd_7234125] using wordTrace_append hprefix tailTrace_7234125
  have hstable : (prefixWord ++ tailWord_7234125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234125).length < 2 ^ (prefixWord ++ tailWord_7234125).sum := by decide
  have hdescent : baseEnd_7234125 < baseStart_7234125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234148 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_7234148 : Nat := 118140960795 + 7234148 * 2 ^ 59
def prefixEnd_7234148 : Nat := 4983230072969 + 3 ^ 40 * 7234148 * 2
def baseEnd_7234148 : Nat := 1238198349920555865460255

theorem tailTrace_7234148 : CollatzResearch.WordTrace tailWord_7234148 prefixEnd_7234148 1238198349920555865460255 := by
  unfold tailWord_7234148
  simp only [CollatzResearch.WordTrace]
  refine ⟨131925526897962382480399549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175900702530616509973866065 131925526897962382480399549)
  ·
    refine ⟨49472072586735893430149831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131925526897962382480399549 49472072586735893430149831)
    ·
      refine ⟨74208108880103840145224747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49472072586735893430149831 74208108880103840145224747)
      ·
        refine ⟨111312163320155760217837121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74208108880103840145224747 111312163320155760217837121)
        ·
          refine ⟨83484122490116820163377841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111312163320155760217837121 83484122490116820163377841)
          ·
            refine ⟨62613091867587615122533381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83484122490116820163377841 62613091867587615122533381)
            ·
              refine ⟨11739954725172677835475009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62613091867587615122533381 11739954725172677835475009)
              ·
                refine ⟨8804966043879508376606257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11739954725172677835475009 8804966043879508376606257)
                ·
                  refine ⟨6603724532909631282454693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8804966043879508376606257 6603724532909631282454693)
                  ·
                    refine ⟨1238198349920555865460255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603724532909631282454693 1238198349920555865460255)
                    ·
                      rfl

theorem cell23_7234148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_7234148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234148 prefixEnd_7234148 := by exact prefixLift 7234148
  have htrace : WordTrace (prefixWord ++ tailWord_7234148) baseStart_7234148 baseEnd_7234148 := by
    simpa [prefixWord, tailWord_7234148, baseEnd_7234148] using wordTrace_append hprefix tailTrace_7234148
  have hstable : (prefixWord ++ tailWord_7234148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234148).length < 2 ^ (prefixWord ++ tailWord_7234148).sum := by decide
  have hdescent : baseEnd_7234148 < baseStart_7234148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234149 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_7234149 : Nat := 118140960795 + 7234149 * 2 ^ 59
def prefixEnd_7234149 : Nat := 4983230072969 + 3 ^ 40 * 7234149 * 2
def baseEnd_7234149 : Nat := 3714595563242322092468261

theorem tailTrace_7234149 : CollatzResearch.WordTrace tailWord_7234149 prefixEnd_7234149 3714595563242322092468261 := by
  unfold tailWord_7234149
  simp only [CollatzResearch.WordTrace]
  refine ⟨263851090268921142131585501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175900726845947428087723667 263851090268921142131585501)
  ·
    refine ⟨98944158850845428299344563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263851090268921142131585501 98944158850845428299344563)
    ·
      refine ⟨148416238276268142449016845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98944158850845428299344563 148416238276268142449016845)
      ·
        refine ⟨55656089353600553418381317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148416238276268142449016845 55656089353600553418381317)
        ·
          refine ⟨10435516753800103765946497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55656089353600553418381317 10435516753800103765946497)
          ·
            refine ⟨7826637565350077824459873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435516753800103765946497 7826637565350077824459873)
            ·
              refine ⟨5869978174012558368344905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7826637565350077824459873 5869978174012558368344905)
              ·
                refine ⟨4402483630509418776258679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869978174012558368344905 4402483630509418776258679)
                ·
                  refine ⟨6603725445764128164388019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402483630509418776258679 6603725445764128164388019)
                  ·
                    refine ⟨9905588168646192246582029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6603725445764128164388019 9905588168646192246582029)
                    ·
                      refine ⟨3714595563242322092468261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905588168646192246582029 3714595563242322092468261)
                      ·
                        rfl

theorem cell23_7234149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_7234149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234149 prefixEnd_7234149 := by exact prefixLift 7234149
  have htrace : WordTrace (prefixWord ++ tailWord_7234149) baseStart_7234149 baseEnd_7234149 := by
    simpa [prefixWord, tailWord_7234149, baseEnd_7234149] using wordTrace_append hprefix tailTrace_7234149
  have hstable : (prefixWord ++ tailWord_7234149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234149).length < 2 ^ (prefixWord ++ tailWord_7234149).sum := by decide
  have hdescent : baseEnd_7234149 < baseStart_7234149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234158 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_7234158 : Nat := 118140960795 + 7234158 * 2 ^ 59
def prefixEnd_7234158 : Nat := 4983230072969 + 3 ^ 40 * 7234158 * 2
def baseEnd_7234158 : Nat := 3714600184568212557255719

theorem tailTrace_7234158 : CollatzResearch.WordTrace tailWord_7234158 prefixEnd_7234158 3714600184568212557255719 := by
  unfold tailWord_7234158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981427315736067083582891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175900945683925691112442085 32981427315736067083582891)
  ·
    refine ⟨49472140973604100625374337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32981427315736067083582891 49472140973604100625374337)
    ·
      refine ⟨37104105730203075469030753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49472140973604100625374337 37104105730203075469030753)
      ·
        refine ⟨27828079297652306601773065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37104105730203075469030753 27828079297652306601773065)
        ·
          refine ⟨20871059473239229951329799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27828079297652306601773065 20871059473239229951329799)
          ·
            refine ⟨31306589209858844926994699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20871059473239229951329799 31306589209858844926994699)
            ·
              refine ⟨46959883814788267390492049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31306589209858844926994699 46959883814788267390492049)
              ·
                refine ⟨35219912861091200542869037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46959883814788267390492049 35219912861091200542869037)
                ·
                  refine ⟨13207467322909200203575889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35219912861091200542869037 13207467322909200203575889)
                  ·
                    refine ⟨9905600492181900152681917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13207467322909200203575889 9905600492181900152681917)
                    ·
                      refine ⟨3714600184568212557255719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905600492181900152681917 3714600184568212557255719)
                      ·
                        rfl

theorem cell23_7234158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_7234158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234158 prefixEnd_7234158 := by exact prefixLift 7234158
  have htrace : WordTrace (prefixWord ++ tailWord_7234158) baseStart_7234158 baseEnd_7234158 := by
    simpa [prefixWord, tailWord_7234158, baseEnd_7234158] using wordTrace_append hprefix tailTrace_7234158
  have hstable : (prefixWord ++ tailWord_7234158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234158).length < 2 ^ (prefixWord ++ tailWord_7234158).sum := by decide
  have hdescent : baseEnd_7234158 < baseStart_7234158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234205 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_7234205 : Nat := 118140960795 + 7234205 * 2 ^ 59
def prefixEnd_7234205 : Nat := 4983230072969 + 3 ^ 40 * 7234205 * 2
def baseEnd_7234205 : Nat := 3714624318158973873368003

theorem tailTrace_7234205 : CollatzResearch.WordTrace tailWord_7234205 prefixEnd_7234205 3714624318158973873368003 := by
  unfold tailWord_7234205
  simp only [CollatzResearch.WordTrace]
  refine ⟨263853132756718263695624069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175902088504478842463749379 263853132756718263695624069)
  ·
    refine ⟨49472462391884674442929513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263853132756718263695624069 49472462391884674442929513)
    ·
      refine ⟨37104346793913505832197135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49472462391884674442929513 37104346793913505832197135)
      ·
        refine ⟨55656520190870258748295703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37104346793913505832197135 55656520190870258748295703)
        ·
          refine ⟨83484780286305388122443555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55656520190870258748295703 83484780286305388122443555)
          ·
            refine ⟨125227170429458082183665333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83484780286305388122443555 125227170429458082183665333)
            ·
              refine ⟨11740047227761695204718625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125227170429458082183665333 11740047227761695204718625)
              ·
                refine ⟨8805035420821271403538969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11740047227761695204718625 8805035420821271403538969)
                ·
                  refine ⟨6603776565615953552654227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805035420821271403538969 6603776565615953552654227)
                  ·
                    refine ⟨9905664848423930328981341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6603776565615953552654227 9905664848423930328981341)
                    ·
                      refine ⟨3714624318158973873368003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905664848423930328981341 3714624318158973873368003)
                      ·
                        rfl

theorem cell23_7234205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_7234205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234205 prefixEnd_7234205 := by exact prefixLift 7234205
  have htrace : WordTrace (prefixWord ++ tailWord_7234205) baseStart_7234205 baseEnd_7234205 := by
    simpa [prefixWord, tailWord_7234205, baseEnd_7234205] using wordTrace_append hprefix tailTrace_7234205
  have hstable : (prefixWord ++ tailWord_7234205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234205).length < 2 ^ (prefixWord ++ tailWord_7234205).sum := by decide
  have hdescent : baseEnd_7234205 < baseStart_7234205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234222 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7234222 : Nat := 118140960795 + 7234222 * 2 ^ 59
def prefixEnd_7234222 : Nat := 4983230072969 + 3 ^ 40 * 7234222 * 2
def baseEnd_7234222 : Nat := 3714633047330100306855425

theorem tailTrace_7234222 : CollatzResearch.WordTrace tailWord_7234222 prefixEnd_7234222 3714633047330100306855425 := by
  unfold tailWord_7234222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981719099707084449874115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175902501865104450399328613 32981719099707084449874115)
  ·
    refine ⟨49472578649560626674811173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32981719099707084449874115 49472578649560626674811173)
    ·
      refine ⟨9276108496792617501527095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49472578649560626674811173 9276108496792617501527095)
      ·
        refine ⟨13914162745188926252290643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276108496792617501527095 13914162745188926252290643)
        ·
          refine ⟨20871244117783389378435965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914162745188926252290643 20871244117783389378435965)
          ·
            refine ⟨7826716544168771016913487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20871244117783389378435965 7826716544168771016913487)
            ·
              refine ⟨11740074816253156525370231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826716544168771016913487 11740074816253156525370231)
              ·
                refine ⟨17610112224379734788055347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740074816253156525370231 17610112224379734788055347)
                ·
                  refine ⟨26415168336569602182083021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17610112224379734788055347 26415168336569602182083021)
                  ·
                    refine ⟨9905688126213600818281133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26415168336569602182083021 9905688126213600818281133)
                    ·
                      refine ⟨3714633047330100306855425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905688126213600818281133 3714633047330100306855425)
                      ·
                        rfl

theorem cell23_7234222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7234222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234222 prefixEnd_7234222 := by exact prefixLift 7234222
  have htrace : WordTrace (prefixWord ++ tailWord_7234222) baseStart_7234222 baseEnd_7234222 := by
    simpa [prefixWord, tailWord_7234222, baseEnd_7234222] using wordTrace_append hprefix tailTrace_7234222
  have hstable : (prefixWord ++ tailWord_7234222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234222).length < 2 ^ (prefixWord ++ tailWord_7234222).sum := by decide
  have hdescent : baseEnd_7234222 < baseStart_7234222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234328 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_7234328 : Nat := 118140960795 + 7234328 * 2 ^ 59
def prefixEnd_7234328 : Nat := 4983230072969 + 3 ^ 40 * 7234328 * 2
def baseEnd_7234328 : Nat := 1238229158759825630709979

theorem tailTrace_7234328 : CollatzResearch.WordTrace tailWord_7234328 prefixEnd_7234328 1238229158759825630709979 := by
  unfold tailWord_7234328
  simp only [CollatzResearch.WordTrace]
  refine ⟨131928809467636327851175819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175905079290181770468234425 131928809467636327851175819)
  ·
    refine ⟨197893214201454491776763729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131928809467636327851175819 197893214201454491776763729)
    ·
      refine ⟨148419910651090868832572797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197893214201454491776763729 148419910651090868832572797)
      ·
        refine ⟨55657466494159075812214799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148419910651090868832572797 55657466494159075812214799)
        ·
          refine ⟨83486199741238613718322199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55657466494159075812214799 83486199741238613718322199)
          ·
            refine ⟨125229299611857920577483299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83486199741238613718322199 125229299611857920577483299)
            ·
              refine ⟨187843949417786880866224949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125229299611857920577483299 187843949417786880866224949)
              ·
                refine ⟨17610370257917520081208589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187843949417786880866224949 17610370257917520081208589)
                ·
                  refine ⟨6603888846719070030453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17610370257917520081208589 6603888846719070030453221)
                  ·
                    refine ⟨1238229158759825630709979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603888846719070030453221 1238229158759825630709979)
                    ·
                      rfl

theorem cell23_7234328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_7234328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234328 prefixEnd_7234328 := by exact prefixLift 7234328
  have htrace : WordTrace (prefixWord ++ tailWord_7234328) baseStart_7234328 baseEnd_7234328 := by
    simpa [prefixWord, tailWord_7234328, baseEnd_7234328] using wordTrace_append hprefix tailTrace_7234328
  have hstable : (prefixWord ++ tailWord_7234328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234328).length < 2 ^ (prefixWord ++ tailWord_7234328).sum := by decide
  have hdescent : baseEnd_7234328 < baseStart_7234328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234335 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 4, 2]
def baseStart_7234335 : Nat := 118140960795 + 7234335 * 2 ^ 59
def prefixEnd_7234335 : Nat := 4983230072969 + 3 ^ 40 * 7234335 * 2
def baseEnd_7234335 : Nat := 3714691070644058364742405

theorem tailTrace_7234335 : CollatzResearch.WordTrace tailWord_7234335 prefixEnd_7234335 3714691070644058364742405 := by
  unfold tailWord_7234335
  simp only [CollatzResearch.WordTrace]
  refine ⟨263857874246247295897856459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175905249497498197265237639 263857874246247295897856459)
  ·
    refine ⟨395786811369370943846784689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263857874246247295897856459 395786811369370943846784689)
    ·
      refine ⟨296840108527028207885088517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395786811369370943846784689 296840108527028207885088517)
      ·
        refine ⟨55657520348817788978454097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296840108527028207885088517 55657520348817788978454097)
        ·
          refine ⟨41743140261613341733840573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55657520348817788978454097 41743140261613341733840573)
          ·
            refine ⟨15653677598105003150190215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41743140261613341733840573 15653677598105003150190215)
            ·
              refine ⟨23480516397157504725285323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15653677598105003150190215 23480516397157504725285323)
              ·
                refine ⟨35220774595736257087927985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23480516397157504725285323 35220774595736257087927985)
                ·
                  refine ⟨26415580946802192815945989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35220774595736257087927985 26415580946802192815945989)
                  ·
                    refine ⟨4952921427525411152989873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26415580946802192815945989 4952921427525411152989873)
                    ·
                      refine ⟨3714691070644058364742405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4952921427525411152989873 3714691070644058364742405)
                      ·
                        rfl

theorem cell23_7234335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_7234335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234335 prefixEnd_7234335 := by exact prefixLift 7234335
  have htrace : WordTrace (prefixWord ++ tailWord_7234335) baseStart_7234335 baseEnd_7234335 := by
    simpa [prefixWord, tailWord_7234335, baseEnd_7234335] using wordTrace_append hprefix tailTrace_7234335
  have hstable : (prefixWord ++ tailWord_7234335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234335).length < 2 ^ (prefixWord ++ tailWord_7234335).sum := by decide
  have hdescent : baseEnd_7234335 < baseStart_7234335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234349 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7234349 : Nat := 118140960795 + 7234349 * 2 ^ 59
def prefixEnd_7234349 : Nat := 4983230072969 + 3 ^ 40 * 7234349 * 2
def baseEnd_7234349 : Nat := 1238232753124407103322447

theorem tailTrace_7234349 : CollatzResearch.WordTrace tailWord_7234349 prefixEnd_7234349 1238232753124407103322447 := by
  unfold tailWord_7234349
  simp only [CollatzResearch.WordTrace]
  refine ⟨263858384868196576288866101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175905589912131050859244067 263858384868196576288866101)
  ·
    refine ⟨24736723581393429027081197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263858384868196576288866101 24736723581393429027081197)
    ·
      refine ⟨9276271343022535885155449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24736723581393429027081197 9276271343022535885155449)
      ·
        refine ⟨6957203507266901913866587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9276271343022535885155449 6957203507266901913866587)
        ·
          refine ⟨10435805260900352870799881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957203507266901913866587 10435805260900352870799881)
          ·
            refine ⟨7826853945675264653099911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435805260900352870799881 7826853945675264653099911)
            ·
              refine ⟨11740280918512896979649867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826853945675264653099911 11740280918512896979649867)
              ·
                refine ⟨17610421377769345469474801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740280918512896979649867 17610421377769345469474801)
                ·
                  refine ⟨13207816033327009102106101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17610421377769345469474801 13207816033327009102106101)
                  ·
                    refine ⟨1238232753124407103322447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13207816033327009102106101 1238232753124407103322447)
                    ·
                      rfl

theorem cell23_7234349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7234349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234349 prefixEnd_7234349 := by exact prefixLift 7234349
  have htrace : WordTrace (prefixWord ++ tailWord_7234349) baseStart_7234349 baseEnd_7234349 := by
    simpa [prefixWord, tailWord_7234349, baseEnd_7234349] using wordTrace_append hprefix tailTrace_7234349
  have hstable : (prefixWord ++ tailWord_7234349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234349).length < 2 ^ (prefixWord ++ tailWord_7234349).sum := by decide
  have hdescent : baseEnd_7234349 < baseStart_7234349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234355 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3]
def baseStart_7234355 : Nat := 118140960795 + 7234355 * 2 ^ 59
def prefixEnd_7234355 : Nat := 4983230072969 + 3 ^ 40 * 7234355 * 2
def baseEnd_7234355 : Nat := 3714701340257148286492313

theorem tailTrace_7234355 : CollatzResearch.WordTrace tailWord_7234355 prefixEnd_7234355 3714701340257148286492313 := by
  unfold tailWord_7234355
  simp only [CollatzResearch.WordTrace]
  refine ⟨263858603706174839313584519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175905735804116559542389679 263858603706174839313584519)
  ·
    refine ⟨395787905559262258970376779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263858603706174839313584519 395787905559262258970376779)
    ·
      refine ⟨593681858338893388455565169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395787905559262258970376779 593681858338893388455565169)
      ·
        refine ⟨445261393754170041341673877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593681858338893388455565169 445261393754170041341673877)
        ·
          refine ⟨20871627832226720687890963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445261393754170041341673877 20871627832226720687890963)
          ·
            refine ⟨31307441748340081031836445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20871627832226720687890963 31307441748340081031836445)
            ·
              refine ⟨11740290655627530386938667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31307441748340081031836445 11740290655627530386938667)
              ·
                refine ⟨17610435983441295580408001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740290655627530386938667 17610435983441295580408001)
                ·
                  refine ⟨13207826987580971685306001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17610435983441295580408001 13207826987580971685306001)
                  ·
                    refine ⟨9905870240685728763979501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13207826987580971685306001 9905870240685728763979501)
                    ·
                      refine ⟨3714701340257148286492313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9905870240685728763979501 3714701340257148286492313)
                      ·
                        rfl

theorem cell23_7234355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_7234355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234355 prefixEnd_7234355 := by exact prefixLift 7234355
  have htrace : WordTrace (prefixWord ++ tailWord_7234355) baseStart_7234355 baseEnd_7234355 := by
    simpa [prefixWord, tailWord_7234355, baseEnd_7234355] using wordTrace_append hprefix tailTrace_7234355
  have hstable : (prefixWord ++ tailWord_7234355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234355).length < 2 ^ (prefixWord ++ tailWord_7234355).sum := by decide
  have hdescent : baseEnd_7234355 < baseStart_7234355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234418 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_7234418 : Nat := 118140960795 + 7234418 * 2 ^ 59
def prefixEnd_7234418 : Nat := 4983230072969 + 3 ^ 40 * 7234418 * 2
def baseEnd_7234418 : Nat := 1238244563179460513334841

theorem tailTrace_7234418 : CollatzResearch.WordTrace tailWord_7234418 prefixEnd_7234418 1238244563179460513334841 := by
  unfold tailWord_7234418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65965225376236650268281977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175907267669964400715418605 65965225376236650268281977)
  ·
    refine ⟨49473919032177487701211483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65965225376236650268281977 49473919032177487701211483)
    ·
      refine ⟨74210878548266231551817225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49473919032177487701211483 74210878548266231551817225)
      ·
        refine ⟨55658158911199673663862919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74210878548266231551817225 55658158911199673663862919)
        ·
          refine ⟨83487238366799510495794379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55658158911199673663862919 83487238366799510495794379)
          ·
            refine ⟨125230857550199265743691569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83487238366799510495794379 125230857550199265743691569)
            ·
              refine ⟨93923143162649449307768677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125230857550199265743691569 93923143162649449307768677)
              ·
                refine ⟨17610589342996771745206627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93923143162649449307768677 17610589342996771745206627)
                ·
                  refine ⟨26415884014495157617809941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17610589342996771745206627 26415884014495157617809941)
                  ·
                    refine ⟨1238244563179460513334841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26415884014495157617809941 1238244563179460513334841)
                    ·
                      rfl

theorem cell23_7234418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_7234418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234418 prefixEnd_7234418 := by exact prefixLift 7234418
  have htrace : WordTrace (prefixWord ++ tailWord_7234418) baseStart_7234418 baseEnd_7234418 := by
    simpa [prefixWord, tailWord_7234418, baseEnd_7234418] using wordTrace_append hprefix tailTrace_7234418
  have hstable : (prefixWord ++ tailWord_7234418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234418).length < 2 ^ (prefixWord ++ tailWord_7234418).sum := by decide
  have hdescent : baseEnd_7234418 < baseStart_7234418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234422 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_7234422 : Nat := 118140960795 + 7234422 * 2 ^ 59
def prefixEnd_7234422 : Nat := 4983230072969 + 3 ^ 40 * 7234422 * 2
def baseEnd_7234422 : Nat := 1238245247820333174784835

theorem tailTrace_7234422 : CollatzResearch.WordTrace tailWord_7234422 prefixEnd_7234422 1238245247820333174784835 := by
  unfold tailWord_7234422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491315462308256859767095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175907364931288073170849013 16491315462308256859767095)
  ·
    refine ⟨24736973193462385289650643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16491315462308256859767095 24736973193462385289650643)
    ·
      refine ⟨37105459790193577934475965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24736973193462385289650643 37105459790193577934475965)
      ·
        refine ⟨13914547421322591725428487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37105459790193577934475965 13914547421322591725428487)
        ·
          refine ⟨20871821131983887588142731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914547421322591725428487 20871821131983887588142731)
          ·
            refine ⟨31307731697975831382214097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20871821131983887588142731 31307731697975831382214097)
            ·
              refine ⟨23480798773481873536660573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31307731697975831382214097 23480798773481873536660573)
              ·
                refine ⟨8805299540055702576247715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23480798773481873536660573 8805299540055702576247715)
                ·
                  refine ⟨13207949310083553864371573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805299540055702576247715 13207949310083553864371573)
                  ·
                    refine ⟨1238245247820333174784835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13207949310083553864371573 1238245247820333174784835)
                    ·
                      rfl

theorem cell23_7234422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_7234422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234422 prefixEnd_7234422 := by exact prefixLift 7234422
  have htrace : WordTrace (prefixWord ++ tailWord_7234422) baseStart_7234422 baseEnd_7234422 := by
    simpa [prefixWord, tailWord_7234422, baseEnd_7234422] using wordTrace_append hprefix tailTrace_7234422
  have hstable : (prefixWord ++ tailWord_7234422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234422).length < 2 ^ (prefixWord ++ tailWord_7234422).sum := by decide
  have hdescent : baseEnd_7234422 < baseStart_7234422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234425 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_7234425 : Nat := 118140960795 + 7234425 * 2 ^ 59
def prefixEnd_7234425 : Nat := 4983230072969 + 3 ^ 40 * 7234425 * 2
def baseEnd_7234425 : Nat := 3714737283902963012616991

theorem tailTrace_7234425 : CollatzResearch.WordTrace tailWord_7234425 prefixEnd_7234425 3714737283902963012616991 := by
  unfold tailWord_7234425
  simp only [CollatzResearch.WordTrace]
  refine ⟨263861156815921241268632729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175907437877280827512421819 263861156815921241268632729)
  ·
    refine ⟨197895867611940930951474547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263861156815921241268632729 197895867611940930951474547)
    ·
      refine ⟨296843801417911396427211821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197895867611940930951474547 296843801417911396427211821)
      ·
        refine ⟨111316425531716773660204433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296843801417911396427211821 111316425531716773660204433)
        ·
          refine ⟨83487319148787580245153325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111316425531716773660204433 83487319148787580245153325)
          ·
            refine ⟨31307744680795342591932497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83487319148787580245153325 31307744680795342591932497)
            ·
              refine ⟨23480808510596506943949373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31307744680795342591932497 23480808510596506943949373)
              ·
                refine ⟨8805303191473690103981015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23480808510596506943949373 8805303191473690103981015)
                ·
                  refine ⟨13207954787210535155971523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805303191473690103981015 13207954787210535155971523)
                  ·
                    refine ⟨19811932180815802733957285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13207954787210535155971523 19811932180815802733957285)
                    ·
                      refine ⟨3714737283902963012616991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19811932180815802733957285 3714737283902963012616991)
                      ·
                        rfl

theorem cell23_7234425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_7234425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234425 prefixEnd_7234425 := by exact prefixLift 7234425
  have htrace : WordTrace (prefixWord ++ tailWord_7234425) baseStart_7234425 baseEnd_7234425 := by
    simpa [prefixWord, tailWord_7234425, baseEnd_7234425] using wordTrace_append hprefix tailTrace_7234425
  have hstable : (prefixWord ++ tailWord_7234425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234425).length < 2 ^ (prefixWord ++ tailWord_7234425).sum := by decide
  have hdescent : baseEnd_7234425 < baseStart_7234425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234431 : List Nat := [1, 1, 2, 2, 1, 1, 15]
def baseStart_7234431 : Nat := 118140960795 + 7234431 * 2 ^ 59
def prefixEnd_7234431 : Nat := 4983230072969 + 3 ^ 40 * 7234431 * 2
def baseEnd_7234431 : Nat := 45860992157862839372123

theorem tailTrace_7234431 : CollatzResearch.WordTrace tailWord_7234431 prefixEnd_7234431 45860992157862839372123 := by
  unfold tailWord_7234431
  simp only [CollatzResearch.WordTrace]
  refine ⟨263861375653899504293351147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175907583769266336195567431 263861375653899504293351147)
  ·
    refine ⟨395792063480849256440026721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263861375653899504293351147 395792063480849256440026721)
    ·
      refine ⟨296844047610636942330020041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395792063480849256440026721 296844047610636942330020041)
      ·
        refine ⟨222633035707977706747515031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296844047610636942330020041 222633035707977706747515031)
        ·
          refine ⟨333949553561966560121272547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222633035707977706747515031 333949553561966560121272547)
          ·
            refine ⟨500924330342949840181908821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333949553561966560121272547 500924330342949840181908821)
            ·
              refine ⟨45860992157862839372123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 500924330342949840181908821 45860992157862839372123)
              ·
                rfl

theorem cell23_7234431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 15].length) (baseStart_7234431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234431 prefixEnd_7234431 := by exact prefixLift 7234431
  have htrace : WordTrace (prefixWord ++ tailWord_7234431) baseStart_7234431 baseEnd_7234431 := by
    simpa [prefixWord, tailWord_7234431, baseEnd_7234431] using wordTrace_append hprefix tailTrace_7234431
  have hstable : (prefixWord ++ tailWord_7234431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234431).length < 2 ^ (prefixWord ++ tailWord_7234431).sum := by decide
  have hdescent : baseEnd_7234431 < baseStart_7234431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234435 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 2, 4]
def baseStart_7234435 : Nat := 118140960795 + 7234435 * 2 ^ 59
def prefixEnd_7234435 : Nat := 4983230072969 + 3 ^ 40 * 7234435 * 2
def baseEnd_7234435 : Nat := 1238247472903169324497315

theorem tailTrace_7234435 : CollatzResearch.WordTrace tailWord_7234435 prefixEnd_7234435 1238247472903169324497315 := by
  unfold tailWord_7234435
  simp only [CollatzResearch.WordTrace]
  refine ⟨263861521545885012976496759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175907681030590008650997839 263861521545885012976496759)
  ·
    refine ⟨395792282318827519464745139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263861521545885012976496759 395792282318827519464745139)
    ·
      refine ⟨593688423478241279197117709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395792282318827519464745139 593688423478241279197117709)
      ·
        refine ⟨222633158804340479698919141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593688423478241279197117709 222633158804340479698919141)
        ·
          refine ⟨41743717275813839943547339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222633158804340479698919141 41743717275813839943547339)
          ·
            refine ⟨62615575913720759915321009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41743717275813839943547339 62615575913720759915321009)
            ·
              refine ⟨46961681935290569936490757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62615575913720759915321009 46961681935290569936490757)
              ·
                refine ⟨8805315362866981863092017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46961681935290569936490757 8805315362866981863092017)
                ·
                  refine ⟨6603986522150236397319013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805315362866981863092017 6603986522150236397319013)
                  ·
                    refine ⟨1238247472903169324497315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6603986522150236397319013 1238247472903169324497315)
                    ·
                      rfl

theorem cell23_7234435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 4].length) (baseStart_7234435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234435 prefixEnd_7234435 := by exact prefixLift 7234435
  have htrace : WordTrace (prefixWord ++ tailWord_7234435) baseStart_7234435 baseEnd_7234435 := by
    simpa [prefixWord, tailWord_7234435, baseEnd_7234435] using wordTrace_append hprefix tailTrace_7234435
  have hstable : (prefixWord ++ tailWord_7234435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234435).length < 2 ^ (prefixWord ++ tailWord_7234435).sum := by decide
  have hdescent : baseEnd_7234435 < baseStart_7234435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234452 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7234452 : Nat := 118140960795 + 7234452 * 2 ^ 59
def prefixEnd_7234452 : Nat := 4983230072969 + 3 ^ 40 * 7234452 * 2
def baseEnd_7234452 : Nat := 1238250382626878135659789

theorem tailTrace_7234452 : CollatzResearch.WordTrace tailWord_7234452 prefixEnd_7234452 1238250382626878135659789 := by
  unfold tailWord_7234452
  simp only [CollatzResearch.WordTrace]
  refine ⟨131931070793411712439932805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175908094391215616586577073 131931070793411712439932805)
  ·
    refine ⟨24737075773764696082487401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131931070793411712439932805 24737075773764696082487401)
    ·
      refine ⟨18552806830323522061865551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24737075773764696082487401 18552806830323522061865551)
      ·
        refine ⟨27829210245485283092798327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18552806830323522061865551 27829210245485283092798327)
        ·
          refine ⟨41743815368227924639197491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27829210245485283092798327 41743815368227924639197491)
          ·
            refine ⟨62615723052341886958796237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41743815368227924639197491 62615723052341886958796237)
            ·
              refine ⟨23480896144628207609548589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62615723052341886958796237 23480896144628207609548589)
              ·
                refine ⟨8805336054235577853580721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23480896144628207609548589 8805336054235577853580721)
                ·
                  refine ⟨6604002040676683390185541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805336054235577853580721 6604002040676683390185541)
                  ·
                    refine ⟨1238250382626878135659789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604002040676683390185541 1238250382626878135659789)
                    ·
                      rfl

theorem cell23_7234452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7234452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234452 prefixEnd_7234452 := by exact prefixLift 7234452
  have htrace : WordTrace (prefixWord ++ tailWord_7234452) baseStart_7234452 baseEnd_7234452 := by
    simpa [prefixWord, tailWord_7234452, baseEnd_7234452] using wordTrace_append hprefix tailTrace_7234452
  have hstable : (prefixWord ++ tailWord_7234452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234452).length < 2 ^ (prefixWord ++ tailWord_7234452).sum := by decide
  have hdescent : baseEnd_7234452 < baseStart_7234452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234545 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_7234545 : Nat := 118140960795 + 7234545 * 2 ^ 59
def prefixEnd_7234545 : Nat := 4983230072969 + 3 ^ 40 * 7234545 * 2
def baseEnd_7234545 : Nat := 3714798901581502543116439

theorem tailTrace_7234545 : CollatzResearch.WordTrace tailWord_7234545 prefixEnd_7234545 3714798901581502543116439 := by
  unfold tailWord_7234545
  simp only [CollatzResearch.WordTrace]
  refine ⟨263865533575486501763001089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175910355716991001175334059 263865533575486501763001089)
  ·
    refine ⟨197899150181614876322250817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263865533575486501763001089 197899150181614876322250817)
    ·
      refine ⟨148424362636211157241688113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197899150181614876322250817 148424362636211157241688113)
      ·
        refine ⟨111318271977158367931266085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148424362636211157241688113 111318271977158367931266085)
        ·
          refine ⟨20872175995717193987112391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111318271977158367931266085 20872175995717193987112391)
          ·
            refine ⟨31308263993575790980668587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872175995717193987112391 31308263993575790980668587)
            ·
              refine ⟨46962395990363686471002881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31308263993575790980668587 46962395990363686471002881)
              ·
                refine ⟨35221796992772764853252161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46962395990363686471002881 35221796992772764853252161)
                ·
                  refine ⟨26416347744579573639939121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35221796992772764853252161 26416347744579573639939121)
                  ·
                    refine ⟨19812260808434680229954341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26416347744579573639939121 19812260808434680229954341)
                    ·
                      refine ⟨3714798901581502543116439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19812260808434680229954341 3714798901581502543116439)
                      ·
                        rfl

theorem cell23_7234545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_7234545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234545 prefixEnd_7234545 := by exact prefixLift 7234545
  have htrace : WordTrace (prefixWord ++ tailWord_7234545) baseStart_7234545 baseEnd_7234545 := by
    simpa [prefixWord, tailWord_7234545, baseEnd_7234545] using wordTrace_append hprefix tailTrace_7234545
  have hstable : (prefixWord ++ tailWord_7234545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234545).length < 2 ^ (prefixWord ++ tailWord_7234545).sum := by decide
  have hdescent : baseEnd_7234545 < baseStart_7234545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234565 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_7234565 : Nat := 118140960795 + 7234565 * 2 ^ 59
def prefixEnd_7234565 : Nat := 4983230072969 + 3 ^ 40 * 7234565 * 2
def baseEnd_7234565 : Nat := 3714809171194592464866347

theorem tailTrace_7234565 : CollatzResearch.WordTrace tailWord_7234565 prefixEnd_7234565 3714809171194592464866347 := by
  unfold tailWord_7234565
  simp only [CollatzResearch.WordTrace]
  refine ⟨263866263035414045178729149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175910842023609363452486099 263866263035414045178729149)
  ·
    refine ⟨98949848638280266942023431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263866263035414045178729149 98949848638280266942023431)
    ·
      refine ⟨148424772957420400413035147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98949848638280266942023431 148424772957420400413035147)
      ·
        refine ⟨222637159436130600619552721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148424772957420400413035147 222637159436130600619552721)
        ·
          refine ⟨166977869577097950464664541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222637159436130600619552721 166977869577097950464664541)
          ·
            refine ⟨62616701091411731424249203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166977869577097950464664541 62616701091411731424249203)
            ·
              refine ⟨93925051637117597136373805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62616701091411731424249203 93925051637117597136373805)
              ·
                refine ⟨35221894363919098926140177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93925051637117597136373805 35221894363919098926140177)
                ·
                  refine ⟨26416420772939324194605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35221894363919098926140177 26416420772939324194605133)
                  ·
                    refine ⟨9906157789852246572976925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26416420772939324194605133 9906157789852246572976925)
                    ·
                      refine ⟨3714809171194592464866347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906157789852246572976925 3714809171194592464866347)
                      ·
                        rfl

theorem cell23_7234565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_7234565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234565 prefixEnd_7234565 := by exact prefixLift 7234565
  have htrace : WordTrace (prefixWord ++ tailWord_7234565) baseStart_7234565 baseEnd_7234565 := by
    simpa [prefixWord, tailWord_7234565, baseEnd_7234565] using wordTrace_append hprefix tailTrace_7234565
  have hstable : (prefixWord ++ tailWord_7234565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234565).length < 2 ^ (prefixWord ++ tailWord_7234565).sum := by decide
  have hdescent : baseEnd_7234565 < baseStart_7234565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234612 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7234612 : Nat := 118140960795 + 7234612 * 2 ^ 59
def prefixEnd_7234612 : Nat := 4983230072969 + 3 ^ 40 * 7234612 * 2
def baseEnd_7234612 : Nat := 3714833304785353780978631

theorem tailTrace_7234612 : CollatzResearch.WordTrace tailWord_7234612 prefixEnd_7234612 3714833304785353780978631 := by
  unfold tailWord_7234612
  simp only [CollatzResearch.WordTrace]
  refine ⟨131933988633121886102845045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175911984844162514803793393 131933988633121886102845045)
  ·
    refine ⟨12368811434355176822141723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131933988633121886102845045 12368811434355176822141723)
    ·
      refine ⟨18553217151532765233212585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12368811434355176822141723 18553217151532765233212585)
      ·
        refine ⟨13914912863649573924909439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18553217151532765233212585 13914912863649573924909439)
        ·
          refine ⟨20872369295474360887364159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914912863649573924909439 20872369295474360887364159)
          ·
            refine ⟨31308553943211541331046239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872369295474360887364159 31308553943211541331046239)
            ·
              refine ⟨46962830914817311996569359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31308553943211541331046239 46962830914817311996569359)
              ·
                refine ⟨70444246372225967994854039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46962830914817311996569359 70444246372225967994854039)
                ·
                  refine ⟨105666369558338951992281059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70444246372225967994854039 105666369558338951992281059)
                  ·
                    refine ⟨158499554337508427988421589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105666369558338951992281059 158499554337508427988421589)
                    ·
                      refine ⟨3714833304785353780978631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158499554337508427988421589 3714833304785353780978631)
                      ·
                        rfl

theorem cell23_7234612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7234612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234612 prefixEnd_7234612 := by exact prefixLift 7234612
  have htrace : WordTrace (prefixWord ++ tailWord_7234612) baseStart_7234612 baseEnd_7234612 := by
    simpa [prefixWord, tailWord_7234612, baseEnd_7234612] using wordTrace_append hprefix tailTrace_7234612
  have hstable : (prefixWord ++ tailWord_7234612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234612).length < 2 ^ (prefixWord ++ tailWord_7234612).sum := by decide
  have hdescent : baseEnd_7234612 < baseStart_7234612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234666 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_7234666 : Nat := 118140960795 + 7234666 * 2 ^ 59
def prefixEnd_7234666 : Nat := 4983230072969 + 3 ^ 40 * 7234666 * 2
def baseEnd_7234666 : Nat := 1238287010913565523234461

theorem tailTrace_7234666 : CollatzResearch.WordTrace tailWord_7234666 prefixEnd_7234666 1238287010913565523234461 := by
  unfold tailWord_7234666
  simp only [CollatzResearch.WordTrace]
  refine ⟨65967486702012034857038963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175913297872032092952103901 65967486702012034857038963)
  ·
    refine ⟨98951230053018052285558445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65967486702012034857038963 98951230053018052285558445)
    ·
      refine ⟨37106711269881769607084417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98951230053018052285558445 37106711269881769607084417)
      ·
        refine ⟨27830033452411327205313313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37106711269881769607084417 27830033452411327205313313)
        ·
          refine ⟨20872525089308495403984985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27830033452411327205313313 20872525089308495403984985)
          ·
            refine ⟨15654393816981371552988739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20872525089308495403984985 15654393816981371552988739)
            ·
              refine ⟨23481590725472057329483109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654393816981371552988739 23481590725472057329483109)
              ·
                refine ⟨4402798261026010749278083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23481590725472057329483109 4402798261026010749278083)
                ·
                  refine ⟨6604197391539016123917125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402798261026010749278083 6604197391539016123917125)
                  ·
                    refine ⟨1238287010913565523234461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604197391539016123917125 1238287010913565523234461)
                    ·
                      rfl

theorem cell23_7234666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_7234666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234666 prefixEnd_7234666 := by exact prefixLift 7234666
  have htrace : WordTrace (prefixWord ++ tailWord_7234666) baseStart_7234666 baseEnd_7234666 := by
    simpa [prefixWord, tailWord_7234666, baseEnd_7234666] using wordTrace_append hprefix tailTrace_7234666
  have hstable : (prefixWord ++ tailWord_7234666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234666).length < 2 ^ (prefixWord ++ tailWord_7234666).sum := by decide
  have hdescent : baseEnd_7234666 < baseStart_7234666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234685 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_7234685 : Nat := 118140960795 + 7234685 * 2 ^ 59
def prefixEnd_7234685 : Nat := 4983230072969 + 3 ^ 40 * 7234685 * 2
def baseEnd_7234685 : Nat := 3714870788873131995365795

theorem tailTrace_7234685 : CollatzResearch.WordTrace tailWord_7234685 prefixEnd_7234685 3714870788873131995365795 := by
  unfold tailWord_7234685
  simp only [CollatzResearch.WordTrace]
  refine ⟨263870639794979305673097509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175913759863319537115398339 263870639794979305673097509)
  ·
    refine ⟨49475744961558619813705783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263870639794979305673097509 49475744961558619813705783)
    ·
      refine ⟨74213617442337929720558675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49475744961558619813705783 74213617442337929720558675)
      ·
        refine ⟨111320426163506894580838013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74213617442337929720558675 111320426163506894580838013)
        ·
          refine ⟨41745159811315085467814255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111320426163506894580838013 41745159811315085467814255)
          ·
            refine ⟨62617739716972628201721383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41745159811315085467814255 62617739716972628201721383)
            ·
              refine ⟨93926609575458942302582075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62617739716972628201721383 93926609575458942302582075)
              ·
                refine ⟨140889914363188413453873113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93926609575458942302582075 140889914363188413453873113)
                ·
                  refine ⟨105667435772391310090404835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140889914363188413453873113 105667435772391310090404835)
                  ·
                    refine ⟨158501153658586965135607253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105667435772391310090404835 158501153658586965135607253)
                    ·
                      refine ⟨3714870788873131995365795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158501153658586965135607253 3714870788873131995365795)
                      ·
                        rfl

theorem cell23_7234685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_7234685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234685 prefixEnd_7234685 := by exact prefixLift 7234685
  have htrace : WordTrace (prefixWord ++ tailWord_7234685) baseStart_7234685 baseEnd_7234685 := by
    simpa [prefixWord, tailWord_7234685, baseEnd_7234685] using wordTrace_append hprefix tailTrace_7234685
  have hstable : (prefixWord ++ tailWord_7234685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234685).length < 2 ^ (prefixWord ++ tailWord_7234685).sum := by decide
  have hdescent : baseEnd_7234685 < baseStart_7234685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234689 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_7234689 : Nat := 118140960795 + 7234689 * 2 ^ 59
def prefixEnd_7234689 : Nat := 4983230072969 + 3 ^ 40 * 7234689 * 2
def baseEnd_7234689 : Nat := 3714872842795749979715777

theorem tailTrace_7234689 : CollatzResearch.WordTrace tailWord_7234689 prefixEnd_7234689 3714872842795749979715777 := by
  unfold tailWord_7234689
  simp only [CollatzResearch.WordTrace]
  refine ⟨263870785686964814356243121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175913857124643209570828747 263870785686964814356243121)
  ·
    refine ⟨197903089265223610767182341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263870785686964814356243121 197903089265223610767182341)
    ·
      refine ⟨37106829237229427018846689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197903089265223610767182341 37106829237229427018846689)
      ·
        refine ⟨27830121927922070264135017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37106829237229427018846689 27830121927922070264135017)
        ·
          refine ⟨20872591445941552698101263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27830121927922070264135017 20872591445941552698101263)
          ·
            refine ⟨31308887168912329047151895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872591445941552698101263 31308887168912329047151895)
            ·
              refine ⟨46963330753368493570727843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31308887168912329047151895 46963330753368493570727843)
              ·
                refine ⟨70444996130052740356091765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46963330753368493570727843 70444996130052740356091765)
                ·
                  refine ⟨6604218387192444408383603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70444996130052740356091765 6604218387192444408383603)
                  ·
                    refine ⟨9906327580788666612575405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604218387192444408383603 9906327580788666612575405)
                    ·
                      refine ⟨3714872842795749979715777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906327580788666612575405 3714872842795749979715777)
                      ·
                        rfl

theorem cell23_7234689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_7234689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234689 prefixEnd_7234689 := by exact prefixLift 7234689
  have htrace : WordTrace (prefixWord ++ tailWord_7234689) baseStart_7234689 baseEnd_7234689 := by
    simpa [prefixWord, tailWord_7234689, baseEnd_7234689] using wordTrace_append hprefix tailTrace_7234689
  have hstable : (prefixWord ++ tailWord_7234689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234689).length < 2 ^ (prefixWord ++ tailWord_7234689).sum := by decide
  have hdescent : baseEnd_7234689 < baseStart_7234689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234692 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_7234692 : Nat := 118140960795 + 7234692 * 2 ^ 59
def prefixEnd_7234692 : Nat := 4983230072969 + 3 ^ 40 * 7234692 * 2
def baseEnd_7234692 : Nat := 1238291461079237822659421

theorem tailTrace_7234692 : CollatzResearch.WordTrace tailWord_7234692 prefixEnd_7234692 1238291461079237822659421 := by
  unfold tailWord_7234692
  simp only [CollatzResearch.WordTrace]
  refine ⟨131935447552976972934301165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175913930070635963912401553 131935447552976972934301165)
  ·
    refine ⟨49475792832366364850362937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131935447552976972934301165 49475792832366364850362937)
    ·
      refine ⟨37106844624274773637772203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49475792832366364850362937 37106844624274773637772203)
      ·
        refine ⟨55660266936412160456658305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37106844624274773637772203 55660266936412160456658305)
        ·
          refine ⟨41745200202309120342493729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55660266936412160456658305 41745200202309120342493729)
          ·
            refine ⟨31308900151731840256870297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41745200202309120342493729 31308900151731840256870297)
            ·
              refine ⟨23481675113798880192652723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31308900151731840256870297 23481675113798880192652723)
              ·
                refine ⟨35222512670698320288979085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23481675113798880192652723 35222512670698320288979085)
                ·
                  refine ⟨13208442251511870108367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35222512670698320288979085 13208442251511870108367157)
                  ·
                    refine ⟨1238291461079237822659421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13208442251511870108367157 1238291461079237822659421)
                    ·
                      rfl

theorem cell23_7234692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_7234692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234692 prefixEnd_7234692 := by exact prefixLift 7234692
  have htrace : WordTrace (prefixWord ++ tailWord_7234692) baseStart_7234692 baseEnd_7234692 := by
    simpa [prefixWord, tailWord_7234692, baseEnd_7234692] using wordTrace_append hprefix tailTrace_7234692
  have hstable : (prefixWord ++ tailWord_7234692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234692).length < 2 ^ (prefixWord ++ tailWord_7234692).sum := by decide
  have hdescent : baseEnd_7234692 < baseStart_7234692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234732 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_7234732 : Nat := 118140960795 + 7234732 * 2 ^ 59
def prefixEnd_7234732 : Nat := 4983230072969 + 3 ^ 40 * 7234732 * 2
def baseEnd_7234732 : Nat := 3714894922463893311478079

theorem tailTrace_7234732 : CollatzResearch.WordTrace tailWord_7234732 prefixEnd_7234732 3714894922463893311478079 := by
  unfold tailWord_7234732
  simp only [CollatzResearch.WordTrace]
  refine ⟨131936177012904516350029225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175914902683872688466705633 131936177012904516350029225)
  ·
    refine ⟨98952132759678387262521919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131936177012904516350029225 98952132759678387262521919)
    ·
      refine ⟨148428199139517580893782879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98952132759678387262521919 148428199139517580893782879)
      ·
        refine ⟨222642298709276371340674319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148428199139517580893782879 222642298709276371340674319)
        ·
          refine ⟨333963448063914557011011479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222642298709276371340674319 333963448063914557011011479)
          ·
            refine ⟨500945172095871835516517219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333963448063914557011011479 500945172095871835516517219)
            ·
              refine ⟨751417758143807753274775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500945172095871835516517219 751417758143807753274775829)
              ·
                refine ⟨35222707412990988434755117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751417758143807753274775829 35222707412990988434755117)
                ·
                  refine ⟨13208515279871620663033169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35222707412990988434755117 13208515279871620663033169)
                  ·
                    refine ⟨9906386459903715497274877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13208515279871620663033169 9906386459903715497274877)
                    ·
                      refine ⟨3714894922463893311478079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906386459903715497274877 3714894922463893311478079)
                      ·
                        rfl

theorem cell23_7234732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_7234732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234732 prefixEnd_7234732 := by exact prefixLift 7234732
  have htrace : WordTrace (prefixWord ++ tailWord_7234732) baseStart_7234732 baseEnd_7234732 := by
    simpa [prefixWord, tailWord_7234732, baseEnd_7234732] using wordTrace_append hprefix tailTrace_7234732
  have hstable : (prefixWord ++ tailWord_7234732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234732).length < 2 ^ (prefixWord ++ tailWord_7234732).sum := by decide
  have hdescent : baseEnd_7234732 < baseStart_7234732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234749 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_7234749 : Nat := 118140960795 + 7234749 * 2 ^ 59
def prefixEnd_7234749 : Nat := 4983230072969 + 3 ^ 40 * 7234749 * 2
def baseEnd_7234749 : Nat := 3714903651635019744965501

theorem tailTrace_7234749 : CollatzResearch.WordTrace tailWord_7234749 prefixEnd_7234749 3714903651635019744965501 := by
  unfold tailWord_7234749
  simp only [CollatzResearch.WordTrace]
  refine ⟨263872974066747444603427301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175915316044498296402284867 263872974066747444603427301)
  ·
    refine ⟨49476182637515145863142619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263872974066747444603427301 49476182637515145863142619)
    ·
      refine ⟨74214273956272718794713929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49476182637515145863142619 74214273956272718794713929)
      ·
        refine ⟨55660705467204539096035447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74214273956272718794713929 55660705467204539096035447)
        ·
          refine ⟨83491058200806808644053171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55660705467204539096035447 83491058200806808644053171)
          ·
            refine ⟨125236587301210212966079757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83491058200806808644053171 125236587301210212966079757)
            ·
              refine ⟨46963720237953829862279909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125236587301210212966079757 46963720237953829862279909)
              ·
                refine ⟨8805697544616343099177483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46963720237953829862279909 8805697544616343099177483)
                ·
                  refine ⟨13208546316924514648766225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805697544616343099177483 13208546316924514648766225)
                  ·
                    refine ⟨9906409737693385986574669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13208546316924514648766225 9906409737693385986574669)
                    ·
                      refine ⟨3714903651635019744965501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906409737693385986574669 3714903651635019744965501)
                      ·
                        rfl

theorem cell23_7234749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_7234749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234749 prefixEnd_7234749 := by exact prefixLift 7234749
  have htrace : WordTrace (prefixWord ++ tailWord_7234749) baseStart_7234749 baseEnd_7234749 := by
    simpa [prefixWord, tailWord_7234749, baseEnd_7234749] using wordTrace_append hprefix tailTrace_7234749
  have hstable : (prefixWord ++ tailWord_7234749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234749).length < 2 ^ (prefixWord ++ tailWord_7234749).sum := by decide
  have hdescent : baseEnd_7234749 < baseStart_7234749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234752 : List Nat := [2, 1, 1, 2, 6, 1, 1, 9]
def baseStart_7234752 : Nat := 118140960795 + 7234752 * 2 ^ 59
def prefixEnd_7234752 : Nat := 4983230072969 + 3 ^ 40 * 7234752 * 2
def baseEnd_7234752 : Nat := 137589081188036416045481

theorem tailTrace_7234752 : CollatzResearch.WordTrace tailWord_7234752 prefixEnd_7234752 137589081188036416045481 := by
  unfold tailWord_7234752
  simp only [CollatzResearch.WordTrace]
  refine ⟨131936541742868288057893255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175915388990491050743857673 131936541742868288057893255)
  ·
    refine ⟨197904812614302432086839883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131936541742868288057893255 197904812614302432086839883)
    ·
      refine ⟨296857218921453648130259825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197904812614302432086839883 296857218921453648130259825)
      ·
        refine ⟨222642914191090236097694869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296857218921453648130259825 222642914191090236097694869)
        ·
          refine ⟨10436386602707354817079447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222642914191090236097694869 10436386602707354817079447)
          ·
            refine ⟨15654579904061032225619171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436386602707354817079447 15654579904061032225619171)
            ·
              refine ⟨23481869856091548338428757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654579904061032225619171 23481869856091548338428757)
              ·
                refine ⟨137589081188036416045481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23481869856091548338428757 137589081188036416045481)
                ·
                  rfl

theorem cell23_7234752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_7234752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234752 prefixEnd_7234752 := by exact prefixLift 7234752
  have htrace : WordTrace (prefixWord ++ tailWord_7234752) baseStart_7234752 baseEnd_7234752 := by
    simpa [prefixWord, tailWord_7234752, baseEnd_7234752] using wordTrace_append hprefix tailTrace_7234752
  have hstable : (prefixWord ++ tailWord_7234752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234752).length < 2 ^ (prefixWord ++ tailWord_7234752).sum := by decide
  have hdescent : baseEnd_7234752 < baseStart_7234752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234796 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_7234796 : Nat := 118140960795 + 7234796 * 2 ^ 59
def prefixEnd_7234796 : Nat := 4983230072969 + 3 ^ 40 * 7234796 * 2
def baseEnd_7234796 : Nat := 3714927785225781061077785

theorem tailTrace_7234796 : CollatzResearch.WordTrace tailWord_7234796 prefixEnd_7234796 3714927785225781061077785 := by
  unfold tailWord_7234796
  simp only [CollatzResearch.WordTrace]
  refine ⟨131937344148788585815194121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175916458865051447753592161 131937344148788585815194121)
  ·
    refine ⟨98953008111591439361395591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131937344148788585815194121 98953008111591439361395591)
    ·
      refine ⟨148429512167387159042093387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98953008111591439361395591 148429512167387159042093387)
      ·
        refine ⟨222644268251080738563140081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148429512167387159042093387 222644268251080738563140081)
        ·
          refine ⟨166983201188310553922355061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222644268251080738563140081 166983201188310553922355061)
          ·
            refine ⟨15654675111404114430220787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166983201188310553922355061 15654675111404114430220787)
            ·
              refine ⟨23482012667106171645331181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654675111404114430220787 23482012667106171645331181)
              ·
                refine ⟨8805754750164814366999193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23482012667106171645331181 8805754750164814366999193)
                ·
                  refine ⟨6604316062623610775249395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805754750164814366999193 6604316062623610775249395)
                  ·
                    refine ⟨9906474093935416162874093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604316062623610775249395 9906474093935416162874093)
                    ·
                      refine ⟨3714927785225781061077785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906474093935416162874093 3714927785225781061077785)
                      ·
                        rfl

theorem cell23_7234796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_7234796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234796 prefixEnd_7234796 := by exact prefixLift 7234796
  have htrace : WordTrace (prefixWord ++ tailWord_7234796) baseStart_7234796 baseEnd_7234796 := by
    simpa [prefixWord, tailWord_7234796, baseEnd_7234796] using wordTrace_append hprefix tailTrace_7234796
  have hstable : (prefixWord ++ tailWord_7234796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234796).length < 2 ^ (prefixWord ++ tailWord_7234796).sum := by decide
  have hdescent : baseEnd_7234796 < baseStart_7234796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234819 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 4, 2]
def baseStart_7234819 : Nat := 118140960795 + 7234819 * 2 ^ 59
def prefixEnd_7234819 : Nat := 4983230072969 + 3 ^ 40 * 7234819 * 2
def baseEnd_7234819 : Nat := 3714939595280834471090179

theorem tailTrace_7234819 : CollatzResearch.WordTrace tailWord_7234819 prefixEnd_7234819 3714939595280834471090179 := by
  unfold tailWord_7234819
  simp only [CollatzResearch.WordTrace]
  refine ⟨263875527176493846558475511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175917018117662564372317007 263875527176493846558475511)
  ·
    refine ⟨395813290764740769837713267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263875527176493846558475511 395813290764740769837713267)
    ·
      refine ⟨593719936147111154756569901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395813290764740769837713267 593719936147111154756569901)
      ·
        refine ⟨222644976055166683033713713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593719936147111154756569901 222644976055166683033713713)
        ·
          refine ⟨166983732041375012275285285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222644976055166683033713713 166983732041375012275285285)
          ·
            refine ⟨31309449757757814801615991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166983732041375012275285285 31309449757757814801615991)
            ·
              refine ⟨46964174636636722202423987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31309449757757814801615991 46964174636636722202423987)
              ·
                refine ⟨70446261954955083303635981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46964174636636722202423987 70446261954955083303635981)
                ·
                  refine ⟨26417348233108156238863493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70446261954955083303635981 26417348233108156238863493)
                  ·
                    refine ⟨4953252793707779294786905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26417348233108156238863493 4953252793707779294786905)
                    ·
                      refine ⟨3714939595280834471090179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953252793707779294786905 3714939595280834471090179)
                      ·
                        rfl

theorem cell23_7234819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_7234819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234819 prefixEnd_7234819 := by exact prefixLift 7234819
  have htrace : WordTrace (prefixWord ++ tailWord_7234819) baseStart_7234819 baseEnd_7234819 := by
    simpa [prefixWord, tailWord_7234819, baseEnd_7234819] using wordTrace_append hprefix tailTrace_7234819
  have hstable : (prefixWord ++ tailWord_7234819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234819).length < 2 ^ (prefixWord ++ tailWord_7234819).sum := by decide
  have hdescent : baseEnd_7234819 < baseStart_7234819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234853 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_7234853 : Nat := 118140960795 + 7234853 * 2 ^ 59
def prefixEnd_7234853 : Nat := 4983230072969 + 3 ^ 40 * 7234853 * 2
def baseEnd_7234853 : Nat := 3714957053623087338065023

theorem tailTrace_7234853 : CollatzResearch.WordTrace tailWord_7234853 prefixEnd_7234853 3714957053623087338065023 := by
  unfold tailWord_7234853
  simp only [CollatzResearch.WordTrace]
  refine ⟨263876767258370670365213213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175917844838913780243475475 263876767258370670365213213)
  ·
    refine ⟨98953787721889001386954955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263876767258370670365213213 98953787721889001386954955)
    ·
      refine ⟨148430681582833502080432433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98953787721889001386954955 148430681582833502080432433)
      ·
        refine ⟨111323011187125126560324325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148430681582833502080432433 111323011187125126560324325)
        ·
          refine ⟨20873064597585961230060811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111323011187125126560324325 20873064597585961230060811)
          ·
            refine ⟨31309596896378941845091217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20873064597585961230060811 31309596896378941845091217)
            ·
              refine ⟨23482197672284206383818413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31309596896378941845091217 23482197672284206383818413)
              ·
                refine ⟨8805824127106577393931905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23482197672284206383818413 8805824127106577393931905)
                ·
                  refine ⟨6604368095329933045448929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805824127106577393931905 6604368095329933045448929)
                  ·
                    refine ⟨4953276071497449784086697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6604368095329933045448929 4953276071497449784086697)
                    ·
                      refine ⟨3714957053623087338065023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953276071497449784086697 3714957053623087338065023)
                      ·
                        rfl

theorem cell23_7234853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_7234853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234853 prefixEnd_7234853 := by exact prefixLift 7234853
  have htrace : WordTrace (prefixWord ++ tailWord_7234853) baseStart_7234853 baseEnd_7234853 := by
    simpa [prefixWord, tailWord_7234853, baseEnd_7234853] using wordTrace_append hprefix tailTrace_7234853
  have hstable : (prefixWord ++ tailWord_7234853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234853).length < 2 ^ (prefixWord ++ tailWord_7234853).sum := by decide
  have hdescent : baseEnd_7234853 < baseStart_7234853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234876 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 5]
def baseStart_7234876 : Nat := 118140960795 + 7234876 * 2 ^ 59
def prefixEnd_7234876 : Nat := 4983230072969 + 3 ^ 40 * 7234876 * 2
def baseEnd_7234876 : Nat := 412774318186460083119713

theorem tailTrace_7234876 : CollatzResearch.WordTrace tailWord_7234876 prefixEnd_7234876 412774318186460083119713 := by
  unfold tailWord_7234876
  simp only [CollatzResearch.WordTrace]
  refine ⟨131938803068643672646650241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175918404091524896862200321 131938803068643672646650241)
  ·
    refine ⟨98954102301482754484987681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131938803068643672646650241 98954102301482754484987681)
    ·
      refine ⟨74215576726112065863740761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98954102301482754484987681 74215576726112065863740761)
      ·
        refine ⟨55661682544584049397805571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74215576726112065863740761 55661682544584049397805571)
        ·
          refine ⟨83492523816876074096708357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55661682544584049397805571 83492523816876074096708357)
          ·
            refine ⟨15654848215664263893132817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83492523816876074096708357 15654848215664263893132817)
            ·
              refine ⟨11741136161748197919849613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15654848215664263893132817 11741136161748197919849613)
              ·
                refine ⟨4402926060655574219943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11741136161748197919849613 4402926060655574219943605)
                ·
                  refine ⟨412774318186460083119713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402926060655574219943605 412774318186460083119713)
                  ·
                    rfl

theorem cell23_7234876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_7234876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234876 prefixEnd_7234876 := by exact prefixLift 7234876
  have htrace : WordTrace (prefixWord ++ tailWord_7234876) baseStart_7234876 baseEnd_7234876 := by
    simpa [prefixWord, tailWord_7234876, baseEnd_7234876] using wordTrace_append hprefix tailTrace_7234876
  have hstable : (prefixWord ++ tailWord_7234876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234876).length < 2 ^ (prefixWord ++ tailWord_7234876).sum := by decide
  have hdescent : baseEnd_7234876 < baseStart_7234876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234893 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7234893 : Nat := 118140960795 + 7234893 * 2 ^ 59
def prefixEnd_7234893 : Nat := 4983230072969 + 3 ^ 40 * 7234893 * 2
def baseEnd_7234893 : Nat := 412775288094363020173871

theorem tailTrace_7234893 : CollatzResearch.WordTrace tailWord_7234893 prefixEnd_7234893 412775288094363020173871 := by
  unfold tailWord_7234893
  simp only [CollatzResearch.WordTrace]
  refine ⟨263878226178225757196669333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175918817452150504797779555 263878226178225757196669333)
  ·
    refine ⟨12369291852104332368593875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263878226178225757196669333 12369291852104332368593875)
    ·
      refine ⟨18553937778156498552890813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12369291852104332368593875 18553937778156498552890813)
      ·
        refine ⟨6957726666808686957334055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18553937778156498552890813 6957726666808686957334055)
        ·
          refine ⟨10436590000213030436001083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957726666808686957334055 10436590000213030436001083)
          ·
            refine ⟨15654885000319545654001625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436590000213030436001083 15654885000319545654001625)
            ·
              refine ⟨11741163750239659240501219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15654885000319545654001625 11741163750239659240501219)
              ·
                refine ⟨17611745625359488860751829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741163750239659240501219 17611745625359488860751829)
                ·
                  refine ⟨412775288094363020173871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17611745625359488860751829 412775288094363020173871)
                  ·
                    rfl

theorem cell23_7234893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7234893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234893 prefixEnd_7234893 := by exact prefixLift 7234893
  have htrace : WordTrace (prefixWord ++ tailWord_7234893) baseStart_7234893 baseEnd_7234893 := by
    simpa [prefixWord, tailWord_7234893, baseEnd_7234893] using wordTrace_append hprefix tailTrace_7234893
  have hstable : (prefixWord ++ tailWord_7234893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234893).length < 2 ^ (prefixWord ++ tailWord_7234893).sum := by decide
  have hdescent : baseEnd_7234893 < baseStart_7234893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234929 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_7234929 : Nat := 118140960795 + 7234929 * 2 ^ 59
def prefixEnd_7234929 : Nat := 4983230072969 + 3 ^ 40 * 7234929 * 2
def baseEnd_7234929 : Nat := 3714996078152829040714673

theorem tailTrace_7234929 : CollatzResearch.WordTrace tailWord_7234929 prefixEnd_7234929 3714996078152829040714673 := by
  unfold tailWord_7234929
  simp only [CollatzResearch.WordTrace]
  refine ⟨263879539206095335344979841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175919692804063556896653227 263879539206095335344979841)
  ·
    refine ⟨197909654404571501508734881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263879539206095335344979841 197909654404571501508734881)
    ·
      refine ⟨148432240803428626131551161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197909654404571501508734881 148432240803428626131551161)
      ·
        refine ⟨111324180602571469598663371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148432240803428626131551161 111324180602571469598663371)
        ·
          refine ⟨166986270903857204397995057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111324180602571469598663371 166986270903857204397995057)
          ·
            refine ⟨125239703177892903298496293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166986270903857204397995057 125239703177892903298496293)
            ·
              refine ⟨23482444345854919368468055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125239703177892903298496293 23482444345854919368468055)
              ·
                refine ⟨35223666518782379052702083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482444345854919368468055 35223666518782379052702083)
                ·
                  refine ⟨52835499778173568579053125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35223666518782379052702083 52835499778173568579053125)
                  ·
                    refine ⟨9906656208407544108572461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52835499778173568579053125 9906656208407544108572461)
                    ·
                      refine ⟨3714996078152829040714673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906656208407544108572461 3714996078152829040714673)
                      ·
                        rfl

theorem cell23_7234929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_7234929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234929 prefixEnd_7234929 := by exact prefixLift 7234929
  have htrace : WordTrace (prefixWord ++ tailWord_7234929) baseStart_7234929 baseEnd_7234929 := by
    simpa [prefixWord, tailWord_7234929, baseEnd_7234929] using wordTrace_append hprefix tailTrace_7234929
  have hstable : (prefixWord ++ tailWord_7234929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234929).length < 2 ^ (prefixWord ++ tailWord_7234929).sum := by decide
  have hdescent : baseEnd_7234929 < baseStart_7234929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234953 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_7234953 : Nat := 118140960795 + 7234953 * 2 ^ 59
def prefixEnd_7234953 : Nat := 4983230072969 + 3 ^ 40 * 7234953 * 2
def baseEnd_7234953 : Nat := 1238336133896178982271521

theorem tailTrace_7234953 : CollatzResearch.WordTrace tailWord_7234953 prefixEnd_7234953 1238336133896178982271521 := by
  unfold tailWord_7234953
  simp only [CollatzResearch.WordTrace]
  refine ⟨263880414558008387443853513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175920276372005591629235675 263880414558008387443853513)
  ·
    refine ⟨197910310918506290582890135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263880414558008387443853513 197910310918506290582890135)
    ·
      refine ⟨296865466377759435874335203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197910310918506290582890135 296865466377759435874335203)
      ·
        refine ⟨445298199566639153811502805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296865466377759435874335203 445298199566639153811502805)
        ·
          refine ⟨10436676552343105167457097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 445298199566639153811502805 10436676552343105167457097)
          ·
            refine ⟨7827507414257328875592823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10436676552343105167457097 7827507414257328875592823)
            ·
              refine ⟨11741261121385993313389235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827507414257328875592823 11741261121385993313389235)
              ·
                refine ⟨17611891682078989970083853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741261121385993313389235 17611891682078989970083853)
                ·
                  refine ⟨6604459380779621238781445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17611891682078989970083853 6604459380779621238781445)
                  ·
                    refine ⟨1238336133896178982271521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604459380779621238781445 1238336133896178982271521)
                    ·
                      rfl

theorem cell23_7234953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_7234953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234953 prefixEnd_7234953 := by exact prefixLift 7234953
  have htrace : WordTrace (prefixWord ++ tailWord_7234953) baseStart_7234953 baseEnd_7234953 := by
    simpa [prefixWord, tailWord_7234953, baseEnd_7234953] using wordTrace_append hprefix tailTrace_7234953
  have hstable : (prefixWord ++ tailWord_7234953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234953).length < 2 ^ (prefixWord ++ tailWord_7234953).sum := by decide
  have hdescent : baseEnd_7234953 < baseStart_7234953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234976 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_7234976 : Nat := 118140960795 + 7234976 * 2 ^ 59
def prefixEnd_7234976 : Nat := 4983230072969 + 3 ^ 40 * 7234976 * 2
def baseEnd_7234976 : Nat := 3715020211743590356826957

theorem tailTrace_7234976 : CollatzResearch.WordTrace tailWord_7234976 prefixEnd_7234976 3715020211743590356826957 := by
  unfold tailWord_7234976
  simp only [CollatzResearch.WordTrace]
  refine ⟨131940626718462531185970391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175920835624616708247960521 131940626718462531185970391)
  ·
    refine ⟨197910940077693796778955587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131940626718462531185970391 197910940077693796778955587)
    ·
      refine ⟨296866410116540695168433381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197910940077693796778955587 296866410116540695168433381)
      ·
        refine ⟨55662451896851380344081259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296866410116540695168433381 55662451896851380344081259)
        ·
          refine ⟨83493677845277070516121889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55662451896851380344081259 83493677845277070516121889)
          ·
            refine ⟨62620258383957802887091417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83493677845277070516121889 62620258383957802887091417)
            ·
              refine ⟨46965193787968352165318563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62620258383957802887091417 46965193787968352165318563)
              ·
                refine ⟨70447790681952528247977845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46965193787968352165318563 70447790681952528247977845)
                ·
                  refine ⟨6604480376433049523247923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70447790681952528247977845 6604480376433049523247923)
                  ·
                    refine ⟨9906720564649574284871885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604480376433049523247923 9906720564649574284871885)
                    ·
                      refine ⟨3715020211743590356826957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906720564649574284871885 3715020211743590356826957)
                      ·
                        rfl

theorem cell23_7234976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_7234976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234976 prefixEnd_7234976 := by exact prefixLift 7234976
  have htrace : WordTrace (prefixWord ++ tailWord_7234976) baseStart_7234976 baseEnd_7234976 := by
    simpa [prefixWord, tailWord_7234976, baseEnd_7234976] using wordTrace_append hprefix tailTrace_7234976
  have hstable : (prefixWord ++ tailWord_7234976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234976).length < 2 ^ (prefixWord ++ tailWord_7234976).sum := by decide
  have hdescent : baseEnd_7234976 < baseStart_7234976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7234979 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 3, 5]
def baseStart_7234979 : Nat := 118140960795 + 7234979 * 2 ^ 59
def prefixEnd_7234979 : Nat := 4983230072969 + 3 ^ 40 * 7234979 * 2
def baseEnd_7234979 : Nat := 1238340584061851281696481

theorem tailTrace_7234979 : CollatzResearch.WordTrace tailWord_7234979 prefixEnd_7234979 1238340584061851281696481 := by
  unfold tailWord_7234979
  simp only [CollatzResearch.WordTrace]
  refine ⟨263881362855914193884299991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175920908570609462589533327 263881362855914193884299991)
  ·
    refine ⟨395822044283871290826449987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263881362855914193884299991 395822044283871290826449987)
    ·
      refine ⟨593733066425806936239674981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395822044283871290826449987 593733066425806936239674981)
      ·
        refine ⟨111324949954838800544939059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593733066425806936239674981 111324949954838800544939059)
        ·
          refine ⟨166987424932258200817408589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111324949954838800544939059 166987424932258200817408589)
          ·
            refine ⟨62620284349596825306528221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166987424932258200817408589 62620284349596825306528221)
            ·
              refine ⟨23482606631098809489948083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62620284349596825306528221 23482606631098809489948083)
              ·
                refine ⟨35223909946648214234922125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482606631098809489948083 35223909946648214234922125)
                ·
                  refine ⟨13208966229993080338095797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35223909946648214234922125 13208966229993080338095797)
                  ·
                    refine ⟨1238340584061851281696481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13208966229993080338095797 1238340584061851281696481)
                    ·
                      rfl

theorem cell23_7234979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].length) (baseStart_7234979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7234979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7234979 prefixEnd_7234979 := by exact prefixLift 7234979
  have htrace : WordTrace (prefixWord ++ tailWord_7234979) baseStart_7234979 baseEnd_7234979 := by
    simpa [prefixWord, tailWord_7234979, baseEnd_7234979] using wordTrace_append hprefix tailTrace_7234979
  have hstable : (prefixWord ++ tailWord_7234979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7234979).length < 2 ^ (prefixWord ++ tailWord_7234979).sum := by decide
  have hdescent : baseEnd_7234979 < baseStart_7234979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7234979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235004 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_7235004 : Nat := 118140960795 + 7235004 * 2 ^ 59
def prefixEnd_7235004 : Nat := 4983230072969 + 3 ^ 40 * 7235004 * 2
def baseEnd_7235004 : Nat := 1238344863067305415758943

theorem tailTrace_7235004 : CollatzResearch.WordTrace tailWord_7235004 prefixEnd_7235004 1238344863067305415758943 := by
  unfold tailWord_7235004
  simp only [CollatzResearch.WordTrace]
  refine ⟨131941137340411811576980033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175921516453882415435973377 131941137340411811576980033)
  ·
    refine ⟨98955853005308858682735025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131941137340411811576980033 98955853005308858682735025)
    ·
      refine ⟨74216889753981644012051269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98955853005308858682735025 74216889753981644012051269)
      ·
        refine ⟨13915666828871558252259613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74216889753981644012051269 13915666828871558252259613)
        ·
          refine ⟨5218375060826834344597355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13915666828871558252259613 5218375060826834344597355)
          ·
            refine ⟨7827562591240251516896033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218375060826834344597355 7827562591240251516896033)
            ·
              refine ⟨5870671943430188637672025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7827562591240251516896033 5870671943430188637672025)
              ·
                refine ⟨4403003957572641478254019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5870671943430188637672025 4403003957572641478254019)
                ·
                  refine ⟨6604505936358962217381029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403003957572641478254019 6604505936358962217381029)
                  ·
                    refine ⟨1238344863067305415758943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604505936358962217381029 1238344863067305415758943)
                    ·
                      rfl

theorem cell23_7235004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_7235004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235004 prefixEnd_7235004 := by exact prefixLift 7235004
  have htrace : WordTrace (prefixWord ++ tailWord_7235004) baseStart_7235004 baseEnd_7235004 := by
    simpa [prefixWord, tailWord_7235004, baseEnd_7235004] using wordTrace_append hprefix tailTrace_7235004
  have hstable : (prefixWord ++ tailWord_7235004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235004).length < 2 ^ (prefixWord ++ tailWord_7235004).sum := by decide
  have hdescent : baseEnd_7235004 < baseStart_7235004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235019 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_7235019 : Nat := 118140960795 + 7235019 * 2 ^ 59
def prefixEnd_7235019 : Nat := 4983230072969 + 3 ^ 40 * 7235019 * 2
def baseEnd_7235019 : Nat := 3715042291411733688589259

theorem tailTrace_7235019 : CollatzResearch.WordTrace tailWord_7235019 prefixEnd_7235019 3715042291411733688589259 := by
  unfold tailWord_7235019
  simp only [CollatzResearch.WordTrace]
  refine ⟨263882821775769280715756111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175921881183846187143837407 263882821775769280715756111)
  ·
    refine ⟨395824232663653921073634167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263882821775769280715756111 395824232663653921073634167)
    ·
      refine ⟨593736348995480881610451251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395824232663653921073634167 593736348995480881610451251)
      ·
        refine ⟨890604523493221322415676877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593736348995480881610451251 890604523493221322415676877)
        ·
          refine ⟨333976696309957995905878829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890604523493221322415676877 333976696309957995905878829)
          ·
            refine ⟨125241261116234248464704561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333976696309957995905878829 125241261116234248464704561)
            ·
              refine ⟨93930945837175686348528421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125241261116234248464704561 93930945837175686348528421)
              ·
                refine ⟨17612052344470441190349079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93930945837175686348528421 17612052344470441190349079)
                ·
                  refine ⟨26418078516705661785523619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17612052344470441190349079 26418078516705661785523619)
                  ·
                    refine ⟨39627117775058492678285429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26418078516705661785523619 39627117775058492678285429)
                    ·
                      refine ⟨3715042291411733688589259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39627117775058492678285429 3715042291411733688589259)
                      ·
                        rfl

theorem cell23_7235019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_7235019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235019 prefixEnd_7235019 := by exact prefixLift 7235019
  have htrace : WordTrace (prefixWord ++ tailWord_7235019) baseStart_7235019 baseEnd_7235019 := by
    simpa [prefixWord, tailWord_7235019, baseEnd_7235019] using wordTrace_append hprefix tailTrace_7235019
  have hstable : (prefixWord ++ tailWord_7235019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235019).length < 2 ^ (prefixWord ++ tailWord_7235019).sum := by decide
  have hdescent : baseEnd_7235019 < baseStart_7235019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235033 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 5, 2, 2]
def baseStart_7235033 : Nat := 118140960795 + 7235033 * 2 ^ 59
def prefixEnd_7235033 : Nat := 4983230072969 + 3 ^ 40 * 7235033 * 2
def baseEnd_7235033 : Nat := 3715049480140896633814195

theorem tailTrace_7235033 : CollatzResearch.WordTrace tailWord_7235033 prefixEnd_7235033 3715049480140896633814195 := by
  unfold tailWord_7235033
  simp only [CollatzResearch.WordTrace]
  refine ⟨263883332397718561106765753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175922221598479040737843835 263883332397718561106765753)
  ·
    refine ⟨197912499298288920830074315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263883332397718561106765753 197912499298288920830074315)
    ·
      refine ⟨296868748947433381245111473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197912499298288920830074315 296868748947433381245111473)
      ·
        refine ⟨222651561710575035933833605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296868748947433381245111473 222651561710575035933833605)
        ·
          refine ⟨41747167820732819237593801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222651561710575035933833605 41747167820732819237593801)
          ·
            refine ⟨31310375865549614428195351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41747167820732819237593801 31310375865549614428195351)
            ·
              refine ⟨46965563798324421642293027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31310375865549614428195351 46965563798324421642293027)
              ·
                refine ⟨70448345697486632463439541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46965563798324421642293027 70448345697486632463439541)
                ·
                  refine ⟨6604532409139371793447457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70448345697486632463439541 6604532409139371793447457)
                  ·
                    refine ⟨4953399306854528845085593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6604532409139371793447457 4953399306854528845085593)
                    ·
                      refine ⟨3715049480140896633814195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953399306854528845085593 3715049480140896633814195)
                      ·
                        rfl

theorem cell23_7235033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_7235033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235033 prefixEnd_7235033 := by exact prefixLift 7235033
  have htrace : WordTrace (prefixWord ++ tailWord_7235033) baseStart_7235033 baseEnd_7235033 := by
    simpa [prefixWord, tailWord_7235033, baseEnd_7235033] using wordTrace_append hprefix tailTrace_7235033
  have hstable : (prefixWord ++ tailWord_7235033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235033).length < 2 ^ (prefixWord ++ tailWord_7235033).sum := by decide
  have hdescent : baseEnd_7235033 < baseStart_7235033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235049 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_7235049 : Nat := 118140960795 + 7235049 * 2 ^ 59
def prefixEnd_7235049 : Nat := 4983230072969 + 3 ^ 40 * 7235049 * 2
def baseEnd_7235049 : Nat := 3715057695831368571214121

theorem tailTrace_7235049 : CollatzResearch.WordTrace tailWord_7235049 prefixEnd_7235049 3715057695831368571214121 := by
  unfold tailWord_7235049
  simp only [CollatzResearch.WordTrace]
  refine ⟨263883915965660595839348201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175922610643773730559565467 263883915965660595839348201)
  ·
    refine ⟨197912936974245446879511151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263883915965660595839348201 197912936974245446879511151)
    ·
      refine ⟨296869405461368170319266727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197912936974245446879511151 296869405461368170319266727)
      ·
        refine ⟨445304108192052255478900091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296869405461368170319266727 445304108192052255478900091)
        ·
          refine ⟨667956162288078383218350137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445304108192052255478900091 667956162288078383218350137)
          ·
            refine ⟨500967121716058787413762603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667956162288078383218350137 500967121716058787413762603)
            ·
              refine ⟨751450682574088181120643905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500967121716058787413762603 751450682574088181120643905)
              ·
                refine ⟨563588011930566135840482929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751450682574088181120643905 563588011930566135840482929)
                ·
                  refine ⟨422691008947924601880362197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563588011930566135840482929 422691008947924601880362197)
                  ·
                    refine ⟨9906820522216982856570989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 422691008947924601880362197 9906820522216982856570989)
                    ·
                      refine ⟨3715057695831368571214121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9906820522216982856570989 3715057695831368571214121)
                      ·
                        rfl

theorem cell23_7235049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_7235049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235049 prefixEnd_7235049 := by exact prefixLift 7235049
  have htrace : WordTrace (prefixWord ++ tailWord_7235049) baseStart_7235049 baseEnd_7235049 := by
    simpa [prefixWord, tailWord_7235049, baseEnd_7235049] using wordTrace_append hprefix tailTrace_7235049
  have hstable : (prefixWord ++ tailWord_7235049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235049).length < 2 ^ (prefixWord ++ tailWord_7235049).sum := by decide
  have hdescent : baseEnd_7235049 < baseStart_7235049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235070 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7235070 : Nat := 118140960795 + 7235070 * 2 ^ 59
def prefixEnd_7235070 : Nat := 4983230072969 + 3 ^ 40 * 7235070 * 2
def baseEnd_7235070 : Nat := 3715068478925112989051525

theorem tailTrace_7235070 : CollatzResearch.WordTrace tailWord_7235070 prefixEnd_7235070 3715068478925112989051525 := by
  unfold tailWord_7235070
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985585237323064553232833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175923121265723010950575109 32985585237323064553232833)
  ·
    refine ⟨24739188927992298414924625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32985585237323064553232833 24739188927992298414924625)
    ·
      refine ⟨18554391695994223811193469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24739188927992298414924625 18554391695994223811193469)
      ·
        refine ⟨6957896885997833929197551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18554391695994223811193469 6957896885997833929197551)
        ·
          refine ⟨10436845328996750893796327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957896885997833929197551 10436845328996750893796327)
          ·
            refine ⟨15655267993495126340694491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436845328996750893796327 15655267993495126340694491)
            ·
              refine ⟨23482901990242689511041737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655267993495126340694491 23482901990242689511041737)
              ·
                refine ⟨17612176492682017133281303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23482901990242689511041737 17612176492682017133281303)
                ·
                  refine ⟨26418264739023025699921955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17612176492682017133281303 26418264739023025699921955)
                  ·
                    refine ⟨39627397108534538549882933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26418264739023025699921955 39627397108534538549882933)
                    ·
                      refine ⟨3715068478925112989051525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39627397108534538549882933 3715068478925112989051525)
                      ·
                        rfl

theorem cell23_7235070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7235070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235070 prefixEnd_7235070 := by exact prefixLift 7235070
  have htrace : WordTrace (prefixWord ++ tailWord_7235070) baseStart_7235070 baseEnd_7235070 := by
    simpa [prefixWord, tailWord_7235070, baseEnd_7235070] using wordTrace_append hprefix tailTrace_7235070
  have hstable : (prefixWord ++ tailWord_7235070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235070).length < 2 ^ (prefixWord ++ tailWord_7235070).sum := by decide
  have hdescent : baseEnd_7235070 < baseStart_7235070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235190 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7235190 : Nat := 118140960795 + 7235190 * 2 ^ 59
def prefixEnd_7235190 : Nat := 4983230072969 + 3 ^ 40 * 7235190 * 2
def baseEnd_7235190 : Nat := 3715130096603652519550973

theorem tailTrace_7235190 : CollatzResearch.WordTrace tailWord_7235190 prefixEnd_7235190 3715130096603652519550973 := by
  unfold tailWord_7235190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493066166134361057514439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175926039105433184613487349 16493066166134361057514439)
  ·
    refine ⟨24739599249201541586271659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16493066166134361057514439 24739599249201541586271659)
    ·
      refine ⟨37109398873802312379407489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24739599249201541586271659 37109398873802312379407489)
      ·
        refine ⟨27832049155351734284555617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37109398873802312379407489 27832049155351734284555617)
        ·
          refine ⟨20874036866513800713416713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27832049155351734284555617 20874036866513800713416713)
          ·
            refine ⟨15655527649885350535062535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20874036866513800713416713 15655527649885350535062535)
            ·
              refine ⟨23483291474828025802593803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655527649885350535062535 23483291474828025802593803)
              ·
                refine ⟨35224937212242038703890705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23483291474828025802593803 35224937212242038703890705)
                ·
                  refine ⟨26418702909181529027918029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35224937212242038703890705 26418702909181529027918029)
                  ·
                    refine ⟨9907013590943073385469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26418702909181529027918029 9907013590943073385469261)
                    ·
                      refine ⟨3715130096603652519550973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907013590943073385469261 3715130096603652519550973)
                      ·
                        rfl

theorem cell23_7235190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7235190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235190 prefixEnd_7235190 := by exact prefixLift 7235190
  have htrace : WordTrace (prefixWord ++ tailWord_7235190) baseStart_7235190 baseEnd_7235190 := by
    simpa [prefixWord, tailWord_7235190, baseEnd_7235190] using wordTrace_append hprefix tailTrace_7235190
  have hstable : (prefixWord ++ tailWord_7235190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235190).length < 2 ^ (prefixWord ++ tailWord_7235190).sum := by decide
  have hdescent : baseEnd_7235190 < baseStart_7235190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235196 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7235196 : Nat := 118140960795 + 7235196 * 2 ^ 59
def prefixEnd_7235196 : Nat := 4983230072969 + 3 ^ 40 * 7235196 * 2
def baseEnd_7235196 : Nat := 3715133177487579496075945

theorem tailTrace_7235196 : CollatzResearch.WordTrace tailWord_7235196 prefixEnd_7235196 3715133177487579496075945 := by
  unfold tailWord_7235196
  simp only [CollatzResearch.WordTrace]
  refine ⟨131944638748064019972474721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175926184997418693296632961 131944638748064019972474721)
  ·
    refine ⟨98958479061048014979356041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131944638748064019972474721 98958479061048014979356041)
    ·
      refine ⟨74218859295786011234517031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98958479061048014979356041 74218859295786011234517031)
      ·
        refine ⟨111328288943679016851775547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74218859295786011234517031 111328288943679016851775547)
        ·
          refine ⟨166992433415518525277663321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111328288943679016851775547 166992433415518525277663321)
          ·
            refine ⟨125244325061638893958247491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166992433415518525277663321 125244325061638893958247491)
            ·
              refine ⟨187866487592458340937371237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125244325061638893958247491 187866487592458340937371237)
              ·
                refine ⟨35224966423585938925757107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187866487592458340937371237 35224966423585938925757107)
                ·
                  refine ⟨52837449635378908388635661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35224966423585938925757107 52837449635378908388635661)
                  ·
                    refine ⟨19814043613267090645738373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52837449635378908388635661 19814043613267090645738373)
                    ·
                      refine ⟨3715133177487579496075945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19814043613267090645738373 3715133177487579496075945)
                      ·
                        rfl

theorem cell23_7235196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7235196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235196 prefixEnd_7235196 := by exact prefixLift 7235196
  have htrace : WordTrace (prefixWord ++ tailWord_7235196) baseStart_7235196 baseEnd_7235196 := by
    simpa [prefixWord, tailWord_7235196, baseEnd_7235196] using wordTrace_append hprefix tailTrace_7235196
  have hstable : (prefixWord ++ tailWord_7235196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235196).length < 2 ^ (prefixWord ++ tailWord_7235196).sum := by decide
  have hdescent : baseEnd_7235196 < baseStart_7235196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235210 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_7235210 : Nat := 118140960795 + 7235210 * 2 ^ 59
def prefixEnd_7235210 : Nat := 4983230072969 + 3 ^ 40 * 7235210 * 2
def baseEnd_7235210 : Nat := 1238380122072247480433627

theorem tailTrace_7235210 : CollatzResearch.WordTrace tailWord_7235210 prefixEnd_7235210 1238380122072247480433627 := by
  unfold tailWord_7235210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65972447029519330083989771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175926525412051546890639389 65972447029519330083989771)
  ·
    refine ⟨98958670544278995125984657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65972447029519330083989771 98958670544278995125984657)
    ·
      refine ⟨74219002908209246344488493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98958670544278995125984657 74219002908209246344488493)
      ·
        refine ⟨27832126090578467379183185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74219002908209246344488493 27832126090578467379183185)
        ·
          refine ⟨20874094567933850534387389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27832126090578467379183185 20874094567933850534387389)
          ·
            refine ⟨7827785462975193950395271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20874094567933850534387389 7827785462975193950395271)
            ·
              refine ⟨11741678194462790925592907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827785462975193950395271 11741678194462790925592907)
              ·
                refine ⟨17612517291694186388389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741678194462790925592907 17612517291694186388389361)
                ·
                  refine ⟨13209387968770639791292021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17612517291694186388389361 13209387968770639791292021)
                  ·
                    refine ⟨1238380122072247480433627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13209387968770639791292021 1238380122072247480433627)
                    ·
                      rfl

theorem cell23_7235210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_7235210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235210 prefixEnd_7235210 := by exact prefixLift 7235210
  have htrace : WordTrace (prefixWord ++ tailWord_7235210) baseStart_7235210 baseEnd_7235210 := by
    simpa [prefixWord, tailWord_7235210, baseEnd_7235210] using wordTrace_append hprefix tailTrace_7235210
  have hstable : (prefixWord ++ tailWord_7235210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235210).length < 2 ^ (prefixWord ++ tailWord_7235210).sum := by decide
  have hdescent : baseEnd_7235210 < baseStart_7235210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235274 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_7235274 : Nat := 118140960795 + 7235274 * 2 ^ 59
def prefixEnd_7235274 : Nat := 4983230072969 + 3 ^ 40 * 7235274 * 2
def baseEnd_7235274 : Nat := 1238391076326210063633529

theorem tailTrace_7235274 : CollatzResearch.WordTrace tailWord_7235274 prefixEnd_7235274 1238391076326210063633529 := by
  unfold tailWord_7235274
  simp only [CollatzResearch.WordTrace]
  refine ⟨65973030597461364816572219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175928081593230306177525917 65973030597461364816572219)
  ·
    refine ⟨98959545896192047224858329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65973030597461364816572219 98959545896192047224858329)
    ·
      refine ⟨74219659422144035418643747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98959545896192047224858329 74219659422144035418643747)
      ·
        refine ⟨111329489133216053127965621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74219659422144035418643747 111329489133216053127965621)
        ·
          refine ⟨10437139606239004980746777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111329489133216053127965621 10437139606239004980746777)
          ·
            refine ⟨7827854704679253735560083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437139606239004980746777 7827854704679253735560083)
            ·
              refine ⟨11741782057018880603340125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827854704679253735560083 11741782057018880603340125)
              ·
                refine ⟨4403168271382080226252547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11741782057018880603340125 4403168271382080226252547)
                ·
                  refine ⟨6604752407073120339378821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403168271382080226252547 6604752407073120339378821)
                  ·
                    refine ⟨1238391076326210063633529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6604752407073120339378821 1238391076326210063633529)
                    ·
                      rfl

theorem cell23_7235274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_7235274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235274 prefixEnd_7235274 := by exact prefixLift 7235274
  have htrace : WordTrace (prefixWord ++ tailWord_7235274) baseStart_7235274 baseEnd_7235274 := by
    simpa [prefixWord, tailWord_7235274, baseEnd_7235274] using wordTrace_append hprefix tailTrace_7235274
  have hstable : (prefixWord ++ tailWord_7235274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235274).length < 2 ^ (prefixWord ++ tailWord_7235274).sum := by decide
  have hdescent : baseEnd_7235274 < baseStart_7235274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235290 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_7235290 : Nat := 118140960795 + 7235290 * 2 ^ 59
def prefixEnd_7235290 : Nat := 4983230072969 + 3 ^ 40 * 7235290 * 2
def baseEnd_7235290 : Nat := 3715181444669102128300513

theorem tailTrace_7235290 : CollatzResearch.WordTrace tailWord_7235290 prefixEnd_7235290 3715181444669102128300513 := by
  unfold tailWord_7235290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65973176489446873499717831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175928470638524995999247549 65973176489446873499717831)
  ·
    refine ⟨98959764734170310249576747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65973176489446873499717831 98959764734170310249576747)
    ·
      refine ⟨148439647101255465374365121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98959764734170310249576747 148439647101255465374365121)
      ·
        refine ⟨111329735325941599030773841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148439647101255465374365121 111329735325941599030773841)
        ·
          refine ⟨83497301494456199273080381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111329735325941599030773841 83497301494456199273080381)
          ·
            refine ⟨31311488060421074727405143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83497301494456199273080381 31311488060421074727405143)
            ·
              refine ⟨46967232090631612091107715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31311488060421074727405143 46967232090631612091107715)
              ·
                refine ⟨70450848135947418136661573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46967232090631612091107715 70450848135947418136661573)
                ·
                  refine ⟨13209534025490140900624045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70450848135947418136661573 13209534025490140900624045)
                  ·
                    refine ⟨4953575259558802837734017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13209534025490140900624045 4953575259558802837734017)
                    ·
                      refine ⟨3715181444669102128300513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953575259558802837734017 3715181444669102128300513)
                      ·
                        rfl

theorem cell23_7235290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_7235290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235290 prefixEnd_7235290 := by exact prefixLift 7235290
  have htrace : WordTrace (prefixWord ++ tailWord_7235290) baseStart_7235290 baseEnd_7235290 := by
    simpa [prefixWord, tailWord_7235290, baseEnd_7235290] using wordTrace_append hprefix tailTrace_7235290
  have hstable : (prefixWord ++ tailWord_7235290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235290).length < 2 ^ (prefixWord ++ tailWord_7235290).sum := by decide
  have hdescent : baseEnd_7235290 < baseStart_7235290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235330 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7235330 : Nat := 118140960795 + 7235330 * 2 ^ 59
def prefixEnd_7235330 : Nat := 4983230072969 + 3 ^ 40 * 7235330 * 2
def baseEnd_7235330 : Nat := 1238400661298427323933443

theorem tailTrace_7235330 : CollatzResearch.WordTrace tailWord_7235330 prefixEnd_7235330 1238400661298427323933443 := by
  unfold tailWord_7235330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65973541219410645207581861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175929443251761720553551629 65973541219410645207581861)
  ·
    refine ⟨12370038978639495976421599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65973541219410645207581861 12370038978639495976421599)
    ·
      refine ⟨18555058467959243964632399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12370038978639495976421599 18555058467959243964632399)
      ·
        refine ⟨27832587701938865946948599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18555058467959243964632399 27832587701938865946948599)
        ·
          refine ⟨41748881552908298920422899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27832587701938865946948599 41748881552908298920422899)
          ·
            refine ⟨62623322329362448380634349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41748881552908298920422899 62623322329362448380634349)
            ·
              refine ⟨23483745873510918142737881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62623322329362448380634349 23483745873510918142737881)
              ·
                refine ⟨17612809405133188607053411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23483745873510918142737881 17612809405133188607053411)
                ·
                  refine ⟨26419214107699782910580117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17612809405133188607053411 26419214107699782910580117)
                  ·
                    refine ⟨1238400661298427323933443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26419214107699782910580117 1238400661298427323933443)
                    ·
                      rfl

theorem cell23_7235330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7235330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235330 prefixEnd_7235330 := by exact prefixLift 7235330
  have htrace : WordTrace (prefixWord ++ tailWord_7235330) baseStart_7235330 baseEnd_7235330 := by
    simpa [prefixWord, tailWord_7235330, baseEnd_7235330] using wordTrace_append hprefix tailTrace_7235330
  have hstable : (prefixWord ++ tailWord_7235330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235330).length < 2 ^ (prefixWord ++ tailWord_7235330).sum := by decide
  have hdescent : baseEnd_7235330 < baseStart_7235330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235340 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_7235340 : Nat := 118140960795 + 7235340 * 2 ^ 59
def prefixEnd_7235340 : Nat := 4983230072969 + 3 ^ 40 * 7235340 * 2
def baseEnd_7235340 : Nat := 3715207118701826932675283

theorem tailTrace_7235340 : CollatzResearch.WordTrace tailWord_7235340 prefixEnd_7235340 3715207118701826932675283 := by
  unfold tailWord_7235340
  simp only [CollatzResearch.WordTrace]
  refine ⟨131947264803803176269095737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175929686405070901692127649 131947264803803176269095737)
  ·
    refine ⟨98960448602852382201821803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131947264803803176269095737 98960448602852382201821803)
    ·
      refine ⟨148440672904278573302732705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98960448602852382201821803 148440672904278573302732705)
      ·
        refine ⟨111330504678208929977049529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148440672904278573302732705 111330504678208929977049529)
        ·
          refine ⟨83497878508656697482787147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111330504678208929977049529 83497878508656697482787147)
          ·
            refine ⟨125246817762985046224180721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83497878508656697482787147 125246817762985046224180721)
            ·
              refine ⟨93935113322238784668135541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125246817762985046224180721 93935113322238784668135541)
              ·
                refine ⟨8806416873959886062637707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93935113322238784668135541 8806416873959886062637707)
                ·
                  refine ⟨13209625310939829093956561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806416873959886062637707 13209625310939829093956561)
                  ·
                    refine ⟨9907218983204871820467421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13209625310939829093956561 9907218983204871820467421)
                    ·
                      refine ⟨3715207118701826932675283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907218983204871820467421 3715207118701826932675283)
                      ·
                        rfl

theorem cell23_7235340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_7235340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235340 prefixEnd_7235340 := by exact prefixLift 7235340
  have htrace : WordTrace (prefixWord ++ tailWord_7235340) baseStart_7235340 baseEnd_7235340 := by
    simpa [prefixWord, tailWord_7235340, baseEnd_7235340] using wordTrace_append hprefix tailTrace_7235340
  have hstable : (prefixWord ++ tailWord_7235340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235340).length < 2 ^ (prefixWord ++ tailWord_7235340).sum := by decide
  have hdescent : baseEnd_7235340 < baseStart_7235340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235391 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 1, 2, 3]
def baseStart_7235391 : Nat := 118140960795 + 7235391 * 2 ^ 59
def prefixEnd_7235391 : Nat := 4983230072969 + 3 ^ 40 * 7235391 * 2
def baseEnd_7235391 : Nat := 3715233306215206233137549

theorem tailTrace_7235391 : CollatzResearch.WordTrace tailWord_7235391 prefixEnd_7235391 3715233306215206233137549 := by
  unfold tailWord_7235391
  simp only [CollatzResearch.WordTrace]
  refine ⟨263896389730421588248298027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175930926486947725498865351 263896389730421588248298027)
  ·
    refine ⟨395844584595632382372447041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263896389730421588248298027 395844584595632382372447041)
    ·
      refine ⟨296883438446724286779335281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395844584595632382372447041 296883438446724286779335281)
      ·
        refine ⟨222662578835043215084501461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296883438446724286779335281 222662578835043215084501461)
        ·
          refine ⟨5218654191446325353543003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 222662578835043215084501461 5218654191446325353543003)
          ·
            refine ⟨7827981287169488030314505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218654191446325353543003 7827981287169488030314505)
            ·
              refine ⟨5870985965377116022735879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7827981287169488030314505 5870985965377116022735879)
              ·
                refine ⟨8806478948065674034103819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870985965377116022735879 8806478948065674034103819)
                ·
                  refine ⟨13209718422098511051155729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806478948065674034103819 13209718422098511051155729)
                  ·
                    refine ⟨9907288816573883288366797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13209718422098511051155729 9907288816573883288366797)
                    ·
                      refine ⟨3715233306215206233137549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907288816573883288366797 3715233306215206233137549)
                      ·
                        rfl

theorem cell23_7235391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_7235391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235391 prefixEnd_7235391 := by exact prefixLift 7235391
  have htrace : WordTrace (prefixWord ++ tailWord_7235391) baseStart_7235391 baseEnd_7235391 := by
    simpa [prefixWord, tailWord_7235391, baseEnd_7235391] using wordTrace_append hprefix tailTrace_7235391
  have hstable : (prefixWord ++ tailWord_7235391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235391).length < 2 ^ (prefixWord ++ tailWord_7235391).sum := by decide
  have hdescent : baseEnd_7235391 < baseStart_7235391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
