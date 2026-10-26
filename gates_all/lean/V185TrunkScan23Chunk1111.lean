import V185TrunkScan23Chunk1110

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6579586 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6579586 : Nat := 118140960795 + 6579586 * 2 ^ 59
def prefixEnd_6579586 : Nat := 4983230072969 + 3 ^ 40 * 6579586 * 2
def baseEnd_6579586 : Nat := 3378490125593399573216041

theorem tailTrace_6579586 : CollatzResearch.WordTrace tailWord_6579586 prefixEnd_6579586 3378490125593399573216041 := by
  unfold tailWord_6579586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59994304085322775167819653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159984810894194067114185741 59994304085322775167819653)
  ·
    refine ⟨11248932015998020343966185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59994304085322775167819653 11248932015998020343966185)
    ·
      refine ⟨8436699011998515257974639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11248932015998020343966185 8436699011998515257974639)
      ·
        refine ⟨12655048517997772886961959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436699011998515257974639 12655048517997772886961959)
        ·
          refine ⟨18982572776996659330442939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12655048517997772886961959 18982572776996659330442939)
          ·
            refine ⟨28473859165494988995664409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18982572776996659330442939 28473859165494988995664409)
            ·
              refine ⟨21355394374121241746748307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28473859165494988995664409 21355394374121241746748307)
              ·
                refine ⟨32033091561181862620122461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355394374121241746748307 32033091561181862620122461)
                ·
                  refine ⟨12012409335443198482545923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32033091561181862620122461 12012409335443198482545923)
                  ·
                    refine ⟨18018614003164797723818885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12012409335443198482545923 18018614003164797723818885)
                    ·
                      refine ⟨3378490125593399573216041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18018614003164797723818885 3378490125593399573216041)
                      ·
                        rfl

theorem cell23_6579586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6579586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579586 prefixEnd_6579586 := by exact prefixLift 6579586
  have htrace : WordTrace (prefixWord ++ tailWord_6579586) baseStart_6579586 baseEnd_6579586 := by
    simpa [prefixWord, tailWord_6579586, baseEnd_6579586] using wordTrace_append hprefix tailTrace_6579586
  have hstable : (prefixWord ++ tailWord_6579586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579586).length < 2 ^ (prefixWord ++ tailWord_6579586).sum := by decide
  have hdescent : baseEnd_6579586 < baseStart_6579586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579619 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 3]
def baseStart_6579619 : Nat := 118140960795 + 6579619 * 2 ^ 59
def prefixEnd_6579619 : Nat := 4983230072969 + 3 ^ 40 * 6579619 * 2
def baseEnd_6579619 : Nat := 3378507070454997944103389

theorem tailTrace_6579619 : CollatzResearch.WordTrace tailWord_6579619 prefixEnd_6579619 3378507070454997944103389 := by
  unfold tailWord_6579619
  simp only [CollatzResearch.WordTrace]
  refine ⟨239978419950171547307229911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159985613300114364871486607 239978419950171547307229911)
  ·
    refine ⟨359967629925257320960844867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239978419950171547307229911 359967629925257320960844867)
    ·
      refine ⟨539951444887885981441267301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359967629925257320960844867 539951444887885981441267301)
      ·
        refine ⟨101240895916478621520237619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 539951444887885981441267301 101240895916478621520237619)
        ·
          refine ⟨151861343874717932280356429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101240895916478621520237619 151861343874717932280356429)
          ·
            refine ⟨56948003953019224605133661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151861343874717932280356429 56948003953019224605133661)
            ·
              refine ⟨21355501482382209226925123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56948003953019224605133661 21355501482382209226925123)
              ·
                refine ⟨32033252223573313840387685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355501482382209226925123 32033252223573313840387685)
                ·
                  refine ⟨6006234791919996345072691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32033252223573313840387685 6006234791919996345072691)
                  ·
                    refine ⟨9009352187879994517609037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6006234791919996345072691 9009352187879994517609037)
                    ·
                      refine ⟨3378507070454997944103389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9009352187879994517609037 3378507070454997944103389)
                      ·
                        rfl

theorem cell23_6579619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_6579619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579619 prefixEnd_6579619 := by exact prefixLift 6579619
  have htrace : WordTrace (prefixWord ++ tailWord_6579619) baseStart_6579619 baseEnd_6579619 := by
    simpa [prefixWord, tailWord_6579619, baseEnd_6579619] using wordTrace_append hprefix tailTrace_6579619
  have hstable : (prefixWord ++ tailWord_6579619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579619).length < 2 ^ (prefixWord ++ tailWord_6579619).sum := by decide
  have hdescent : baseEnd_6579619 < baseStart_6579619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579659 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 4, 2]
def baseStart_6579659 : Nat := 118140960795 + 6579659 * 2 ^ 59
def prefixEnd_6579659 : Nat := 4983230072969 + 3 ^ 40 * 6579659 * 2
def baseEnd_6579659 : Nat := 3378527609681177787603205

theorem tailTrace_6579659 : CollatzResearch.WordTrace tailWord_6579659 prefixEnd_6579659 3378527609681177787603205 := by
  unfold tailWord_6579659
  simp only [CollatzResearch.WordTrace]
  refine ⟨239979878870026634138686031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159986585913351089425790687 239979878870026634138686031)
  ·
    refine ⟨359969818305039951208029047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239979878870026634138686031 359969818305039951208029047)
    ·
      refine ⟨539954727457559926812043571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359969818305039951208029047 539954727457559926812043571)
      ·
        refine ⟨809932091186339890218065357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539954727457559926812043571 809932091186339890218065357)
        ·
          refine ⟨303724534194877458831774509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 809932091186339890218065357 303724534194877458831774509)
          ·
            refine ⟨113896700323079047061915441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303724534194877458831774509 113896700323079047061915441)
            ·
              refine ⟨85422525242309285296436581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113896700323079047061915441 85422525242309285296436581)
              ·
                refine ⟨16016723482932990993081859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85422525242309285296436581 16016723482932990993081859)
                ·
                  refine ⟨24025085224399486489622789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16016723482932990993081859 24025085224399486489622789)
                  ·
                    refine ⟨4504703479574903716804273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24025085224399486489622789 4504703479574903716804273)
                    ·
                      refine ⟨3378527609681177787603205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504703479574903716804273 3378527609681177787603205)
                      ·
                        rfl

theorem cell23_6579659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4, 2].length) (baseStart_6579659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579659 prefixEnd_6579659 := by exact prefixLift 6579659
  have htrace : WordTrace (prefixWord ++ tailWord_6579659) baseStart_6579659 baseEnd_6579659 := by
    simpa [prefixWord, tailWord_6579659, baseEnd_6579659] using wordTrace_append hprefix tailTrace_6579659
  have hstable : (prefixWord ++ tailWord_6579659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579659).length < 2 ^ (prefixWord ++ tailWord_6579659).sum := by decide
  have hdescent : baseEnd_6579659 < baseStart_6579659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579662 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6579662 : Nat := 118140960795 + 6579662 * 2 ^ 59
def prefixEnd_6579662 : Nat := 4983230072969 + 3 ^ 40 * 6579662 * 2
def baseEnd_6579662 : Nat := 3378529150123141275865691

theorem tailTrace_6579662 : CollatzResearch.WordTrace tailWord_6579662 prefixEnd_6579662 3378529150123141275865691 := by
  unfold tailWord_6579662
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997498536126970706380655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159986658859343843767363493 29997498536126970706380655)
  ·
    refine ⟨44996247804190456059570983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29997498536126970706380655 44996247804190456059570983)
    ·
      refine ⟨67494371706285684089356475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44996247804190456059570983 67494371706285684089356475)
      ·
        refine ⟨101241557559428526134034713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67494371706285684089356475 101241557559428526134034713)
        ·
          refine ⟨75931168169571394600526035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101241557559428526134034713 75931168169571394600526035)
          ·
            refine ⟨113896752254357091900789053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75931168169571394600526035 113896752254357091900789053)
            ·
              refine ⟨42711282095383909462795895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113896752254357091900789053 42711282095383909462795895)
              ·
                refine ⟨64066923143075864194193843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42711282095383909462795895 64066923143075864194193843)
                ·
                  refine ⟨96100384714613796291290765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64066923143075864194193843 96100384714613796291290765)
                  ·
                    refine ⟨36037644267980173609234037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96100384714613796291290765 36037644267980173609234037)
                    ·
                      refine ⟨3378529150123141275865691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36037644267980173609234037 3378529150123141275865691)
                      ·
                        rfl

theorem cell23_6579662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6579662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579662 prefixEnd_6579662 := by exact prefixLift 6579662
  have htrace : WordTrace (prefixWord ++ tailWord_6579662) baseStart_6579662 baseEnd_6579662 := by
    simpa [prefixWord, tailWord_6579662, baseEnd_6579662] using wordTrace_append hprefix tailTrace_6579662
  have hstable : (prefixWord ++ tailWord_6579662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579662).length < 2 ^ (prefixWord ++ tailWord_6579662).sum := by decide
  have hdescent : baseEnd_6579662 < baseStart_6579662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579672 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6579672 : Nat := 118140960795 + 6579672 * 2 ^ 59
def prefixEnd_6579672 : Nat := 4983230072969 + 3 ^ 40 * 6579672 * 2
def baseEnd_6579672 : Nat := 3378534284929686236740645

theorem tailTrace_6579672 : CollatzResearch.WordTrace tailWord_6579672 prefixEnd_6579672 3378534284929686236740645 := by
  unfold tailWord_6579672
  simp only [CollatzResearch.WordTrace]
  refine ⟨119990176509489768679454635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159986902012653024905939513 119990176509489768679454635)
  ·
    refine ⟨179985264764234653019181953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119990176509489768679454635 179985264764234653019181953)
    ·
      refine ⟨134988948573175989764386465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179985264764234653019181953 134988948573175989764386465)
      ·
        refine ⟨101241711429881992323289849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134988948573175989764386465 101241711429881992323289849)
        ·
          refine ⟨75931283572411494242467387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101241711429881992323289849 75931283572411494242467387)
          ·
            refine ⟨113896925358617241363701081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75931283572411494242467387 113896925358617241363701081)
            ·
              refine ⟨85422694018962931022775811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113896925358617241363701081 85422694018962931022775811)
              ·
                refine ⟨128134041028444396534163717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85422694018962931022775811 128134041028444396534163717)
                ·
                  refine ⟨24025132692833324350155697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128134041028444396534163717 24025132692833324350155697)
                  ·
                    refine ⟨18018849519624993262616773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24025132692833324350155697 18018849519624993262616773)
                    ·
                      refine ⟨3378534284929686236740645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18018849519624993262616773 3378534284929686236740645)
                      ·
                        rfl

theorem cell23_6579672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6579672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579672 prefixEnd_6579672 := by exact prefixLift 6579672
  have htrace : WordTrace (prefixWord ++ tailWord_6579672) baseStart_6579672 baseEnd_6579672 := by
    simpa [prefixWord, tailWord_6579672, baseEnd_6579672] using wordTrace_append hprefix tailTrace_6579672
  have hstable : (prefixWord ++ tailWord_6579672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579672).length < 2 ^ (prefixWord ++ tailWord_6579672).sum := by decide
  have hdescent : baseEnd_6579672 < baseStart_6579672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579710 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6579710 : Nat := 118140960795 + 6579710 * 2 ^ 59
def prefixEnd_6579710 : Nat := 4983230072969 + 3 ^ 40 * 6579710 * 2
def baseEnd_6579710 : Nat := 3378553797194557088065471

theorem tailTrace_6579710 : CollatzResearch.WordTrace tailWord_6579710 prefixEnd_6579710 3378553797194557088065471 := by
  unfold tailWord_6579710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997717374105233731099073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159987825995227913232528389 29997717374105233731099073)
  ·
    refine ⟨22498288030578925298324305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29997717374105233731099073 22498288030578925298324305)
    ·
      refine ⟨16873716022934193973743229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22498288030578925298324305 16873716022934193973743229)
      ·
        refine ⟨6327643508600322740153711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16873716022934193973743229 6327643508600322740153711)
        ·
          refine ⟨9491465262900484110230567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327643508600322740153711 9491465262900484110230567)
          ·
            refine ⟨14237197894350726165345851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491465262900484110230567 14237197894350726165345851)
            ·
              refine ⟨21355796841526089248018777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14237197894350726165345851 21355796841526089248018777)
              ·
                refine ⟨16016847631144566936014083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21355796841526089248018777 16016847631144566936014083)
                ·
                  refine ⟨24025271446716850404021125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16016847631144566936014083 24025271446716850404021125)
                  ·
                    refine ⟨4504738396259409450753961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24025271446716850404021125 4504738396259409450753961)
                    ·
                      refine ⟨3378553797194557088065471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504738396259409450753961 3378553797194557088065471)
                      ·
                        rfl

theorem cell23_6579710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6579710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579710 prefixEnd_6579710 := by exact prefixLift 6579710
  have htrace : WordTrace (prefixWord ++ tailWord_6579710) baseStart_6579710 baseEnd_6579710 := by
    simpa [prefixWord, tailWord_6579710, baseEnd_6579710] using wordTrace_append hprefix tailTrace_6579710
  have hstable : (prefixWord ++ tailWord_6579710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579710).length < 2 ^ (prefixWord ++ tailWord_6579710).sum := by decide
  have hdescent : baseEnd_6579710 < baseStart_6579710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579733 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 5]
def baseStart_6579733 : Nat := 118140960795 + 6579733 * 2 ^ 59
def prefixEnd_6579733 : Nat := 4983230072969 + 3 ^ 40 * 6579733 * 2
def baseEnd_6579733 : Nat := 375396178583290055341985

theorem tailTrace_6579733 : CollatzResearch.WordTrace tailWord_6579733 prefixEnd_6579733 375396178583290055341985 := by
  unfold tailWord_6579733
  simp only [CollatzResearch.WordTrace]
  refine ⟨239982577871758544776879853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159988385247839029851253235 239982577871758544776879853)
  ·
    refine ⟨89993466701909454291329945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239982577871758544776879853 89993466701909454291329945)
    ·
      refine ⟨67495100026432090718497459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89993466701909454291329945 67495100026432090718497459)
      ·
        refine ⟨101242650039648136077746189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67495100026432090718497459 101242650039648136077746189)
        ·
          refine ⟨37965993764868051029154821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101242650039648136077746189 37965993764868051029154821)
          ·
            refine ⟨7118623830912759567966529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37965993764868051029154821 7118623830912759567966529)
            ·
              refine ⟨5338967873184569675974897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118623830912759567966529 5338967873184569675974897)
              ·
                refine ⟨4004225904888427256981173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338967873184569675974897 4004225904888427256981173)
                ·
                  refine ⟨375396178583290055341985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004225904888427256981173 375396178583290055341985)
                  ·
                    rfl

theorem cell23_6579733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_6579733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579733 prefixEnd_6579733 := by exact prefixLift 6579733
  have htrace : WordTrace (prefixWord ++ tailWord_6579733) baseStart_6579733 baseEnd_6579733 := by
    simpa [prefixWord, tailWord_6579733, baseEnd_6579733] using wordTrace_append hprefix tailTrace_6579733
  have hstable : (prefixWord ++ tailWord_6579733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579733).length < 2 ^ (prefixWord ++ tailWord_6579733).sum := by decide
  have hdescent : baseEnd_6579733 < baseStart_6579733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579792 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_6579792 : Nat := 118140960795 + 6579792 * 2 ^ 59
def prefixEnd_6579792 : Nat := 4983230072969 + 3 ^ 40 * 6579792 * 2
def baseEnd_6579792 : Nat := 3378595902608225767240093

theorem tailTrace_6579792 : CollatzResearch.WordTrace tailWord_6579792 prefixEnd_6579792 3378595902608225767240093 := by
  unfold tailWord_6579792
  simp only [CollatzResearch.WordTrace]
  refine ⟨119992364889272398926638815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159989819852363198568851753 119992364889272398926638815)
  ·
    refine ⟨179988547333908598389958223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119992364889272398926638815 179988547333908598389958223)
    ·
      refine ⟨269982821000862897584937335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179988547333908598389958223 269982821000862897584937335)
      ·
        refine ⟨404974231501294346377406003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269982821000862897584937335 404974231501294346377406003)
        ·
          refine ⟨607461347251941519566109005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404974231501294346377406003 607461347251941519566109005)
          ·
            refine ⟨227798005219478069837290877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607461347251941519566109005 227798005219478069837290877)
            ·
              refine ⟨85424251957304276188984079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227798005219478069837290877 85424251957304276188984079)
              ·
                refine ⟨128136377935956414283476119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85424251957304276188984079 128136377935956414283476119)
                ·
                  refine ⟨192204566903934621425214179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128136377935956414283476119 192204566903934621425214179)
                  ·
                    refine ⟨288306850355901932137821269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192204566903934621425214179 288306850355901932137821269)
                    ·
                      refine ⟨3378595902608225767240093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 288306850355901932137821269 3378595902608225767240093)
                      ·
                        rfl

theorem cell23_6579792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_6579792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579792 prefixEnd_6579792 := by exact prefixLift 6579792
  have htrace : WordTrace (prefixWord ++ tailWord_6579792) baseStart_6579792 baseEnd_6579792 := by
    simpa [prefixWord, tailWord_6579792, baseEnd_6579792] using wordTrace_append hprefix tailTrace_6579792
  have hstable : (prefixWord ++ tailWord_6579792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579792).length < 2 ^ (prefixWord ++ tailWord_6579792).sum := by decide
  have hdescent : baseEnd_6579792 < baseStart_6579792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579850 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_6579850 : Nat := 118140960795 + 6579850 * 2 ^ 59
def prefixEnd_6579850 : Nat := 4983230072969 + 3 ^ 40 * 6579850 * 2
def baseEnd_6579850 : Nat := 3378625684486186540314827

theorem tailTrace_6579850 : CollatzResearch.WordTrace tailWord_6579850 prefixEnd_6579850 3378625684486186540314827 := by
  unfold tailWord_6579850
  simp only [CollatzResearch.WordTrace]
  refine ⟨59996711303083668439722251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159991230141556449172592669 59996711303083668439722251)
  ·
    refine ⟨89995066954625502659583377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59996711303083668439722251 89995066954625502659583377)
    ·
      refine ⟨67496300215969126994687533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89995066954625502659583377 67496300215969126994687533)
      ·
        refine ⟨25311112580988422623007825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67496300215969126994687533 25311112580988422623007825)
        ·
          refine ⟨18983334435741316967255869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311112580988422623007825 18983334435741316967255869)
          ·
            refine ⟨7118750413402993862720951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18983334435741316967255869 7118750413402993862720951)
            ·
              refine ⟨10678125620104490794081427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118750413402993862720951 10678125620104490794081427)
              ·
                refine ⟨16017188430156736191122141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10678125620104490794081427 16017188430156736191122141)
                ·
                  refine ⟨6006445661308776071670803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16017188430156736191122141 6006445661308776071670803)
                  ·
                    refine ⟨9009668491963164107506205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6006445661308776071670803 9009668491963164107506205)
                    ·
                      refine ⟨3378625684486186540314827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9009668491963164107506205 3378625684486186540314827)
                      ·
                        rfl

theorem cell23_6579850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_6579850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579850 prefixEnd_6579850 := by exact prefixLift 6579850
  have htrace : WordTrace (prefixWord ++ tailWord_6579850) baseStart_6579850 baseEnd_6579850 := by
    simpa [prefixWord, tailWord_6579850, baseEnd_6579850] using wordTrace_append hprefix tailTrace_6579850
  have hstable : (prefixWord ++ tailWord_6579850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579850).length < 2 ^ (prefixWord ++ tailWord_6579850).sum := by decide
  have hdescent : baseEnd_6579850 < baseStart_6579850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579870 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6579870 : Nat := 118140960795 + 6579870 * 2 ^ 59
def prefixEnd_6579870 : Nat := 4983230072969 + 3 ^ 40 * 6579870 * 2
def baseEnd_6579870 : Nat := 1126211984699758820688245

theorem tailTrace_6579870 : CollatzResearch.WordTrace tailWord_6579870 prefixEnd_6579870 1126211984699758820688245 := by
  unfold tailWord_6579870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998446834032777146827133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159991716448174811449744709 29998446834032777146827133)
  ·
    refine ⟨11249417562762291430060175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29998446834032777146827133 11249417562762291430060175)
    ·
      refine ⟨16874126344143437145090263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249417562762291430060175 16874126344143437145090263)
      ·
        refine ⟨25311189516215155717635395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874126344143437145090263 25311189516215155717635395)
        ·
          refine ⟨37966784274322733576453093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25311189516215155717635395 37966784274322733576453093)
          ·
            refine ⟨7118772051435512545584955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37966784274322733576453093 7118772051435512545584955)
            ·
              refine ⟨10678158077153268818377433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118772051435512545584955 10678158077153268818377433)
              ·
                refine ⟨8008618557864951613783075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10678158077153268818377433 8008618557864951613783075)
                ·
                  refine ⟨12012927836797427420674613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008618557864951613783075 12012927836797427420674613)
                  ·
                    refine ⟨1126211984699758820688245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12012927836797427420674613 1126211984699758820688245)
                    ·
                      rfl

theorem cell23_6579870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6579870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579870 prefixEnd_6579870 := by exact prefixLift 6579870
  have htrace : WordTrace (prefixWord ++ tailWord_6579870) baseStart_6579870 baseEnd_6579870 := by
    simpa [prefixWord, tailWord_6579870, baseEnd_6579870] using wordTrace_append hprefix tailTrace_6579870
  have hstable : (prefixWord ++ tailWord_6579870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579870).length < 2 ^ (prefixWord ++ tailWord_6579870).sum := by decide
  have hdescent : baseEnd_6579870 < baseStart_6579870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579873 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6579873 : Nat := 118140960795 + 6579873 * 2 ^ 59
def prefixEnd_6579873 : Nat := 4983230072969 + 3 ^ 40 * 6579873 * 2
def baseEnd_6579873 : Nat := 3378637494541239950327221

theorem tailTrace_6579873 : CollatzResearch.WordTrace tailWord_6579873 prefixEnd_6579873 3378637494541239950327221 := by
  unfold tailWord_6579873
  simp only [CollatzResearch.WordTrace]
  refine ⟨239987684091251348686976273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159991789394167565791317515 239987684091251348686976273)
  ·
    refine ⟨179990763068438511515232205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239987684091251348686976273 179990763068438511515232205)
    ·
      refine ⟨67496536150664441818212077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179990763068438511515232205 67496536150664441818212077)
      ·
        refine ⟨25311201056499165681829529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67496536150664441818212077 25311201056499165681829529)
        ·
          refine ⟨18983400792374374261372147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311201056499165681829529 18983400792374374261372147)
          ·
            refine ⟨28475101188561561392058221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18983400792374374261372147 28475101188561561392058221)
            ·
              refine ⟨10678162945710585522021833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28475101188561561392058221 10678162945710585522021833)
              ·
                refine ⟨8008622209282939141516375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10678162945710585522021833 8008622209282939141516375)
                ·
                  refine ⟨12012933313924408712274563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008622209282939141516375 12012933313924408712274563)
                  ·
                    refine ⟨18019399970886613068411845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12012933313924408712274563 18019399970886613068411845)
                    ·
                      refine ⟨3378637494541239950327221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18019399970886613068411845 3378637494541239950327221)
                      ·
                        rfl

theorem cell23_6579873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6579873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579873 prefixEnd_6579873 := by exact prefixLift 6579873
  have htrace : WordTrace (prefixWord ++ tailWord_6579873) baseStart_6579873 baseEnd_6579873 := by
    simpa [prefixWord, tailWord_6579873, baseEnd_6579873] using wordTrace_append hprefix tailTrace_6579873
  have hstable : (prefixWord ++ tailWord_6579873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579873).length < 2 ^ (prefixWord ++ tailWord_6579873).sum := by decide
  have hdescent : baseEnd_6579873 < baseStart_6579873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579950 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_6579950 : Nat := 118140960795 + 6579950 * 2 ^ 59
def prefixEnd_6579950 : Nat := 4983230072969 + 3 ^ 40 * 6579950 * 2
def baseEnd_6579950 : Nat := 3378677032551636149064367

theorem tailTrace_6579950 : CollatzResearch.WordTrace tailWord_6579950 prefixEnd_6579950 3378677032551636149064367 := by
  unfold tailWord_6579950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998811563996548854691163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159993661674648260558352869 29998811563996548854691163)
  ·
    refine ⟨44998217345994823282036745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29998811563996548854691163 44998217345994823282036745)
    ·
      refine ⟨33748663009496117461527559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44998217345994823282036745 33748663009496117461527559)
      ·
        refine ⟨50622994514244176192291339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33748663009496117461527559 50622994514244176192291339)
        ·
          refine ⟨75934491771366264288437009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50622994514244176192291339 75934491771366264288437009)
          ·
            refine ⟨56950868828524698216327757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75934491771366264288437009 56950868828524698216327757)
            ·
              refine ⟨21356575810696761831122909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56950868828524698216327757 21356575810696761831122909)
              ·
                refine ⟨8008715929011285686671091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21356575810696761831122909 8008715929011285686671091)
                ·
                  refine ⟨12013073893516928530006637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008715929011285686671091 12013073893516928530006637)
                  ·
                    refine ⟨4504902710068848198752489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12013073893516928530006637 4504902710068848198752489)
                    ·
                      refine ⟨3378677032551636149064367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504902710068848198752489 3378677032551636149064367)
                      ·
                        rfl

theorem cell23_6579950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_6579950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579950 prefixEnd_6579950 := by exact prefixLift 6579950
  have htrace : WordTrace (prefixWord ++ tailWord_6579950) baseStart_6579950 baseEnd_6579950 := by
    simpa [prefixWord, tailWord_6579950, baseEnd_6579950] using wordTrace_append hprefix tailTrace_6579950
  have hstable : (prefixWord ++ tailWord_6579950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579950).length < 2 ^ (prefixWord ++ tailWord_6579950).sum := by decide
  have hdescent : baseEnd_6579950 < baseStart_6579950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579976 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6579976 : Nat := 118140960795 + 6579976 * 2 ^ 59
def prefixEnd_6579976 : Nat := 4983230072969 + 3 ^ 40 * 6579976 * 2
def baseEnd_6579976 : Nat := 3378690383048653047339247

theorem tailTrace_6579976 : CollatzResearch.WordTrace tailWord_6579976 prefixEnd_6579976 3378690383048653047339247 := by
  unfold tailWord_6579976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119995720404939098638987891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159994293873252131518650521 119995720404939098638987891)
  ·
    refine ⟨179993580607408647958481837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119995720404939098638987891 179993580607408647958481837)
    ·
      refine ⟨67497592727778242984430689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179993580607408647958481837 67497592727778242984430689)
      ·
        refine ⟨50623194545833682238323017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67497592727778242984430689 50623194545833682238323017)
        ·
          refine ⟨37967395909375261678742263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50623194545833682238323017 37967395909375261678742263)
          ·
            refine ⟨56951093864062892518113395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37967395909375261678742263 56951093864062892518113395)
            ·
              refine ⟨85426640796094338777170093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56951093864062892518113395 85426640796094338777170093)
              ·
                refine ⟨32034990298535377041438785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85426640796094338777170093 32034990298535377041438785)
                ·
                  refine ⟨24026242723901532781079089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32034990298535377041438785 24026242723901532781079089)
                  ·
                    refine ⟨18019682042926149585809317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24026242723901532781079089 18019682042926149585809317)
                    ·
                      refine ⟨3378690383048653047339247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18019682042926149585809317 3378690383048653047339247)
                      ·
                        rfl

theorem cell23_6579976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6579976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579976 prefixEnd_6579976 := by exact prefixLift 6579976
  have htrace : WordTrace (prefixWord ++ tailWord_6579976) baseStart_6579976 baseEnd_6579976 := by
    simpa [prefixWord, tailWord_6579976, baseEnd_6579976] using wordTrace_append hprefix tailTrace_6579976
  have hstable : (prefixWord ++ tailWord_6579976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579976).length < 2 ^ (prefixWord ++ tailWord_6579976).sum := by decide
  have hdescent : baseEnd_6579976 < baseStart_6579976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579980 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_6579980 : Nat := 118140960795 + 6579980 * 2 ^ 59
def prefixEnd_6579980 : Nat := 4983230072969 + 3 ^ 40 * 6579980 * 2
def baseEnd_6579980 : Nat := 3378692436971271031689229

theorem tailTrace_6579980 : CollatzResearch.WordTrace tailWord_6579980 prefixEnd_6579980 3378692436971271031689229 := by
  unfold tailWord_6579980
  simp only [CollatzResearch.WordTrace]
  refine ⟨119995793350931852980560697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159994391134575803974080929 119995793350931852980560697)
  ·
    refine ⟨89996845013198889735420523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119995793350931852980560697 89996845013198889735420523)
    ·
      refine ⟨134995267519798334603130785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89996845013198889735420523 134995267519798334603130785)
      ·
        refine ⟨101246450639848750952348089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134995267519798334603130785 101246450639848750952348089)
        ·
          refine ⟨75934837979886563214261067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101246450639848750952348089 75934837979886563214261067)
          ·
            refine ⟨113902256969829844821391601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75934837979886563214261067 113902256969829844821391601)
            ·
              refine ⟨85426692727372383616043701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113902256969829844821391601 85426692727372383616043701)
              ·
                refine ⟨8008752443191160964004097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85426692727372383616043701 8008752443191160964004097)
                ·
                  refine ⟨6006564332393370723003073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8008752443191160964004097 6006564332393370723003073)
                  ·
                    refine ⟨4504923249295028042252305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006564332393370723003073 4504923249295028042252305)
                    ·
                      refine ⟨3378692436971271031689229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504923249295028042252305 3378692436971271031689229)
                      ·
                        rfl

theorem cell23_6579980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_6579980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579980 prefixEnd_6579980 := by exact prefixLift 6579980
  have htrace : WordTrace (prefixWord ++ tailWord_6579980) baseStart_6579980 baseEnd_6579980 := by
    simpa [prefixWord, tailWord_6579980, baseEnd_6579980] using wordTrace_append hprefix tailTrace_6579980
  have hstable : (prefixWord ++ tailWord_6579980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579980).length < 2 ^ (prefixWord ++ tailWord_6579980).sum := by decide
  have hdescent : baseEnd_6579980 < baseStart_6579980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579981 : List Nat := [1, 7, 2, 1, 2, 1, 2, 7]
def baseStart_6579981 : Nat := 118140960795 + 6579981 * 2 ^ 59
def prefixEnd_6579981 : Nat := 4983230072969 + 3 ^ 40 * 6579981 * 2
def baseEnd_6579981 : Nat := 125136775942663908436175

theorem tailTrace_6579981 : CollatzResearch.WordTrace tailWord_6579981 prefixEnd_6579981 125136775942663908436175 := by
  unfold tailWord_6579981
  simp only [CollatzResearch.WordTrace]
  refine ⟨239991623174860083131907797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159994415449906722087938531 239991623174860083131907797)
  ·
    refine ⟨5624803668160783198404089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 239991623174860083131907797 5624803668160783198404089)
    ·
      refine ⟨4218602751120587398803067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5624803668160783198404089 4218602751120587398803067)
      ·
        refine ⟨6327904126680881098204601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218602751120587398803067 6327904126680881098204601)
        ·
          refine ⟨4745928095010660823653451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6327904126680881098204601 4745928095010660823653451)
          ·
            refine ⟨7118892142515991235480177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745928095010660823653451 7118892142515991235480177)
            ·
              refine ⟨5339169106886993426610133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118892142515991235480177 5339169106886993426610133)
              ·
                refine ⟨125136775942663908436175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5339169106886993426610133 125136775942663908436175)
                ·
                  rfl

theorem cell23_6579981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 7].length) (baseStart_6579981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579981 prefixEnd_6579981 := by exact prefixLift 6579981
  have htrace : WordTrace (prefixWord ++ tailWord_6579981) baseStart_6579981 baseEnd_6579981 := by
    simpa [prefixWord, tailWord_6579981, baseEnd_6579981] using wordTrace_append hprefix tailTrace_6579981
  have hstable : (prefixWord ++ tailWord_6579981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579981).length < 2 ^ (prefixWord ++ tailWord_6579981).sum := by decide
  have hdescent : baseEnd_6579981 < baseStart_6579981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580003 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 5]
def baseStart_6580003 : Nat := 118140960795 + 6580003 * 2 ^ 59
def prefixEnd_6580003 : Nat := 4983230072969 + 3 ^ 40 * 6580003 * 2
def baseEnd_6580003 : Nat := 375411583002924937966847

theorem tailTrace_6580003 : CollatzResearch.WordTrace tailWord_6580003 prefixEnd_6580003 375411583002924937966847 := by
  unfold tailWord_6580003
  simp only [CollatzResearch.WordTrace]
  refine ⟨239992425580780380889208663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159994950387186920592805775 239992425580780380889208663)
  ·
    refine ⟨359988638371170571333812995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239992425580780380889208663 359988638371170571333812995)
    ·
      refine ⟨539982957556755857000719493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359988638371170571333812995 539982957556755857000719493)
      ·
        refine ⟨101246804541891723187634905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 539982957556755857000719493 101246804541891723187634905)
        ·
          refine ⟨75935103406418792390726179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101246804541891723187634905 75935103406418792390726179)
          ·
            refine ⟨113902655109628188586089269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75935103406418792390726179 113902655109628188586089269)
            ·
              refine ⟨10678373916527642679945869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113902655109628188586089269 10678373916527642679945869)
              ·
                refine ⟨4004390218697866004979701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10678373916527642679945869 4004390218697866004979701)
                ·
                  refine ⟨375411583002924937966847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004390218697866004979701 375411583002924937966847)
                  ·
                    rfl

theorem cell23_6580003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 5].length) (baseStart_6580003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580003 prefixEnd_6580003 := by exact prefixLift 6580003
  have htrace : WordTrace (prefixWord ++ tailWord_6580003) baseStart_6580003 baseEnd_6580003 := by
    simpa [prefixWord, tailWord_6580003, baseEnd_6580003] using wordTrace_append hprefix tailTrace_6580003
  have hstable : (prefixWord ++ tailWord_6580003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580003).length < 2 ^ (prefixWord ++ tailWord_6580003).sum := by decide
  have hdescent : baseEnd_6580003 < baseStart_6580003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580020 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6580020 : Nat := 118140960795 + 6580020 * 2 ^ 59
def prefixEnd_6580020 : Nat := 4983230072969 + 3 ^ 40 * 6580020 * 2
def baseEnd_6580020 : Nat := 375412552910827875021005

theorem tailTrace_6580020 : CollatzResearch.WordTrace tailWord_6580020 prefixEnd_6580020 375412552910827875021005 := by
  unfold tailWord_6580020
  simp only [CollatzResearch.WordTrace]
  refine ⟨119996522810859396396288757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159995363747812528528385009 119996522810859396396288757)
  ·
    refine ⟨11249674013518068412152071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119996522810859396396288757 11249674013518068412152071)
    ·
      refine ⟨16874511020277102618228107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249674013518068412152071 16874511020277102618228107)
      ·
        refine ⟨25311766530415653927342161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874511020277102618228107 25311766530415653927342161)
        ·
          refine ⟨18983824897811740445506621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311766530415653927342161 18983824897811740445506621)
          ·
            refine ⟨7118934336679402667064983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18983824897811740445506621 7118934336679402667064983)
            ·
              refine ⟨10678401505019104000597475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118934336679402667064983 10678401505019104000597475)
              ·
                refine ⟨16017602257528656000896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10678401505019104000597475 16017602257528656000896213)
                ·
                  refine ⟨375412552910827875021005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16017602257528656000896213 375412552910827875021005)
                  ·
                    rfl

theorem cell23_6580020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6580020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580020 prefixEnd_6580020 := by exact prefixLift 6580020
  have htrace : WordTrace (prefixWord ++ tailWord_6580020) baseStart_6580020 baseEnd_6580020 := by
    simpa [prefixWord, tailWord_6580020, baseEnd_6580020] using wordTrace_append hprefix tailTrace_6580020
  have hstable : (prefixWord ++ tailWord_6580020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580020).length < 2 ^ (prefixWord ++ tailWord_6580020).sum := by decide
  have hdescent : baseEnd_6580020 < baseStart_6580020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580026 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_6580026 : Nat := 118140960795 + 6580026 * 2 ^ 59
def prefixEnd_6580026 : Nat := 4983230072969 + 3 ^ 40 * 6580026 * 2
def baseEnd_6580026 : Nat := 3378716057081377851714017

theorem tailTrace_6580026 : CollatzResearch.WordTrace tailWord_6580026 prefixEnd_6580026 3378716057081377851714017 := by
  unfold tailWord_6580026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59998316114924263954323983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159995509639798037211530621 59998316114924263954323983)
  ·
    refine ⟨89997474172386395931485975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59998316114924263954323983 89997474172386395931485975)
    ·
      refine ⟨134996211258579593897228963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89997474172386395931485975 134996211258579593897228963)
      ·
        refine ⟨202494316887869390845843445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134996211258579593897228963 202494316887869390845843445)
        ·
          refine ⟨18983842208237755391797823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202494316887869390845843445 18983842208237755391797823)
          ·
            refine ⟨28475763312356633087696735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18983842208237755391797823 28475763312356633087696735)
            ·
              refine ⟨42713644968534949631545103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28475763312356633087696735 42713644968534949631545103)
              ·
                refine ⟨64070467452802424447317655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42713644968534949631545103 64070467452802424447317655)
                ·
                  refine ⟨96105701179203636670976483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64070467452802424447317655 96105701179203636670976483)
                  ·
                    refine ⟨144158551768805455006464725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96105701179203636670976483 144158551768805455006464725)
                    ·
                      refine ⟨3378716057081377851714017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144158551768805455006464725 3378716057081377851714017)
                      ·
                        rfl

theorem cell23_6580026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_6580026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580026 prefixEnd_6580026 := by exact prefixLift 6580026
  have htrace : WordTrace (prefixWord ++ tailWord_6580026) baseStart_6580026 baseEnd_6580026 := by
    simpa [prefixWord, tailWord_6580026, baseEnd_6580026] using wordTrace_append hprefix tailTrace_6580026
  have hstable : (prefixWord ++ tailWord_6580026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580026).length < 2 ^ (prefixWord ++ tailWord_6580026).sum := by decide
  have hdescent : baseEnd_6580026 < baseStart_6580026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580031 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 2, 2, 2]
def baseStart_6580031 : Nat := 118140960795 + 6580031 * 2 ^ 59
def prefixEnd_6580031 : Nat := 4983230072969 + 3 ^ 40 * 6580031 * 2
def baseEnd_6580031 : Nat := 3378718624484650332151495

theorem tailTrace_6580031 : CollatzResearch.WordTrace tailWord_6580031 prefixEnd_6580031 3378718624484650332151495 := by
  unfold tailWord_6580031
  simp only [CollatzResearch.WordTrace]
  refine ⟨239993446824678941671227947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159995631216452627780818631 239993446824678941671227947)
  ·
    refine ⟨359990170237018412506841921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239993446824678941671227947 359990170237018412506841921)
    ·
      refine ⟨269992627677763809380131441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359990170237018412506841921 269992627677763809380131441)
      ·
        refine ⟨202494470758322857035098581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269992627677763809380131441 202494470758322857035098581)
        ·
          refine ⟨4745964158398191961760123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 202494470758322857035098581 4745964158398191961760123)
          ·
            refine ⟨7118946237597287942640185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745964158398191961760123 7118946237597287942640185)
            ·
              refine ⟨5339209678197965956980139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118946237597287942640185 5339209678197965956980139)
              ·
                refine ⟨8008814517296948935470209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339209678197965956980139 8008814517296948935470209)
                ·
                  refine ⟨6006610887972711701602657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8008814517296948935470209 6006610887972711701602657)
                  ·
                    refine ⟨4504958165979533776201993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006610887972711701602657 4504958165979533776201993)
                    ·
                      refine ⟨3378718624484650332151495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504958165979533776201993 3378718624484650332151495)
                      ·
                        rfl

theorem cell23_6580031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_6580031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580031 prefixEnd_6580031 := by exact prefixLift 6580031
  have htrace : WordTrace (prefixWord ++ tailWord_6580031) baseStart_6580031 baseEnd_6580031 := by
    simpa [prefixWord, tailWord_6580031, baseEnd_6580031] using wordTrace_append hprefix tailTrace_6580031
  have hstable : (prefixWord ++ tailWord_6580031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580031).length < 2 ^ (prefixWord ++ tailWord_6580031).sum := by decide
  have hdescent : baseEnd_6580031 < baseStart_6580031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580053 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6580053 : Nat := 118140960795 + 6580053 * 2 ^ 59
def prefixEnd_6580053 : Nat := 4983230072969 + 3 ^ 40 * 6580053 * 2
def baseEnd_6580053 : Nat := 3378729921059049246076393

theorem tailTrace_6580053 : CollatzResearch.WordTrace tailWord_6580053 prefixEnd_6580053 3378729921059049246076393 := by
  unfold tailWord_6580053
  simp only [CollatzResearch.WordTrace]
  refine ⟨239994249230599239428528813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159996166153732826285685875 239994249230599239428528813)
  ·
    refine ⟨89997843461474714785698305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239994249230599239428528813 89997843461474714785698305)
    ·
      refine ⟨67498382596106036089273729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89997843461474714785698305 67498382596106036089273729)
      ·
        refine ⟨50623786947079527066955297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67498382596106036089273729 50623786947079527066955297)
        ·
          refine ⟨37967840210309645300216473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50623786947079527066955297 37967840210309645300216473)
          ·
            refine ⟨28475880157732233975162355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37967840210309645300216473 28475880157732233975162355)
            ·
              refine ⟨42713820236598350962743533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28475880157732233975162355 42713820236598350962743533)
              ·
                refine ⟨16017682588724381611028825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42713820236598350962743533 16017682588724381611028825)
                ·
                  refine ⟨12013261941543286208271619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16017682588724381611028825 12013261941543286208271619)
                  ·
                    refine ⟨18019892912314929312407429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12013261941543286208271619 18019892912314929312407429)
                    ·
                      refine ⟨3378729921059049246076393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18019892912314929312407429 3378729921059049246076393)
                      ·
                        rfl

theorem cell23_6580053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6580053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580053 prefixEnd_6580053 := by exact prefixLift 6580053
  have htrace : WordTrace (prefixWord ++ tailWord_6580053) baseStart_6580053 baseEnd_6580053 := by
    simpa [prefixWord, tailWord_6580053, baseEnd_6580053] using wordTrace_append hprefix tailTrace_6580053
  have hstable : (prefixWord ++ tailWord_6580053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580053).length < 2 ^ (prefixWord ++ tailWord_6580053).sum := by decide
  have hdescent : baseEnd_6580053 < baseStart_6580053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580097 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6580097 : Nat := 118140960795 + 6580097 * 2 ^ 59
def prefixEnd_6580097 : Nat := 4983230072969 + 3 ^ 40 * 6580097 * 2
def baseEnd_6580097 : Nat := 1126250838069282357975397

theorem tailTrace_6580097 : CollatzResearch.WordTrace tailWord_6580097 prefixEnd_6580097 1126250838069282357975397 := by
  unfold tailWord_6580097
  simp only [CollatzResearch.WordTrace]
  refine ⟨239995854042439834943130545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159997236028293223295420363 239995854042439834943130545)
  ·
    refine ⟨179996890531829876207347909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239995854042439834943130545 179996890531829876207347909)
    ·
      refine ⟨33749416974718101788877733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179996890531829876207347909 33749416974718101788877733)
      ·
        refine ⟨6328015682759644085414575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33749416974718101788877733 6328015682759644085414575)
        ·
          refine ⟨9492023524139466128121863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328015682759644085414575 9492023524139466128121863)
          ·
            refine ⟨14238035286209199192182795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492023524139466128121863 14238035286209199192182795)
            ·
              refine ⟨21357052929313798788274193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238035286209199192182795 21357052929313798788274193)
              ·
                refine ⟨16017789696985349091205645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21357052929313798788274193 16017789696985349091205645)
                ·
                  refine ⟨6006671136369505909202117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16017789696985349091205645 6006671136369505909202117)
                  ·
                    refine ⟨1126250838069282357975397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6006671136369505909202117 1126250838069282357975397)
                    ·
                      rfl

theorem cell23_6580097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6580097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580097 prefixEnd_6580097 := by exact prefixLift 6580097
  have htrace : WordTrace (prefixWord ++ tailWord_6580097) baseStart_6580097 baseEnd_6580097 := by
    simpa [prefixWord, tailWord_6580097, baseEnd_6580097] using wordTrace_append hprefix tailTrace_6580097
  have hstable : (prefixWord ++ tailWord_6580097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580097).length < 2 ^ (prefixWord ++ tailWord_6580097).sum := by decide
  have hdescent : baseEnd_6580097 < baseStart_6580097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580114 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6580114 : Nat := 118140960795 + 6580114 * 2 ^ 59
def prefixEnd_6580114 : Nat := 4983230072969 + 3 ^ 40 * 6580114 * 2
def baseEnd_6580114 : Nat := 1126253747792991169137871

theorem tailTrace_6580114 : CollatzResearch.WordTrace tailWord_6580114 prefixEnd_6580114 1126253747792991169137871 := by
  unfold tailWord_6580114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59999118520844561711624849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159997649388918831230999597 59999118520844561711624849)
  ·
    refine ⟨44999338890633421283718637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59999118520844561711624849 44999338890633421283718637)
    ·
      refine ⟨16874752083987532981394489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44999338890633421283718637 16874752083987532981394489)
      ·
        refine ⟨12656064062990649736045867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16874752083987532981394489 12656064062990649736045867)
        ·
          refine ⟨18984096094485974604068801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12656064062990649736045867 18984096094485974604068801)
          ·
            refine ⟨14238072070864480953051601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18984096094485974604068801 14238072070864480953051601)
            ·
              refine ⟨10678554053148360714788701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14238072070864480953051601 10678554053148360714788701)
              ·
                refine ⟨4004457769930635268045763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10678554053148360714788701 4004457769930635268045763)
                ·
                  refine ⟨6006686654895952902068645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004457769930635268045763 6006686654895952902068645)
                  ·
                    refine ⟨1126253747792991169137871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6006686654895952902068645 1126253747792991169137871)
                    ·
                      rfl

theorem cell23_6580114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6580114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580114 prefixEnd_6580114 := by exact prefixLift 6580114
  have htrace : WordTrace (prefixWord ++ tailWord_6580114) baseStart_6580114 baseEnd_6580114 := by
    simpa [prefixWord, tailWord_6580114, baseEnd_6580114] using wordTrace_append hprefix tailTrace_6580114
  have hstable : (prefixWord ++ tailWord_6580114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580114).length < 2 ^ (prefixWord ++ tailWord_6580114).sum := by decide
  have hdescent : baseEnd_6580114 < baseStart_6580114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580127 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 6]
def baseStart_6580127 : Nat := 118140960795 + 6580127 * 2 ^ 59
def prefixEnd_6580127 : Nat := 4983230072969 + 3 ^ 40 * 6580127 * 2
def baseEnd_6580127 : Nat := 375418657625275772950117

theorem tailTrace_6580127 : CollatzResearch.WordTrace tailWord_6580127 prefixEnd_6580127 375418657625275772950117 := by
  unfold tailWord_6580127
  simp only [CollatzResearch.WordTrace]
  refine ⟨239996948232331150066722635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159997965488220766711148423 239996948232331150066722635)
  ·
    refine ⟨359995422348496725100083953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239996948232331150066722635 359995422348496725100083953)
    ·
      refine ⟨269996566761372543825062965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359995422348496725100083953 269996566761372543825062965)
      ·
        refine ⟨25312178133878675983599653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269996566761372543825062965 25312178133878675983599653)
        ·
          refine ⟨4746033400102251746924935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25312178133878675983599653 4746033400102251746924935)
          ·
            refine ⟨7119050100153377620387403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746033400102251746924935 7119050100153377620387403)
            ·
              refine ⟨10678575150230066430581105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119050100153377620387403 10678575150230066430581105)
              ·
                refine ⟨8008931362672549822935829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10678575150230066430581105 8008931362672549822935829)
                ·
                  refine ⟨375418657625275772950117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8008931362672549822935829 375418657625275772950117)
                  ·
                    rfl

theorem cell23_6580127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 6].length) (baseStart_6580127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580127 prefixEnd_6580127 := by exact prefixLift 6580127
  have htrace : WordTrace (prefixWord ++ tailWord_6580127) baseStart_6580127 baseEnd_6580127 := by
    simpa [prefixWord, tailWord_6580127, baseEnd_6580127] using wordTrace_append hprefix tailTrace_6580127
  have hstable : (prefixWord ++ tailWord_6580127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580127).length < 2 ^ (prefixWord ++ tailWord_6580127).sum := by decide
  have hdescent : baseEnd_6580127 < baseStart_6580127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580160 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_6580160 : Nat := 118140960795 + 6580160 * 2 ^ 59
def prefixEnd_6580160 : Nat := 4983230072969 + 3 ^ 40 * 6580160 * 2
def baseEnd_6580160 : Nat := 3378784863489080327438401

theorem tailTrace_6580160 : CollatzResearch.WordTrace tailWord_6580160 prefixEnd_6580160 3378784863489080327438401 := by
  unfold tailWord_6580160
  simp only [CollatzResearch.WordTrace]
  refine ⟨119999075920605798351336967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159998767894141064468449289 119999075920605798351336967)
  ·
    refine ⟨179998613880908697527005451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119999075920605798351336967 179998613880908697527005451)
    ·
      refine ⟨269997920821363046290508177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179998613880908697527005451 269997920821363046290508177)
      ·
        refine ⟨202498440616022284717881133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269997920821363046290508177 202498440616022284717881133)
        ·
          refine ⟨75936915231008356769205425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202498440616022284717881133 75936915231008356769205425)
          ·
            refine ⟨56952686423256267576904069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75936915231008356769205425 56952686423256267576904069)
            ·
              refine ⟨10678628704360550170669513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56952686423256267576904069 10678628704360550170669513)
              ·
                refine ⟨8008971528270412628002135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10678628704360550170669513 8008971528270412628002135)
                ·
                  refine ⟨12013457292405618942003203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008971528270412628002135 12013457292405618942003203)
                  ·
                    refine ⟨18020185938608428413004805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12013457292405618942003203 18020185938608428413004805)
                    ·
                      refine ⟨3378784863489080327438401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18020185938608428413004805 3378784863489080327438401)
                      ·
                        rfl

theorem cell23_6580160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_6580160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580160 prefixEnd_6580160 := by exact prefixLift 6580160
  have htrace : WordTrace (prefixWord ++ tailWord_6580160) baseStart_6580160 baseEnd_6580160 := by
    simpa [prefixWord, tailWord_6580160, baseEnd_6580160] using wordTrace_append hprefix tailTrace_6580160
  have hstable : (prefixWord ++ tailWord_6580160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580160).length < 2 ^ (prefixWord ++ tailWord_6580160).sum := by decide
  have hdescent : baseEnd_6580160 < baseStart_6580160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580180 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6580180 : Nat := 118140960795 + 6580180 * 2 ^ 59
def prefixEnd_6580180 : Nat := 4983230072969 + 3 ^ 40 * 6580180 * 2
def baseEnd_6580180 : Nat := 3378795133102170249188309

theorem tailTrace_6580180 : CollatzResearch.WordTrace tailWord_6580180 prefixEnd_6580180 3378795133102170249188309 := by
  unfold tailWord_6580180
  simp only [CollatzResearch.WordTrace]
  refine ⟨119999440650569570059200997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159999254200759426745601329 119999440650569570059200997)
  ·
    refine ⟨22499895121981794386100187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119999440650569570059200997 22499895121981794386100187)
    ·
      refine ⟨33749842682972691579150281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22499895121981794386100187 33749842682972691579150281)
      ·
        refine ⟨25312382012229518684362711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33749842682972691579150281 25312382012229518684362711)
        ·
          refine ⟨37968573018344278026544067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25312382012229518684362711 37968573018344278026544067)
          ·
            refine ⟨56952859527516417039816101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37968573018344278026544067 56952859527516417039816101)
            ·
              refine ⟨10678661161409328194965519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56952859527516417039816101 10678661161409328194965519)
              ·
                refine ⟨16017991742113992292448279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10678661161409328194965519 16017991742113992292448279)
                ·
                  refine ⟨24026987613170988438672419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16017991742113992292448279 24026987613170988438672419)
                  ·
                    refine ⟨36040481419756482658008629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24026987613170988438672419 36040481419756482658008629)
                    ·
                      refine ⟨3378795133102170249188309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36040481419756482658008629 3378795133102170249188309)
                      ·
                        rfl

theorem cell23_6580180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6580180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580180 prefixEnd_6580180 := by exact prefixLift 6580180
  have htrace : WordTrace (prefixWord ++ tailWord_6580180) baseStart_6580180 baseEnd_6580180 := by
    simpa [prefixWord, tailWord_6580180, baseEnd_6580180] using wordTrace_append hprefix tailTrace_6580180
  have hstable : (prefixWord ++ tailWord_6580180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580180).length < 2 ^ (prefixWord ++ tailWord_6580180).sum := by decide
  have hdescent : baseEnd_6580180 < baseStart_6580180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580188 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6580188 : Nat := 118140960795 + 6580188 * 2 ^ 59
def prefixEnd_6580188 : Nat := 4983230072969 + 3 ^ 40 * 6580188 * 2
def baseEnd_6580188 : Nat := 3378799240947406217888273

theorem tailTrace_6580188 : CollatzResearch.WordTrace tailWord_6580188 prefixEnd_6580188 3378799240947406217888273 := by
  unfold tailWord_6580188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119999586542555078742346609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159999448723406771656462145 119999586542555078742346609)
  ·
    refine ⟨89999689906916309056759957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119999586542555078742346609 89999689906916309056759957)
    ·
      refine ⟨4218735464386701987035623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89999689906916309056759957 4218735464386701987035623)
      ·
        refine ⟨6328103196580052980553435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218735464386701987035623 6328103196580052980553435)
        ·
          refine ⟨9492154794870079470830153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328103196580052980553435 9492154794870079470830153)
          ·
            refine ⟨7119116096152559603122615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9492154794870079470830153 7119116096152559603122615)
            ·
              refine ⟨10678674144228839404683923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119116096152559603122615 10678674144228839404683923)
              ·
                refine ⟨16018011216343259107025885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10678674144228839404683923 16018011216343259107025885)
                ·
                  refine ⟨6006754206128722165134707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16018011216343259107025885 6006754206128722165134707)
                  ·
                    refine ⟨9010131309193083247702061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6006754206128722165134707 9010131309193083247702061)
                    ·
                      refine ⟨3378799240947406217888273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010131309193083247702061 3378799240947406217888273)
                      ·
                        rfl

theorem cell23_6580188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6580188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580188 prefixEnd_6580188 := by exact prefixLift 6580188
  have htrace : WordTrace (prefixWord ++ tailWord_6580188) baseStart_6580188 baseEnd_6580188 := by
    simpa [prefixWord, tailWord_6580188, baseEnd_6580188] using wordTrace_append hprefix tailTrace_6580188
  have hstable : (prefixWord ++ tailWord_6580188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580188).length < 2 ^ (prefixWord ++ tailWord_6580188).sum := by decide
  have hdescent : baseEnd_6580188 < baseStart_6580188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580245 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_6580245 : Nat := 118140960795 + 6580245 * 2 ^ 59
def prefixEnd_6580245 : Nat := 4983230072969 + 3 ^ 40 * 6580245 * 2
def baseEnd_6580245 : Nat := 3378828509344712494875511

theorem tailTrace_6580245 : CollatzResearch.WordTrace tailWord_6580245 prefixEnd_6580245 3378828509344712494875511 := by
  unfold tailWord_6580245
  simp only [CollatzResearch.WordTrace]
  refine ⟨240001252045903656219518189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160000834697269104146345459 240001252045903656219518189)
  ·
    refine ⟨90000469517213871082319321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240001252045903656219518189 90000469517213871082319321)
    ·
      refine ⟨67500352137910403311739491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90000469517213871082319321 67500352137910403311739491)
      ·
        refine ⟨101250528206865604967609237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67500352137910403311739491 101250528206865604967609237)
        ·
          refine ⟨4746118509696825232856683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101250528206865604967609237 4746118509696825232856683)
          ·
            refine ⟨7119177764545237849285025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746118509696825232856683 7119177764545237849285025)
            ·
              refine ⟨5339383323408928386963769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119177764545237849285025 5339383323408928386963769)
              ·
                refine ⟨4004537492556696290222827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339383323408928386963769 4004537492556696290222827)
                ·
                  refine ⟨6006806238835044435334241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004537492556696290222827 6006806238835044435334241)
                  ·
                    refine ⟨4505104679126283326500681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006806238835044435334241 4505104679126283326500681)
                    ·
                      refine ⟨3378828509344712494875511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505104679126283326500681 3378828509344712494875511)
                      ·
                        rfl

theorem cell23_6580245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_6580245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580245 prefixEnd_6580245 := by exact prefixLift 6580245
  have htrace : WordTrace (prefixWord ++ tailWord_6580245) baseStart_6580245 baseEnd_6580245 := by
    simpa [prefixWord, tailWord_6580245, baseEnd_6580245] using wordTrace_append hprefix tailTrace_6580245
  have hstable : (prefixWord ++ tailWord_6580245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580245).length < 2 ^ (prefixWord ++ tailWord_6580245).sum := by decide
  have hdescent : baseEnd_6580245 < baseStart_6580245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580273 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 9]
def baseStart_6580273 : Nat := 118140960795 + 6580273 * 2 ^ 59
def prefixEnd_6580273 : Nat := 4983230072969 + 3 ^ 40 * 6580273 * 2
def baseEnd_6580273 : Nat := 375426987422559820591709

theorem tailTrace_6580273 : CollatzResearch.WordTrace tailWord_6580273 prefixEnd_6580273 375426987422559820591709 := by
  unfold tailWord_6580273
  simp only [CollatzResearch.WordTrace]
  refine ⟨240002273289802217001537473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160001515526534811334358315 240002273289802217001537473)
  ·
    refine ⟨180001704967351662751153105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240002273289802217001537473 180001704967351662751153105)
    ·
      refine ⟨135001278725513747063364829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180001704967351662751153105 135001278725513747063364829)
      ·
        refine ⟨50625479522067655148761811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135001278725513747063364829 50625479522067655148761811)
        ·
          refine ⟨75938219283101482723142717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50625479522067655148761811 75938219283101482723142717)
          ·
            refine ⟨28476832231163056021178519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75938219283101482723142717 28476832231163056021178519)
            ·
              refine ⟨42715248346744584031767779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28476832231163056021178519 42715248346744584031767779)
              ·
                refine ⟨64072872520116876047651669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42715248346744584031767779 64072872520116876047651669)
                ·
                  refine ⟨375426987422559820591709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64072872520116876047651669 375426987422559820591709)
                  ·
                    rfl

theorem cell23_6580273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_6580273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580273 prefixEnd_6580273 := by exact prefixLift 6580273
  have htrace : WordTrace (prefixWord ++ tailWord_6580273) baseStart_6580273 baseEnd_6580273 := by
    simpa [prefixWord, tailWord_6580273, baseEnd_6580273] using wordTrace_append hprefix tailTrace_6580273
  have hstable : (prefixWord ++ tailWord_6580273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580273).length < 2 ^ (prefixWord ++ tailWord_6580273).sum := by decide
  have hdescent : baseEnd_6580273 < baseStart_6580273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580300 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6580300 : Nat := 118140960795 + 6580300 * 2 ^ 59
def prefixEnd_6580300 : Nat := 4983230072969 + 3 ^ 40 * 6580300 * 2
def baseEnd_6580300 : Nat := 3378856750780709779687757

theorem tailTrace_6580300 : CollatzResearch.WordTrace tailWord_6580300 prefixEnd_6580300 3378856750780709779687757 := by
  unfold tailWord_6580300
  simp only [CollatzResearch.WordTrace]
  refine ⟨120001629030352200306385177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160002172040469600408513569 120001629030352200306385177)
  ·
    refine ⟨90001221772764150229788883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120001629030352200306385177 90001221772764150229788883)
    ·
      refine ⟨135001832659146225344683325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90001221772764150229788883 135001832659146225344683325)
      ·
        refine ⟨50625687247179834504256247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135001832659146225344683325 50625687247179834504256247)
        ·
          refine ⟨75938530870769751756384371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50625687247179834504256247 75938530870769751756384371)
          ·
            refine ⟨113907796306154627634576557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75938530870769751756384371 113907796306154627634576557)
            ·
              refine ⟨42715423614807985362966209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113907796306154627634576557 42715423614807985362966209)
              ·
                refine ⟨32036567711105989022224657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42715423614807985362966209 32036567711105989022224657)
                ·
                  refine ⟨24027425783329491766668493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32036567711105989022224657 24027425783329491766668493)
                  ·
                    refine ⟨9010284668748559412500685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24027425783329491766668493 9010284668748559412500685)
                    ·
                      refine ⟨3378856750780709779687757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010284668748559412500685 3378856750780709779687757)
                      ·
                        rfl

theorem cell23_6580300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6580300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580300 prefixEnd_6580300 := by exact prefixLift 6580300
  have htrace : WordTrace (prefixWord ++ tailWord_6580300) baseStart_6580300 baseEnd_6580300 := by
    simpa [prefixWord, tailWord_6580300, baseEnd_6580300] using wordTrace_append hprefix tailTrace_6580300
  have hstable : (prefixWord ++ tailWord_6580300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580300).length < 2 ^ (prefixWord ++ tailWord_6580300).sum := by decide
  have hdescent : baseEnd_6580300 < baseStart_6580300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580313 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_6580313 : Nat := 118140960795 + 6580313 * 2 ^ 59
def prefixEnd_6580313 : Nat := 4983230072969 + 3 ^ 40 * 6580313 * 2
def baseEnd_6580313 : Nat := 3378863426029218228825197

theorem tailTrace_6580313 : CollatzResearch.WordTrace tailWord_6580313 prefixEnd_6580313 3378863426029218228825197 := by
  unfold tailWord_6580313
  simp only [CollatzResearch.WordTrace]
  refine ⟨240003732209657303832993593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160002488139771535888662395 240003732209657303832993593)
  ·
    refine ⟨180002799157242977874745195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240003732209657303832993593 180002799157242977874745195)
    ·
      refine ⟨270004198735864466812117793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180002799157242977874745195 270004198735864466812117793)
      ·
        refine ⟨202503149051898350109088345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270004198735864466812117793 202503149051898350109088345)
        ·
          refine ⟨151877361788923762581816259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202503149051898350109088345 151877361788923762581816259)
          ·
            refine ⟨227816042683385643872724389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151877361788923762581816259 227816042683385643872724389)
            ·
              refine ⟨42715508003134808226135823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227816042683385643872724389 42715508003134808226135823)
              ·
                refine ⟨64073262004702212339203735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42715508003134808226135823 64073262004702212339203735)
                ·
                  refine ⟨96109893007053318508805603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64073262004702212339203735 96109893007053318508805603)
                  ·
                    refine ⟨144164839510579977763208405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96109893007053318508805603 144164839510579977763208405)
                    ·
                      refine ⟨3378863426029218228825197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144164839510579977763208405 3378863426029218228825197)
                      ·
                        rfl

theorem cell23_6580313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_6580313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580313 prefixEnd_6580313 := by exact prefixLift 6580313
  have htrace : WordTrace (prefixWord ++ tailWord_6580313) baseStart_6580313 baseEnd_6580313 := by
    simpa [prefixWord, tailWord_6580313, baseEnd_6580313] using wordTrace_append hprefix tailTrace_6580313
  have hstable : (prefixWord ++ tailWord_6580313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580313).length < 2 ^ (prefixWord ++ tailWord_6580313).sum := by decide
  have hdescent : baseEnd_6580313 < baseStart_6580313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580357 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_6580357 : Nat := 118140960795 + 6580357 * 2 ^ 59
def prefixEnd_6580357 : Nat := 4983230072969 + 3 ^ 40 * 6580357 * 2
def baseEnd_6580357 : Nat := 3378886019178016056674995

theorem tailTrace_6580357 : CollatzResearch.WordTrace tailWord_6580357 prefixEnd_6580357 3378886019178016056674995 := by
  unfold tailWord_6580357
  simp only [CollatzResearch.WordTrace]
  refine ⟨240005337021497899347595325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160003558014331932898396883 240005337021497899347595325)
  ·
    refine ⟨90002001383061712255348247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240005337021497899347595325 90002001383061712255348247)
    ·
      refine ⟨135003002074592568383022371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90002001383061712255348247 135003002074592568383022371)
      ·
        refine ⟨202504503111888852574533557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135003002074592568383022371 202504503111888852574533557)
        ·
          refine ⟨18984797166739579928862521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202504503111888852574533557 18984797166739579928862521)
          ·
            refine ⟨14238597875054684946646891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18984797166739579928862521 14238597875054684946646891)
            ·
              refine ⟨21357896812582027419970337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238597875054684946646891 21357896812582027419970337)
              ·
                refine ⟨16018422609436520564977753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21357896812582027419970337 16018422609436520564977753)
                ·
                  refine ⟨12013816957077390423733315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16018422609436520564977753 12013816957077390423733315)
                  ·
                    refine ⟨18020725435616085635599973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12013816957077390423733315 18020725435616085635599973)
                    ·
                      refine ⟨3378886019178016056674995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18020725435616085635599973 3378886019178016056674995)
                      ·
                        rfl

theorem cell23_6580357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_6580357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580357 prefixEnd_6580357 := by exact prefixLift 6580357
  have htrace : WordTrace (prefixWord ++ tailWord_6580357) baseStart_6580357 baseEnd_6580357 := by
    simpa [prefixWord, tailWord_6580357, baseEnd_6580357] using wordTrace_append hprefix tailTrace_6580357
  have hstable : (prefixWord ++ tailWord_6580357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580357).length < 2 ^ (prefixWord ++ tailWord_6580357).sum := by decide
  have hdescent : baseEnd_6580357 < baseStart_6580357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580414 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_6580414 : Nat := 118140960795 + 6580414 * 2 ^ 59
def prefixEnd_6580414 : Nat := 4983230072969 + 3 ^ 40 * 6580414 * 2
def baseEnd_6580414 : Nat := 375435031952813592629137

theorem tailTrace_6580414 : CollatzResearch.WordTrace tailWord_6580414 prefixEnd_6580414 375435031952813592629137 := by
  unfold tailWord_6580414
  simp only [CollatzResearch.WordTrace]
  refine ⟨30000926997786424760302537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160004943988194265388280197 30000926997786424760302537)
  ·
    refine ⟨22500695248339818570226903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30000926997786424760302537 22500695248339818570226903)
    ·
      refine ⟨33751042872509727855340355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22500695248339818570226903 33751042872509727855340355)
      ·
        refine ⟨50626564308764591783010533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33751042872509727855340355 50626564308764591783010533)
        ·
          refine ⟨9492480807893360959314475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50626564308764591783010533 9492480807893360959314475)
          ·
            refine ⟨14238721211840041438971713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492480807893360959314475 14238721211840041438971713)
            ·
              refine ⟨10679040908880031079228785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14238721211840041438971713 10679040908880031079228785)
              ·
                refine ⟨8009280681660023309421589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679040908880031079228785 8009280681660023309421589)
                ·
                  refine ⟨375435031952813592629137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8009280681660023309421589 375435031952813592629137)
                  ·
                    rfl

theorem cell23_6580414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_6580414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580414 prefixEnd_6580414 := by exact prefixLift 6580414
  have htrace : WordTrace (prefixWord ++ tailWord_6580414) baseStart_6580414 baseEnd_6580414 := by
    simpa [prefixWord, tailWord_6580414, baseEnd_6580414] using wordTrace_append hprefix tailTrace_6580414
  have hstable : (prefixWord ++ tailWord_6580414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580414).length < 2 ^ (prefixWord ++ tailWord_6580414).sum := by decide
  have hdescent : baseEnd_6580414 < baseStart_6580414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_6580447 : Nat := 118140960795 + 6580447 * 2 ^ 59
def prefixEnd_6580447 : Nat := 4983230072969 + 3 ^ 40 * 6580447 * 2
def baseEnd_6580447 : Nat := 3378932232436920704549581

theorem tailTrace_6580447 : CollatzResearch.WordTrace tailWord_6580447 prefixEnd_6580447 3378932232436920704549581 := by
  unfold tailWord_6580447
  simp only [CollatzResearch.WordTrace]
  refine ⟨240008619591171844718371595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160005746394114563145581063 240008619591171844718371595)
  ·
    refine ⟨360012929386757767077557393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240008619591171844718371595 360012929386757767077557393)
    ·
      refine ⟨270009697040068325308168045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360012929386757767077557393 270009697040068325308168045)
      ·
        refine ⟨101253636390025621990563017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270009697040068325308168045 101253636390025621990563017)
        ·
          refine ⟨75940227292519216492922263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101253636390025621990563017 75940227292519216492922263)
          ·
            refine ⟨113910340938778824739383395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75940227292519216492922263 113910340938778824739383395)
            ·
              refine ⟨170865511408168237109075093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113910340938778824739383395 170865511408168237109075093)
              ·
                refine ⟨8009320847257886114487895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170865511408168237109075093 8009320847257886114487895)
                ·
                  refine ⟨12013981270886829171731843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009320847257886114487895 12013981270886829171731843)
                  ·
                    refine ⟨18020971906330243757597765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12013981270886829171731843 18020971906330243757597765)
                    ·
                      refine ⟨3378932232436920704549581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18020971906330243757597765 3378932232436920704549581)
                      ·
                        rfl

theorem cell23_6580447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_6580447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580447 prefixEnd_6580447 := by exact prefixLift 6580447
  have htrace : WordTrace (prefixWord ++ tailWord_6580447) baseStart_6580447 baseEnd_6580447 := by
    simpa [prefixWord, tailWord_6580447, baseEnd_6580447] using wordTrace_append hprefix tailTrace_6580447
  have hstable : (prefixWord ++ tailWord_6580447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580447).length < 2 ^ (prefixWord ++ tailWord_6580447).sum := by decide
  have hdescent : baseEnd_6580447 < baseStart_6580447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580451 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6580451 : Nat := 118140960795 + 6580451 * 2 ^ 59
def prefixEnd_6580451 : Nat := 4983230072969 + 3 ^ 40 * 6580451 * 2
def baseEnd_6580451 : Nat := 3378934286359538688899563

theorem tailTrace_6580451 : CollatzResearch.WordTrace tailWord_6580451 prefixEnd_6580451 3378934286359538688899563 := by
  unfold tailWord_6580451
  simp only [CollatzResearch.WordTrace]
  refine ⟨240008765483157353401517207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160005843655438235601011471 240008765483157353401517207)
  ·
    refine ⟨360013148224736030102275811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240008765483157353401517207 360013148224736030102275811)
    ·
      refine ⟨540019722337104045153413717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360013148224736030102275811 540019722337104045153413717)
      ·
        refine ⟨6328356121137938029141567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 540019722337104045153413717 6328356121137938029141567)
        ·
          refine ⟨9492534181706907043712351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328356121137938029141567 9492534181706907043712351)
          ·
            refine ⟨14238801272560360565568527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492534181706907043712351 14238801272560360565568527)
            ·
              refine ⟨21358201908840540848352791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238801272560360565568527 21358201908840540848352791)
              ·
                refine ⟨32037302863260811272529187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21358201908840540848352791 32037302863260811272529187)
                ·
                  refine ⟨48055954294891216908793781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32037302863260811272529187 48055954294891216908793781)
                  ·
                    refine ⟨4505245715146051585199417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48055954294891216908793781 4505245715146051585199417)
                    ·
                      refine ⟨3378934286359538688899563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505245715146051585199417 3378934286359538688899563)
                      ·
                        rfl

theorem cell23_6580451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6580451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580451 prefixEnd_6580451 := by exact prefixLift 6580451
  have htrace : WordTrace (prefixWord ++ tailWord_6580451) baseStart_6580451 baseEnd_6580451 := by
    simpa [prefixWord, tailWord_6580451, baseEnd_6580451] using wordTrace_append hprefix tailTrace_6580451
  have hstable : (prefixWord ++ tailWord_6580451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580451).length < 2 ^ (prefixWord ++ tailWord_6580451).sum := by decide
  have hdescent : baseEnd_6580451 < baseStart_6580451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580474 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_6580474 : Nat := 118140960795 + 6580474 * 2 ^ 59
def prefixEnd_6580474 : Nat := 4983230072969 + 3 ^ 40 * 6580474 * 2
def baseEnd_6580474 : Nat := 1126315365471530699637319

theorem tailTrace_6580474 : CollatzResearch.WordTrace tailWord_6580474 prefixEnd_6580474 1126315365471530699637319 := by
  unfold tailWord_6580474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60002401090518507082401119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160006402908049352219736317 60002401090518507082401119)
  ·
    refine ⟨90003601635777760623601679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60002401090518507082401119 90003601635777760623601679)
    ·
      refine ⟨135005402453666640935402519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90003601635777760623601679 135005402453666640935402519)
      ·
        refine ⟨202508103680499961403103779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135005402453666640935402519 202508103680499961403103779)
        ·
          refine ⟨303762155520749942104655669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202508103680499961403103779 303762155520749942104655669)
          ·
            refine ⟨28477702080070307072311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303762155520749942104655669 28477702080070307072311469)
            ·
              refine ⟨10679138280026365152116801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28477702080070307072311469 10679138280026365152116801)
              ·
                refine ⟨8009353710019773864087601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679138280026365152116801 8009353710019773864087601)
                ·
                  refine ⟨6007015282514830398065701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009353710019773864087601 6007015282514830398065701)
                  ·
                    refine ⟨1126315365471530699637319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007015282514830398065701 1126315365471530699637319)
                    ·
                      rfl

theorem cell23_6580474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_6580474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580474 prefixEnd_6580474 := by exact prefixLift 6580474
  have htrace : WordTrace (prefixWord ++ tailWord_6580474) baseStart_6580474 baseEnd_6580474 := by
    simpa [prefixWord, tailWord_6580474, baseEnd_6580474] using wordTrace_append hprefix tailTrace_6580474
  have hstable : (prefixWord ++ tailWord_6580474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580474).length < 2 ^ (prefixWord ++ tailWord_6580474).sum := by decide
  have hdescent : baseEnd_6580474 < baseStart_6580474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580481 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_6580481 : Nat := 118140960795 + 6580481 * 2 ^ 59
def prefixEnd_6580481 : Nat := 4983230072969 + 3 ^ 40 * 6580481 * 2
def baseEnd_6580481 : Nat := 3378949690779173571524425

theorem tailTrace_6580481 : CollatzResearch.WordTrace tailWord_6580481 prefixEnd_6580481 3378949690779173571524425 := by
  unfold tailWord_6580481
  simp only [CollatzResearch.WordTrace]
  refine ⟨240009859673048668525109297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160006573115365779016739531 240009859673048668525109297)
  ·
    refine ⟨180007394754786501393831973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240009859673048668525109297 180007394754786501393831973)
    ·
      refine ⟨33751386516522469011343495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180007394754786501393831973 33751386516522469011343495)
      ·
        refine ⟨50627079774783703517015243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33751386516522469011343495 50627079774783703517015243)
        ·
          refine ⟨75940619662175555275522865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50627079774783703517015243 75940619662175555275522865)
          ·
            refine ⟨56955464746631666456642149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75940619662175555275522865 56955464746631666456642149)
            ·
              refine ⟨10679149639993437460620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56955464746631666456642149 10679149639993437460620403)
              ·
                refine ⟨16018724459990156190930605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10679149639993437460620403 16018724459990156190930605)
                ·
                  refine ⟨6007021672496308571598977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16018724459990156190930605 6007021672496308571598977)
                  ·
                    refine ⟨4505266254372231428699233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007021672496308571598977 4505266254372231428699233)
                    ·
                      refine ⟨3378949690779173571524425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505266254372231428699233 3378949690779173571524425)
                      ·
                        rfl

theorem cell23_6580481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_6580481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580481 prefixEnd_6580481 := by exact prefixLift 6580481
  have htrace : WordTrace (prefixWord ++ tailWord_6580481) baseStart_6580481 baseEnd_6580481 := by
    simpa [prefixWord, tailWord_6580481, baseEnd_6580481] using wordTrace_append hprefix tailTrace_6580481
  have hstable : (prefixWord ++ tailWord_6580481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580481).length < 2 ^ (prefixWord ++ tailWord_6580481).sum := by decide
  have hdescent : baseEnd_6580481 < baseStart_6580481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580484 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6580484 : Nat := 118140960795 + 6580484 * 2 ^ 59
def prefixEnd_6580484 : Nat := 4983230072969 + 3 ^ 40 * 6580484 * 2
def baseEnd_6580484 : Nat := 3378951231221137059786911

theorem tailTrace_6580484 : CollatzResearch.WordTrace tailWord_6580484 prefixEnd_6580484 3378951231221137059786911 := by
  unfold tailWord_6580484
  simp only [CollatzResearch.WordTrace]
  refine ⟨120004984546018900018734253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160006646061358533358312337 120004984546018900018734253)
  ·
    refine ⟨45001869204757087507025345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120004984546018900018734253 45001869204757087507025345)
    ·
      refine ⟨33751401903567815630269009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45001869204757087507025345 33751401903567815630269009)
      ·
        refine ⟨25313551427675861722701757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33751401903567815630269009 25313551427675861722701757)
        ·
          refine ⟨9492581785378448146013159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25313551427675861722701757 9492581785378448146013159)
          ·
            refine ⟨14238872678067672219019739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492581785378448146013159 14238872678067672219019739)
            ·
              refine ⟨21358309017101508328529609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238872678067672219019739 21358309017101508328529609)
              ·
                refine ⟨16018731762826131246397207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21358309017101508328529609 16018731762826131246397207)
                ·
                  refine ⟨24028097644239196869595811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16018731762826131246397207 24028097644239196869595811)
                  ·
                    refine ⟨36042146466358795304393717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24028097644239196869595811 36042146466358795304393717)
                    ·
                      refine ⟨3378951231221137059786911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36042146466358795304393717 3378951231221137059786911)
                      ·
                        rfl

theorem cell23_6580484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6580484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580484 prefixEnd_6580484 := by exact prefixLift 6580484
  have htrace : WordTrace (prefixWord ++ tailWord_6580484) baseStart_6580484 baseEnd_6580484 := by
    simpa [prefixWord, tailWord_6580484, baseEnd_6580484] using wordTrace_append hprefix tailTrace_6580484
  have hstable : (prefixWord ++ tailWord_6580484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580484).length < 2 ^ (prefixWord ++ tailWord_6580484).sum := by decide
  have hdescent : baseEnd_6580484 < baseStart_6580484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580532 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6580532 : Nat := 118140960795 + 6580532 * 2 ^ 59
def prefixEnd_6580532 : Nat := 4983230072969 + 3 ^ 40 * 6580532 * 2
def baseEnd_6580532 : Nat := 3378975878292552871986691

theorem tailTrace_6580532 : CollatzResearch.WordTrace tailWord_6580532 prefixEnd_6580532 3378975878292552871986691 := by
  unfold tailWord_6580532
  simp only [CollatzResearch.WordTrace]
  refine ⟨120005859897931952117607925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160007813197242602823477233 120005859897931952117607925)
  ·
    refine ⟨11250549365431120511025743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120005859897931952117607925 11250549365431120511025743)
    ·
      refine ⟨16875824048146680766538615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250549365431120511025743 16875824048146680766538615)
      ·
        refine ⟨25313736072220021149807923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16875824048146680766538615 25313736072220021149807923)
        ·
          refine ⟨37970604108330031724711885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25313736072220021149807923 37970604108330031724711885)
          ·
            refine ⟨14238976540623761896766957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37970604108330031724711885 14238976540623761896766957)
            ·
              refine ⟨5339616202733910711287609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14238976540623761896766957 5339616202733910711287609)
              ·
                refine ⟨4004712152050433033465707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339616202733910711287609 4004712152050433033465707)
                ·
                  refine ⟨6007068228075649550198561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004712152050433033465707 6007068228075649550198561)
                  ·
                    refine ⟨4505301171056737162648921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007068228075649550198561 4505301171056737162648921)
                    ·
                      refine ⟨3378975878292552871986691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505301171056737162648921 3378975878292552871986691)
                      ·
                        rfl

theorem cell23_6580532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6580532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580532 prefixEnd_6580532 := by exact prefixLift 6580532
  have htrace : WordTrace (prefixWord ++ tailWord_6580532) baseStart_6580532 baseEnd_6580532 := by
    simpa [prefixWord, tailWord_6580532, baseEnd_6580532] using wordTrace_append hprefix tailTrace_6580532
  have hstable : (prefixWord ++ tailWord_6580532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580532).length < 2 ^ (prefixWord ++ tailWord_6580532).sum := by decide
  have hdescent : baseEnd_6580532 < baseStart_6580532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580587 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3]
def baseStart_6580587 : Nat := 118140960795 + 6580587 * 2 ^ 59
def prefixEnd_6580587 : Nat := 4983230072969 + 3 ^ 40 * 6580587 * 2
def baseEnd_6580587 : Nat := 3379004119728550156798937

theorem tailTrace_6580587 : CollatzResearch.WordTrace tailWord_6580587 prefixEnd_6580587 3379004119728550156798937 := by
  unfold tailWord_6580587
  simp only [CollatzResearch.WordTrace]
  refine ⟨240013725810664648628468015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160009150540443099085645343 240013725810664648628468015)
  ·
    refine ⟨360020588715996972942702023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240013725810664648628468015 360020588715996972942702023)
    ·
      refine ⟨540030883073995459414053035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360020588715996972942702023 540030883073995459414053035)
      ·
        refine ⟨810046324610993189121079553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540030883073995459414053035 810046324610993189121079553)
        ·
          refine ⟨607534743458244891840809665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810046324610993189121079553 607534743458244891840809665)
          ·
            refine ⟨455651057593683668880607249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607534743458244891840809665 455651057593683668880607249)
            ·
              refine ⟨341738293195262751660455437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455651057593683668880607249 341738293195262751660455437)
              ·
                refine ⟨128151859948223531872670789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341738293195262751660455437 128151859948223531872670789)
                ·
                  refine ⟨24028473740291912226125773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128151859948223531872670789 24028473740291912226125773)
                  ·
                    refine ⟨9010677652609467084797165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24028473740291912226125773 9010677652609467084797165)
                    ·
                      refine ⟨3379004119728550156798937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010677652609467084797165 3379004119728550156798937)
                      ·
                        rfl

theorem cell23_6580587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].length) (baseStart_6580587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580587 prefixEnd_6580587 := by exact prefixLift 6580587
  have htrace : WordTrace (prefixWord ++ tailWord_6580587) baseStart_6580587 baseEnd_6580587 := by
    simpa [prefixWord, tailWord_6580587, baseEnd_6580587] using wordTrace_append hprefix tailTrace_6580587
  have hstable : (prefixWord ++ tailWord_6580587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580587).length < 2 ^ (prefixWord ++ tailWord_6580587).sum := by decide
  have hdescent : baseEnd_6580587 < baseStart_6580587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580628 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 5]
def baseStart_6580628 : Nat := 118140960795 + 6580628 * 2 ^ 59
def prefixEnd_6580628 : Nat := 4983230072969 + 3 ^ 40 * 6580628 * 2
def baseEnd_6580628 : Nat := 375447241381709388487361

theorem tailTrace_6580628 : CollatzResearch.WordTrace tailWord_6580628 prefixEnd_6580628 375447241381709388487361 := by
  unfold tailWord_6580628
  simp only [CollatzResearch.WordTrace]
  refine ⟨120007610601758056315355269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160010147469010741753807025 120007610601758056315355269)
  ·
    refine ⟨22501426987829635559129113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120007610601758056315355269 22501426987829635559129113)
    ·
      refine ⟨16876070240872226669346835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22501426987829635559129113 16876070240872226669346835)
      ·
        refine ⟨25314105361308340004020253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876070240872226669346835 25314105361308340004020253)
        ·
          refine ⟨9492789510490627501507595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25314105361308340004020253 9492789510490627501507595)
          ·
            refine ⟨14239184265735941252261393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492789510490627501507595 14239184265735941252261393)
            ·
              refine ⟨10679388199301955939196045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14239184265735941252261393 10679388199301955939196045)
              ·
                refine ⟨4004770574738233477198517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10679388199301955939196045 4004770574738233477198517)
                ·
                  refine ⟨375447241381709388487361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004770574738233477198517 375447241381709388487361)
                  ·
                    rfl

theorem cell23_6580628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_6580628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580628 prefixEnd_6580628 := by exact prefixLift 6580628
  have htrace : WordTrace (prefixWord ++ tailWord_6580628) baseStart_6580628 baseEnd_6580628 := by
    simpa [prefixWord, tailWord_6580628, baseEnd_6580628] using wordTrace_append hprefix tailTrace_6580628
  have hstable : (prefixWord ++ tailWord_6580628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580628).length < 2 ^ (prefixWord ++ tailWord_6580628).sum := by decide
  have hdescent : baseEnd_6580628 < baseStart_6580628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580644 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_6580644 : Nat := 118140960795 + 6580644 * 2 ^ 59
def prefixEnd_6580644 : Nat := 4983230072969 + 3 ^ 40 * 6580644 * 2
def baseEnd_6580644 : Nat := 3379033388125856433786175

theorem tailTrace_6580644 : CollatzResearch.WordTrace tailWord_6580644 prefixEnd_6580644 3379033388125856433786175 := by
  unfold tailWord_6580644
  simp only [CollatzResearch.WordTrace]
  refine ⟨120007902385729073681646493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160010536514305431575528657 120007902385729073681646493)
  ·
    refine ⟨45002963394648402630617435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120007902385729073681646493 45002963394648402630617435)
    ·
      refine ⟨67504445091972603945926153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45002963394648402630617435 67504445091972603945926153)
      ·
        refine ⟨50628333818979452959444615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67504445091972603945926153 50628333818979452959444615)
        ·
          refine ⟨75942500728469179439166923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50628333818979452959444615 75942500728469179439166923)
          ·
            refine ⟨113913751092703769158750385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75942500728469179439166923 113913751092703769158750385)
            ·
              refine ⟨85435313319527826869062789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113913751092703769158750385 85435313319527826869062789)
              ·
                refine ⟨16019121247411467537949273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85435313319527826869062789 16019121247411467537949273)
                ·
                  refine ⟨12014340935558600653461955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16019121247411467537949273 12014340935558600653461955)
                  ·
                    refine ⟨18021511403337900980192933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12014340935558600653461955 18021511403337900980192933)
                    ·
                      refine ⟨3379033388125856433786175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18021511403337900980192933 3379033388125856433786175)
                      ·
                        rfl

theorem cell23_6580644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_6580644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580644 prefixEnd_6580644 := by exact prefixLift 6580644
  have htrace : WordTrace (prefixWord ++ tailWord_6580644) baseStart_6580644 baseEnd_6580644 := by
    simpa [prefixWord, tailWord_6580644, baseEnd_6580644] using wordTrace_append hprefix tailTrace_6580644
  have hstable : (prefixWord ++ tailWord_6580644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580644).length < 2 ^ (prefixWord ++ tailWord_6580644).sum := by decide
  have hdescent : baseEnd_6580644 < baseStart_6580644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580718 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_6580718 : Nat := 118140960795 + 6580718 * 2 ^ 59
def prefixEnd_6580718 : Nat := 4983230072969 + 3 ^ 40 * 6580718 * 2
def baseEnd_6580718 : Nat := 375452376188254349362315

theorem tailTrace_6580718 : CollatzResearch.WordTrace tailWord_6580718 prefixEnd_6580718 375452376188254349362315 := by
  unfold tailWord_6580718
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002312971648757250185851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160012335848793372000991205 30002312971648757250185851)
  ·
    refine ⟨45003469457473135875278777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30002312971648757250185851 45003469457473135875278777)
    ·
      refine ⟨33752602093104851906459083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45003469457473135875278777 33752602093104851906459083)
      ·
        refine ⟨50628903139657277859688625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33752602093104851906459083 50628903139657277859688625)
        ·
          refine ⟨37971677354742958394766469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50628903139657277859688625 37971677354742958394766469)
          ·
            refine ⟨7119689504014304699018713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37971677354742958394766469 7119689504014304699018713)
            ·
              refine ⟨5339767128010728524264035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119689504014304699018713 5339767128010728524264035)
              ·
                refine ⟨8009650692016092786396053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339767128010728524264035 8009650692016092786396053)
                ·
                  refine ⟨375452376188254349362315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8009650692016092786396053 375452376188254349362315)
                  ·
                    rfl

theorem cell23_6580718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_6580718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580718 prefixEnd_6580718 := by exact prefixLift 6580718
  have htrace : WordTrace (prefixWord ++ tailWord_6580718) baseStart_6580718 baseEnd_6580718 := by
    simpa [prefixWord, tailWord_6580718, baseEnd_6580718] using wordTrace_append hprefix tailTrace_6580718
  have hstable : (prefixWord ++ tailWord_6580718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580718).length < 2 ^ (prefixWord ++ tailWord_6580718).sum := by decide
  have hdescent : baseEnd_6580718 < baseStart_6580718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580721 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_6580721 : Nat := 118140960795 + 6580721 * 2 ^ 59
def prefixEnd_6580721 : Nat := 4983230072969 + 3 ^ 40 * 6580721 * 2
def baseEnd_6580721 : Nat := 3379072926136252632523321

theorem tailTrace_6580721 : CollatzResearch.WordTrace tailWord_6580721 prefixEnd_6580721 3379072926136252632523321 := by
  unfold tailWord_6580721
  simp only [CollatzResearch.WordTrace]
  refine ⟨240018613192179189513846017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160012408794786126342564011 240018613192179189513846017)
  ·
    refine ⟨180013959894134392135384513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240018613192179189513846017 180013959894134392135384513)
    ·
      refine ⟨135010469920600794101538385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180013959894134392135384513 135010469920600794101538385)
      ·
        refine ⟨101257852440450595576153789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135010469920600794101538385 101257852440450595576153789)
        ·
          refine ⟨37971694665168973341057671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101257852440450595576153789 37971694665168973341057671)
          ·
            refine ⟨56957541997753460011586507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37971694665168973341057671 56957541997753460011586507)
            ·
              refine ⟨85436312996630190017379761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56957541997753460011586507 85436312996630190017379761)
              ·
                refine ⟨64077234747472642513034821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85436312996630190017379761 64077234747472642513034821)
                ·
                  refine ⟨12014481515151120471194029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64077234747472642513034821 12014481515151120471194029)
                  ·
                    refine ⟨4505430568181670176697761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12014481515151120471194029 4505430568181670176697761)
                    ·
                      refine ⟨3379072926136252632523321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505430568181670176697761 3379072926136252632523321)
                      ·
                        rfl

theorem cell23_6580721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_6580721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580721 prefixEnd_6580721 := by exact prefixLift 6580721
  have htrace : WordTrace (prefixWord ++ tailWord_6580721) baseStart_6580721 baseEnd_6580721 := by
    simpa [prefixWord, tailWord_6580721, baseEnd_6580721] using wordTrace_append hprefix tailTrace_6580721
  have hstable : (prefixWord ++ tailWord_6580721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580721).length < 2 ^ (prefixWord ++ tailWord_6580721).sum := by decide
  have hdescent : baseEnd_6580721 < baseStart_6580721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580748 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_6580748 : Nat := 118140960795 + 6580748 * 2 ^ 59
def prefixEnd_6580748 : Nat := 4983230072969 + 3 ^ 40 * 6580748 * 2
def baseEnd_6580748 : Nat := 1126362263371308008961899

theorem tailTrace_6580748 : CollatzResearch.WordTrace tailWord_6580748 prefixEnd_6580748 1126362263371308008961899 := by
  unfold tailWord_6580748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120009798981540686562539449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160013065308720915416719265 120009798981540686562539449)
  ·
    refine ⟨90007349236155514921904587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120009798981540686562539449 90007349236155514921904587)
    ·
      refine ⟨135011023854233272382856881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90007349236155514921904587 135011023854233272382856881)
      ·
        refine ⟨101258267890674954287142661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135011023854233272382856881 101258267890674954287142661)
        ·
          refine ⟨18985925229501553928839249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101258267890674954287142661 18985925229501553928839249)
          ·
            refine ⟨14239443922126165446629437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18985925229501553928839249 14239443922126165446629437)
            ·
              refine ⟨5339791470797312042486039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14239443922126165446629437 5339791470797312042486039)
              ·
                refine ⟨8009687206195968063729059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339791470797312042486039 8009687206195968063729059)
                ·
                  refine ⟨12014530809293952095593589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009687206195968063729059 12014530809293952095593589)
                  ·
                    refine ⟨1126362263371308008961899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12014530809293952095593589 1126362263371308008961899)
                    ·
                      rfl

theorem cell23_6580748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_6580748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580748 prefixEnd_6580748 := by exact prefixLift 6580748
  have htrace : WordTrace (prefixWord ++ tailWord_6580748) baseStart_6580748 baseEnd_6580748 := by
    simpa [prefixWord, tailWord_6580748, baseEnd_6580748] using wordTrace_append hprefix tailTrace_6580748
  have hstable : (prefixWord ++ tailWord_6580748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580748).length < 2 ^ (prefixWord ++ tailWord_6580748).sum := by decide
  have hdescent : baseEnd_6580748 < baseStart_6580748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580771 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3]
def baseStart_6580771 : Nat := 118140960795 + 6580771 * 2 ^ 59
def prefixEnd_6580771 : Nat := 4983230072969 + 3 ^ 40 * 6580771 * 2
def baseEnd_6580771 : Nat := 3379098600168977436898091

theorem tailTrace_6580771 : CollatzResearch.WordTrace tailWord_6580771 prefixEnd_6580771 3379098600168977436898091 := by
  unfold tailWord_6580771
  simp only [CollatzResearch.WordTrace]
  refine ⟨240020436841998048053166167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160013624561332032035444111 240020436841998048053166167)
  ·
    refine ⟨360030655262997072079749251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240020436841998048053166167 360030655262997072079749251)
    ·
      refine ⟨540045982894495608119623877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360030655262997072079749251 540045982894495608119623877)
      ·
        refine ⟨101258621792717926522429477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 540045982894495608119623877 101258621792717926522429477)
        ·
          refine ⟨18985991586134611222955527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101258621792717926522429477 18985991586134611222955527)
          ·
            refine ⟨28478987379201916834433291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18985991586134611222955527 28478987379201916834433291)
            ·
              refine ⟨42718481068802875251649937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28478987379201916834433291 42718481068802875251649937)
              ·
                refine ⟨32038860801602156438737453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42718481068802875251649937 32038860801602156438737453)
                ·
                  refine ⟨12014572800600808664526545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32038860801602156438737453 12014572800600808664526545)
                  ·
                    refine ⟨9010929600450606498394909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12014572800600808664526545 9010929600450606498394909)
                    ·
                      refine ⟨3379098600168977436898091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010929600450606498394909 3379098600168977436898091)
                      ·
                        rfl

theorem cell23_6580771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_6580771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580771 prefixEnd_6580771 := by exact prefixLift 6580771
  have htrace : WordTrace (prefixWord ++ tailWord_6580771) baseStart_6580771 baseEnd_6580771 := by
    simpa [prefixWord, tailWord_6580771, baseEnd_6580771] using wordTrace_append hprefix tailTrace_6580771
  have hstable : (prefixWord ++ tailWord_6580771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580771).length < 2 ^ (prefixWord ++ tailWord_6580771).sum := by decide
  have hdescent : baseEnd_6580771 < baseStart_6580771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580778 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_6580778 : Nat := 118140960795 + 6580778 * 2 ^ 59
def prefixEnd_6580778 : Nat := 4983230072969 + 3 ^ 40 * 6580778 * 2
def baseEnd_6580778 : Nat := 1126367398177852969836853

theorem tailTrace_6580778 : CollatzResearch.WordTrace tailWord_6580778 prefixEnd_6580778 1126367398177852969836853 := by
  unfold tailWord_6580778
  simp only [CollatzResearch.WordTrace]
  refine ⟨60005173038243172062167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160013794768648458832447325 60005173038243172062167747)
  ·
    refine ⟨90007759557364758093251621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60005173038243172062167747 90007759557364758093251621)
    ·
      refine ⟨16876454917005892142484679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90007759557364758093251621 16876454917005892142484679)
      ·
        refine ⟨25314682375508838213727019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876454917005892142484679 25314682375508838213727019)
        ·
          refine ⟨37972023563263257320590529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25314682375508838213727019 37972023563263257320590529)
          ·
            refine ⟨28479017672447442990442897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37972023563263257320590529 28479017672447442990442897)
            ·
              refine ⟨21359263254335582242832173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28479017672447442990442897 21359263254335582242832173)
              ·
                refine ⟨8009723720375843341062065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21359263254335582242832173 8009723720375843341062065)
                ·
                  refine ⟨6007292790281882505796549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009723720375843341062065 6007292790281882505796549)
                  ·
                    refine ⟨1126367398177852969836853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007292790281882505796549 1126367398177852969836853)
                    ·
                      rfl

theorem cell23_6580778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_6580778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580778 prefixEnd_6580778 := by exact prefixLift 6580778
  have htrace : WordTrace (prefixWord ++ tailWord_6580778) baseStart_6580778 baseEnd_6580778 := by
    simpa [prefixWord, tailWord_6580778, baseEnd_6580778] using wordTrace_append hprefix tailTrace_6580778
  have hstable : (prefixWord ++ tailWord_6580778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580778).length < 2 ^ (prefixWord ++ tailWord_6580778).sum := by decide
  have hdescent : baseEnd_6580778 < baseStart_6580778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580805 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_6580805 : Nat := 118140960795 + 6580805 * 2 ^ 59
def prefixEnd_6580805 : Nat := 4983230072969 + 3 ^ 40 * 6580805 * 2
def baseEnd_6580805 : Nat := 3379116058511230303872935

theorem tailTrace_6580805 : CollatzResearch.WordTrace tailWord_6580805 prefixEnd_6580805 3379116058511230303872935 := by
  unfold tailWord_6580805
  simp only [CollatzResearch.WordTrace]
  refine ⟨240021676923874871859903869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160014451282583247906602579 240021676923874871859903869)
  ·
    refine ⟨90008128846453076947463951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240021676923874871859903869 90008128846453076947463951)
    ·
      refine ⟨135012193269679615421195927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90008128846453076947463951 135012193269679615421195927)
      ·
        refine ⟨202518289904519423131793891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135012193269679615421195927 202518289904519423131793891)
        ·
          refine ⟨303777434856779134697690837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202518289904519423131793891 303777434856779134697690837)
          ·
            refine ⟨7119783629455760969477129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 303777434856779134697690837 7119783629455760969477129)
            ·
              refine ⟨5339837722091820727107847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119783629455760969477129 5339837722091820727107847)
              ·
                refine ⟨8009756583137731090661771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339837722091820727107847 8009756583137731090661771)
                ·
                  refine ⟨12014634874706596635992657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009756583137731090661771 12014634874706596635992657)
                  ·
                    refine ⟨9010976156029947476994493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12014634874706596635992657 9010976156029947476994493)
                    ·
                      refine ⟨3379116058511230303872935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010976156029947476994493 3379116058511230303872935)
                      ·
                        rfl

theorem cell23_6580805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_6580805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580805 prefixEnd_6580805 := by exact prefixLift 6580805
  have htrace : WordTrace (prefixWord ++ tailWord_6580805) baseStart_6580805 baseEnd_6580805 := by
    simpa [prefixWord, tailWord_6580805, baseEnd_6580805] using wordTrace_append hprefix tailTrace_6580805
  have hstable : (prefixWord ++ tailWord_6580805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580805).length < 2 ^ (prefixWord ++ tailWord_6580805).sum := by decide
  have hdescent : baseEnd_6580805 < baseStart_6580805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580818 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_6580818 : Nat := 118140960795 + 6580818 * 2 ^ 59
def prefixEnd_6580818 : Nat := 4983230072969 + 3 ^ 40 * 6580818 * 2
def baseEnd_6580818 : Nat := 3379122733759738753010375

theorem tailTrace_6580818 : CollatzResearch.WordTrace tailWord_6580818 prefixEnd_6580818 3379122733759738753010375 := by
  unfold tailWord_6580818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60005537768206943770031777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160014767381885183386751405 60005537768206943770031777)
  ·
    refine ⟨45004153326155207827523833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60005537768206943770031777 45004153326155207827523833)
    ·
      refine ⟨33753114994616405870642875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45004153326155207827523833 33753114994616405870642875)
      ·
        refine ⟨50629672491924608805964313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33753114994616405870642875 50629672491924608805964313)
        ·
          refine ⟨37972254368943456604473235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50629672491924608805964313 37972254368943456604473235)
          ·
            refine ⟨56958381553415184906709853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37972254368943456604473235 56958381553415184906709853)
            ·
              refine ⟨21359393082530694340016195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56958381553415184906709853 21359393082530694340016195)
              ·
                refine ⟨32039089623796041510024293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21359393082530694340016195 32039089623796041510024293)
                ·
                  refine ⟨6007329304461757783129555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32039089623796041510024293 6007329304461757783129555)
                  ·
                    refine ⟨9010993956692636674694333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007329304461757783129555 9010993956692636674694333)
                    ·
                      refine ⟨3379122733759738753010375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9010993956692636674694333 3379122733759738753010375)
                      ·
                        rfl

theorem cell23_6580818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_6580818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580818 prefixEnd_6580818 := by exact prefixLift 6580818
  have htrace : WordTrace (prefixWord ++ tailWord_6580818) baseStart_6580818 baseEnd_6580818 := by
    simpa [prefixWord, tailWord_6580818, baseEnd_6580818] using wordTrace_append hprefix tailTrace_6580818
  have hstable : (prefixWord ++ tailWord_6580818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580818).length < 2 ^ (prefixWord ++ tailWord_6580818).sum := by decide
  have hdescent : baseEnd_6580818 < baseStart_6580818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580824 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6580824 : Nat := 118140960795 + 6580824 * 2 ^ 59
def prefixEnd_6580824 : Nat := 4983230072969 + 3 ^ 40 * 6580824 * 2
def baseEnd_6580824 : Nat := 3379125814643665729535347

theorem tailTrace_6580824 : CollatzResearch.WordTrace tailWord_6580824 prefixEnd_6580824 3379125814643665729535347 := by
  unfold tailWord_6580824
  simp only [CollatzResearch.WordTrace]
  refine ⟨120011184955403019052422763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160014913273870692069897017 120011184955403019052422763)
  ·
    refine ⟨180016777433104528578634145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120011184955403019052422763 180016777433104528578634145)
    ·
      refine ⟨135012583074828396433975609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180016777433104528578634145 135012583074828396433975609)
      ·
        refine ⟨101259437306121297325481707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135012583074828396433975609 101259437306121297325481707)
        ·
          refine ⟨151889155959181945988222561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101259437306121297325481707 151889155959181945988222561)
          ·
            refine ⟨113916866969386459491166921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151889155959181945988222561 113916866969386459491166921)
            ·
              refine ⟨85437650227039844618375191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113916866969386459491166921 85437650227039844618375191)
              ·
                refine ⟨128156475340559766927562787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85437650227039844618375191 128156475340559766927562787)
                ·
                  refine ⟨192234713010839650391344181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128156475340559766927562787 192234713010839650391344181)
                  ·
                    refine ⟨18022004344766217224188517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 192234713010839650391344181 18022004344766217224188517)
                    ·
                      refine ⟨3379125814643665729535347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18022004344766217224188517 3379125814643665729535347)
                      ·
                        rfl

theorem cell23_6580824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6580824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580824 prefixEnd_6580824 := by exact prefixLift 6580824
  have htrace : WordTrace (prefixWord ++ tailWord_6580824) baseStart_6580824 baseEnd_6580824 := by
    simpa [prefixWord, tailWord_6580824, baseEnd_6580824] using wordTrace_append hprefix tailTrace_6580824
  have hstable : (prefixWord ++ tailWord_6580824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580824).length < 2 ^ (prefixWord ++ tailWord_6580824).sum := by decide
  have hdescent : baseEnd_6580824 < baseStart_6580824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580835 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6580835 : Nat := 118140960795 + 6580835 * 2 ^ 59
def prefixEnd_6580835 : Nat := 4983230072969 + 3 ^ 40 * 6580835 * 2
def baseEnd_6580835 : Nat := 3379131462930865186497797

theorem tailTrace_6580835 : CollatzResearch.WordTrace tailWord_6580835 prefixEnd_6580835 3379131462930865186497797 := by
  unfold tailWord_6580835
  simp only [CollatzResearch.WordTrace]
  refine ⟨240022771113766186983495959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160015180742510791322330639 240022771113766186983495959)
  ·
    refine ⟨360034156670649280475243939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240022771113766186983495959 360034156670649280475243939)
    ·
      refine ⟨540051235005973920712865909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360034156670649280475243939 540051235005973920712865909)
      ·
        refine ⟨50629803281810055066831179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 540051235005973920712865909 50629803281810055066831179)
        ·
          refine ⟨75944704922715082600246769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50629803281810055066831179 75944704922715082600246769)
          ·
            refine ⟨56958528692036311950185077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75944704922715082600246769 56958528692036311950185077)
            ·
              refine ⟨5339862064878404245329851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56958528692036311950185077 5339862064878404245329851)
              ·
                refine ⟨8009793097317606367994777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339862064878404245329851 8009793097317606367994777)
                ·
                  refine ⟨6007344822988204775996083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009793097317606367994777 6007344822988204775996083)
                  ·
                    refine ⟨9011017234482307163994125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6007344822988204775996083 9011017234482307163994125)
                    ·
                      refine ⟨3379131462930865186497797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9011017234482307163994125 3379131462930865186497797)
                      ·
                        rfl

theorem cell23_6580835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6580835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580835 prefixEnd_6580835 := by exact prefixLift 6580835
  have htrace : WordTrace (prefixWord ++ tailWord_6580835) baseStart_6580835 baseEnd_6580835 := by
    simpa [prefixWord, tailWord_6580835, baseEnd_6580835] using wordTrace_append hprefix tailTrace_6580835
  have hstable : (prefixWord ++ tailWord_6580835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580835).length < 2 ^ (prefixWord ++ tailWord_6580835).sum := by decide
  have hdescent : baseEnd_6580835 < baseStart_6580835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580845 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6580845 : Nat := 118140960795 + 6580845 * 2 ^ 59
def prefixEnd_6580845 : Nat := 4983230072969 + 3 ^ 40 * 6580845 * 2
def baseEnd_6580845 : Nat := 3379136597737410147372751

theorem tailTrace_6580845 : CollatzResearch.WordTrace tailWord_6580845 prefixEnd_6580845 3379136597737410147372751 := by
  unfold tailWord_6580845
  simp only [CollatzResearch.WordTrace]
  refine ⟨240023135843729958691359989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160015423895819972460906659 240023135843729958691359989)
  ·
    refine ⟨22502168985349683627314999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240023135843729958691359989 22502168985349683627314999)
    ·
      refine ⟨33753253478024525440972499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22502168985349683627314999 33753253478024525440972499)
      ·
        refine ⟨50629880217036788161458749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33753253478024525440972499 50629880217036788161458749)
        ·
          refine ⟨18986205081388795560547031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50629880217036788161458749 18986205081388795560547031)
          ·
            refine ⟨28479307622083193340820547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18986205081388795560547031 28479307622083193340820547)
            ·
              refine ⟨42718961433124790011230821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28479307622083193340820547 42718961433124790011230821)
              ·
                refine ⟨8009805268710898127105779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42718961433124790011230821 8009805268710898127105779)
                ·
                  refine ⟨12014707903066347190658669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009805268710898127105779 12014707903066347190658669)
                  ·
                    refine ⟨4505515463649880196497001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12014707903066347190658669 4505515463649880196497001)
                    ·
                      refine ⟨3379136597737410147372751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505515463649880196497001 3379136597737410147372751)
                      ·
                        rfl

theorem cell23_6580845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6580845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580845 prefixEnd_6580845 := by exact prefixLift 6580845
  have htrace : WordTrace (prefixWord ++ tailWord_6580845) baseStart_6580845 baseEnd_6580845 := by
    simpa [prefixWord, tailWord_6580845, baseEnd_6580845] using wordTrace_append hprefix tailTrace_6580845
  have hstable : (prefixWord ++ tailWord_6580845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580845).length < 2 ^ (prefixWord ++ tailWord_6580845).sum := by decide
  have hdescent : baseEnd_6580845 < baseStart_6580845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580892 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6580892 : Nat := 118140960795 + 6580892 * 2 ^ 59
def prefixEnd_6580892 : Nat := 4983230072969 + 3 ^ 40 * 6580892 * 2
def baseEnd_6580892 : Nat := 3379160731328171463485035

theorem tailTrace_6580892 : CollatzResearch.WordTrace tailWord_6580892 prefixEnd_6580892 3379160731328171463485035 := by
  unfold tailWord_6580892
  simp only [CollatzResearch.WordTrace]
  refine ⟨120012425037279842859160465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160016566716373123812213953 120012425037279842859160465)
  ·
    refine ⟨90009318777959882144370349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120012425037279842859160465 90009318777959882144370349)
    ·
      refine ⟨33753494541734955804138881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90009318777959882144370349 33753494541734955804138881)
      ·
        refine ⟨25315120906301216853104161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33753494541734955804138881 25315120906301216853104161)
        ·
          refine ⟨18986340679725912639828121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25315120906301216853104161 18986340679725912639828121)
          ·
            refine ⟨14239755509794434479871091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18986340679725912639828121 14239755509794434479871091)
            ·
              refine ⟨21359633264691651719806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14239755509794434479871091 21359633264691651719806637)
              ·
                refine ⟨8009862474259369394927489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21359633264691651719806637 8009862474259369394927489)
                ·
                  refine ⟨6007396855694527046195617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8009862474259369394927489 6007396855694527046195617)
                  ·
                    refine ⟨4505547641770895284646713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007396855694527046195617 4505547641770895284646713)
                    ·
                      refine ⟨3379160731328171463485035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505547641770895284646713 3379160731328171463485035)
                      ·
                        rfl

theorem cell23_6580892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6580892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580892 prefixEnd_6580892 := by exact prefixLift 6580892
  have htrace : WordTrace (prefixWord ++ tailWord_6580892) baseStart_6580892 baseEnd_6580892 := by
    simpa [prefixWord, tailWord_6580892, baseEnd_6580892] using wordTrace_append hprefix tailTrace_6580892
  have hstable : (prefixWord ++ tailWord_6580892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580892).length < 2 ^ (prefixWord ++ tailWord_6580892).sum := by decide
  have hdescent : baseEnd_6580892 < baseStart_6580892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580911 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 2, 5]
def baseStart_6580911 : Nat := 118140960795 + 6580911 * 2 ^ 59
def prefixEnd_6580911 : Nat := 4983230072969 + 3 ^ 40 * 6580911 * 2
def baseEnd_6580911 : Nat := 1126390162486868963049149

theorem tailTrace_6580911 : CollatzResearch.WordTrace tailWord_6580911 prefixEnd_6580911 1126390162486868963049149 := by
  unfold tailWord_6580911
  simp only [CollatzResearch.WordTrace]
  refine ⟨240025543061490851963262587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160017028707660567975508391 240025543061490851963262587)
  ·
    refine ⟨360038314592236277944893881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240025543061490851963262587 360038314592236277944893881)
    ·
      refine ⟨270028735944177208458670411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360038314592236277944893881 270028735944177208458670411)
      ·
        refine ⟨405043103916265812688005617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270028735944177208458670411 405043103916265812688005617)
        ·
          refine ⟨303782327937199359516004213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405043103916265812688005617 303782327937199359516004213)
          ·
            refine ⟨28479593244112439954625395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303782327937199359516004213 28479593244112439954625395)
            ·
              refine ⟨42719389866168659931938093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28479593244112439954625395 42719389866168659931938093)
              ·
                refine ⟨16019771199813247474476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42719389866168659931938093 16019771199813247474476785)
                ·
                  refine ⟨12014828399859935605857589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16019771199813247474476785 12014828399859935605857589)
                  ·
                    refine ⟨1126390162486868963049149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12014828399859935605857589 1126390162486868963049149)
                    ·
                      rfl

theorem cell23_6580911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_6580911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580911 prefixEnd_6580911 := by exact prefixLift 6580911
  have htrace : WordTrace (prefixWord ++ tailWord_6580911) baseStart_6580911 baseEnd_6580911 := by
    simpa [prefixWord, tailWord_6580911, baseEnd_6580911] using wordTrace_append hprefix tailTrace_6580911
  have hstable : (prefixWord ++ tailWord_6580911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580911).length < 2 ^ (prefixWord ++ tailWord_6580911).sum := by decide
  have hdescent : baseEnd_6580911 < baseStart_6580911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580932 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 5]
def baseStart_6580932 : Nat := 118140960795 + 6580932 * 2 ^ 59
def prefixEnd_6580932 : Nat := 4983230072969 + 3 ^ 40 * 6580932 * 2
def baseEnd_6580932 : Nat := 375464585617150145220539

theorem tailTrace_6580932 : CollatzResearch.WordTrace tailWord_6580932 prefixEnd_6580932 375464585617150145220539 := by
  unfold tailWord_6580932
  simp only [CollatzResearch.WordTrace]
  refine ⟨120013154497207386274888525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160017539329609848366518033 120013154497207386274888525)
  ·
    refine ⟨45004932936452769853083197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120013154497207386274888525 45004932936452769853083197)
    ·
      refine ⟨16876849851169788694906199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45004932936452769853083197 16876849851169788694906199)
      ·
        refine ⟨25315274776754683042359299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876849851169788694906199 25315274776754683042359299)
        ·
          refine ⟨37972912165132024563538949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25315274776754683042359299 37972912165132024563538949)
          ·
            refine ⟨7119921030962254605663553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37972912165132024563538949 7119921030962254605663553)
            ·
              refine ⟨5339940773221690954247665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119921030962254605663553 5339940773221690954247665)
              ·
                refine ⟨4004955579916268215685749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339940773221690954247665 4004955579916268215685749)
                ·
                  refine ⟨375464585617150145220539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004955579916268215685749 375464585617150145220539)
                  ·
                    rfl

theorem cell23_6580932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_6580932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580932 prefixEnd_6580932 := by exact prefixLift 6580932
  have htrace : WordTrace (prefixWord ++ tailWord_6580932) baseStart_6580932 baseEnd_6580932 := by
    simpa [prefixWord, tailWord_6580932, baseEnd_6580932] using wordTrace_append hprefix tailTrace_6580932
  have hstable : (prefixWord ++ tailWord_6580932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580932).length < 2 ^ (prefixWord ++ tailWord_6580932).sum := by decide
  have hdescent : baseEnd_6580932 < baseStart_6580932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580965 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6580965 : Nat := 118140960795 + 6580965 * 2 ^ 59
def prefixEnd_6580965 : Nat := 4983230072969 + 3 ^ 40 * 6580965 * 2
def baseEnd_6580965 : Nat := 3379198215415949677872199

theorem tailTrace_6580965 : CollatzResearch.WordTrace tailWord_6580965 prefixEnd_6580965 3379198215415949677872199 := by
  unfold tailWord_6580965
  simp only [CollatzResearch.WordTrace]
  refine ⟨240027512603295219185728349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160018341735530146123818899 240027512603295219185728349)
  ·
    refine ⟨90010317226235707194648131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240027512603295219185728349 90010317226235707194648131)
    ·
      refine ⟨135015475839353560791972197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90010317226235707194648131 135015475839353560791972197)
      ·
        refine ⟨25315401719878792648494787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135015475839353560791972197 25315401719878792648494787)
        ·
          refine ⟨37973102579818188972742181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25315401719878792648494787 37973102579818188972742181)
          ·
            refine ⟨7119956733715910432389159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37973102579818188972742181 7119956733715910432389159)
            ·
              refine ⟨10679935100573865648583739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119956733715910432389159 10679935100573865648583739)
              ·
                refine ⟨16019902650860798472875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10679935100573865648583739 16019902650860798472875609)
                ·
                  refine ⟨12014926988145598854656707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16019902650860798472875609 12014926988145598854656707)
                  ·
                    refine ⟨18022390482218398281985061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12014926988145598854656707 18022390482218398281985061)
                    ·
                      refine ⟨3379198215415949677872199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18022390482218398281985061 3379198215415949677872199)
                      ·
                        rfl

theorem cell23_6580965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6580965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580965 prefixEnd_6580965 := by exact prefixLift 6580965
  have htrace : WordTrace (prefixWord ++ tailWord_6580965) baseStart_6580965 baseEnd_6580965 := by
    simpa [prefixWord, tailWord_6580965, baseEnd_6580965] using wordTrace_append hprefix tailTrace_6580965
  have hstable : (prefixWord ++ tailWord_6580965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580965).length < 2 ^ (prefixWord ++ tailWord_6580965).sum := by decide
  have hdescent : baseEnd_6580965 < baseStart_6580965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580975 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 1, 4]
def baseStart_6580975 : Nat := 118140960795 + 6580975 * 2 ^ 59
def prefixEnd_6580975 : Nat := 4983230072969 + 3 ^ 40 * 6580975 * 2
def baseEnd_6580975 : Nat := 1126401116740831546249051

theorem tailTrace_6580975 : CollatzResearch.WordTrace tailWord_6580975 prefixEnd_6580975 1126401116740831546249051 := by
  unfold tailWord_6580975
  simp only [CollatzResearch.WordTrace]
  refine ⟨240027877333258990893592379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160018584888839327262394919 240027877333258990893592379)
  ·
    refine ⟨360041815999888486340388569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240027877333258990893592379 360041815999888486340388569)
    ·
      refine ⟨270031361999916364755291427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360041815999888486340388569 270031361999916364755291427)
      ·
        refine ⟨405047042999874547132937141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270031361999916364755291427 405047042999874547132937141)
        ·
          refine ⟨37973160281238238793712857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405047042999874547132937141 37973160281238238793712857)
          ·
            refine ⟨28479870210928679095284643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37973160281238238793712857 28479870210928679095284643)
            ·
              refine ⟨42719805316393018642926965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28479870210928679095284643 42719805316393018642926965)
              ·
                refine ⟨4004981748411845497774403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42719805316393018642926965 4004981748411845497774403)
                ·
                  refine ⟨6007472622617768246661605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004981748411845497774403 6007472622617768246661605)
                  ·
                    refine ⟨1126401116740831546249051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007472622617768246661605 1126401116740831546249051)
                    ·
                      rfl

theorem cell23_6580975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_6580975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580975 prefixEnd_6580975 := by exact prefixLift 6580975
  have htrace : WordTrace (prefixWord ++ tailWord_6580975) baseStart_6580975 baseEnd_6580975 := by
    simpa [prefixWord, tailWord_6580975, baseEnd_6580975] using wordTrace_append hprefix tailTrace_6580975
  have hstable : (prefixWord ++ tailWord_6580975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580975).length < 2 ^ (prefixWord ++ tailWord_6580975).sum := by decide
  have hdescent : baseEnd_6580975 < baseStart_6580975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6580988 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 6]
def baseStart_6580988 : Nat := 118140960795 + 6580988 * 2 ^ 59
def prefixEnd_6580988 : Nat := 4983230072969 + 3 ^ 40 * 6580988 * 2
def baseEnd_6580988 : Nat := 375467780607889231987177

theorem tailTrace_6580988 : CollatzResearch.WordTrace tailWord_6580988 prefixEnd_6580988 375467780607889231987177 := by
  unfold tailWord_6580988
  simp only [CollatzResearch.WordTrace]
  refine ⟨120014175741105947056907809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160018900988141262742543745 120014175741105947056907809)
  ·
    refine ⟨90010631805829460292680857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120014175741105947056907809 90010631805829460292680857)
    ·
      refine ⟨67507973854372095219510643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90010631805829460292680857 67507973854372095219510643)
      ·
        refine ⟨101261960781558142829265965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67507973854372095219510643 101261960781558142829265965)
        ·
          refine ⟨37973235293084303560974737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101261960781558142829265965 37973235293084303560974737)
          ·
            refine ⟨28479926469813227670731053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37973235293084303560974737 28479926469813227670731053)
            ·
              refine ⟨10679972426179960376524145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28479926469813227670731053 10679972426179960376524145)
              ·
                refine ⟨8009979319634970282393109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679972426179960376524145 8009979319634970282393109)
                ·
                  refine ⟨375467780607889231987177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8009979319634970282393109 375467780607889231987177)
                  ·
                    rfl

theorem cell23_6580988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_6580988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6580988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6580988 prefixEnd_6580988 := by exact prefixLift 6580988
  have htrace : WordTrace (prefixWord ++ tailWord_6580988) baseStart_6580988 baseEnd_6580988 := by
    simpa [prefixWord, tailWord_6580988, baseEnd_6580988] using wordTrace_append hprefix tailTrace_6580988
  have hstable : (prefixWord ++ tailWord_6580988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6580988).length < 2 ^ (prefixWord ++ tailWord_6580988).sum := by decide
  have hdescent : baseEnd_6580988 < baseStart_6580988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6580988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581001 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_6581001 : Nat := 118140960795 + 6581001 * 2 ^ 59
def prefixEnd_6581001 : Nat := 4983230072969 + 3 ^ 40 * 6581001 * 2
def baseEnd_6581001 : Nat := 1126405566906503845674011

theorem tailTrace_6581001 : CollatzResearch.WordTrace tailWord_6581001 prefixEnd_6581001 1126405566906503845674011 := by
  unfold tailWord_6581001
  simp only [CollatzResearch.WordTrace]
  refine ⟨240028825631164797334038857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160019217087443198222692571 240028825631164797334038857)
  ·
    refine ⟨180021619223373598000529143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240028825631164797334038857 180021619223373598000529143)
    ·
      refine ⟨270032428835060397000793715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180021619223373598000529143 270032428835060397000793715)
      ·
        refine ⟨405048643252590595501190573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270032428835060397000793715 405048643252590595501190573)
        ·
          refine ⟨151893241219721473312946465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405048643252590595501190573 151893241219721473312946465)
          ·
            refine ⟨113919930914791104984709849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151893241219721473312946465 113919930914791104984709849)
            ·
              refine ⟨85439948186093328738532387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113919930914791104984709849 85439948186093328738532387)
              ·
                refine ⟨128159922279139993107798581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85439948186093328738532387 128159922279139993107798581)
                ·
                  refine ⟨12014992713669374353856117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128159922279139993107798581 12014992713669374353856117)
                  ·
                    refine ⟨1126405566906503845674011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12014992713669374353856117 1126405566906503845674011)
                    ·
                      rfl

theorem cell23_6581001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_6581001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581001 prefixEnd_6581001 := by exact prefixLift 6581001
  have htrace : WordTrace (prefixWord ++ tailWord_6581001) baseStart_6581001 baseEnd_6581001 := by
    simpa [prefixWord, tailWord_6581001, baseEnd_6581001] using wordTrace_append hprefix tailTrace_6581001
  have hstable : (prefixWord ++ tailWord_6581001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581001).length < 2 ^ (prefixWord ++ tailWord_6581001).sum := by decide
  have hdescent : baseEnd_6581001 < baseStart_6581001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581025 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6581025 : Nat := 118140960795 + 6581025 * 2 ^ 59
def prefixEnd_6581025 : Nat := 4983230072969 + 3 ^ 40 * 6581025 * 2
def baseEnd_6581025 : Nat := 3379229024255219443121923

theorem tailTrace_6581025 : CollatzResearch.WordTrace tailWord_6581025 prefixEnd_6581025 3379229024255219443121923 := by
  unfold tailWord_6581025
  simp only [CollatzResearch.WordTrace]
  refine ⟨240029700983077849432912529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160019800655385232955275019 240029700983077849432912529)
  ·
    refine ⟨180022275737308387074684397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240029700983077849432912529 180022275737308387074684397)
    ·
      refine ⟨67508353401490645153006649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180022275737308387074684397 67508353401490645153006649)
      ·
        refine ⟨50631265051117983864754987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67508353401490645153006649 50631265051117983864754987)
        ·
          refine ⟨75946897576676975797132481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50631265051117983864754987 75946897576676975797132481)
          ·
            refine ⟨56960173182507731847849361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75946897576676975797132481 56960173182507731847849361)
            ·
              refine ⟨42720129886880798885887021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56960173182507731847849361 42720129886880798885887021)
              ·
                refine ⟨16020048707580299582207633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42720129886880798885887021 16020048707580299582207633)
                ·
                  refine ⟨12015036530685224686655725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16020048707580299582207633 12015036530685224686655725)
                  ·
                    refine ⟨4505638699006959257495897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12015036530685224686655725 4505638699006959257495897)
                    ·
                      refine ⟨3379229024255219443121923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505638699006959257495897 3379229024255219443121923)
                      ·
                        rfl

theorem cell23_6581025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6581025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581025 prefixEnd_6581025 := by exact prefixLift 6581025
  have htrace : WordTrace (prefixWord ++ tailWord_6581025) baseStart_6581025 baseEnd_6581025 := by
    simpa [prefixWord, tailWord_6581025, baseEnd_6581025] using wordTrace_append hprefix tailTrace_6581025
  have hstable : (prefixWord ++ tailWord_6581025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581025).length < 2 ^ (prefixWord ++ tailWord_6581025).sum := by decide
  have hdescent : baseEnd_6581025 < baseStart_6581025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581048 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_6581048 : Nat := 118140960795 + 6581048 * 2 ^ 59
def prefixEnd_6581048 : Nat := 4983230072969 + 3 ^ 40 * 6581048 * 2
def baseEnd_6581048 : Nat := 1126413611436757617711439

theorem tailTrace_6581048 : CollatzResearch.WordTrace tailWord_6581048 prefixEnd_6581048 1126413611436757617711439 := by
  unfold tailWord_6581048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120015269930997262180499899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160020359907996349573999865 120015269930997262180499899)
  ·
    refine ⟨180022904896495893270749849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120015269930997262180499899 180022904896495893270749849)
    ·
      refine ⟨135017178672371919953062387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180022904896495893270749849 135017178672371919953062387)
      ·
        refine ⟨202525768008557879929593581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135017178672371919953062387 202525768008557879929593581)
        ·
          refine ⟨75947163003209204973597593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202525768008557879929593581 75947163003209204973597593)
          ·
            refine ⟨56960372252406903730198195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75947163003209204973597593 56960372252406903730198195)
            ·
              refine ⟨85440558378610355595297293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56960372252406903730198195 85440558378610355595297293)
              ·
                refine ⟨32040209391978883348236485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85440558378610355595297293 32040209391978883348236485)
                ·
                  refine ⟨6007539260996040627794341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32040209391978883348236485 6007539260996040627794341)
                  ·
                    refine ⟨1126413611436757617711439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007539260996040627794341 1126413611436757617711439)
                    ·
                      rfl

theorem cell23_6581048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_6581048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581048 prefixEnd_6581048 := by exact prefixLift 6581048
  have htrace : WordTrace (prefixWord ++ tailWord_6581048) baseStart_6581048 baseEnd_6581048 := by
    simpa [prefixWord, tailWord_6581048, baseEnd_6581048] using wordTrace_append hprefix tailTrace_6581048
  have hstable : (prefixWord ++ tailWord_6581048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581048).length < 2 ^ (prefixWord ++ tailWord_6581048).sum := by decide
  have hdescent : baseEnd_6581048 < baseStart_6581048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581065 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_6581065 : Nat := 118140960795 + 6581065 * 2 ^ 59
def prefixEnd_6581065 : Nat := 4983230072969 + 3 ^ 40 * 6581065 * 2
def baseEnd_6581065 : Nat := 1126416521160466428873913

theorem tailTrace_6581065 : CollatzResearch.WordTrace tailWord_6581065 prefixEnd_6581065 1126416521160466428873913 := by
  unfold tailWord_6581065
  simp only [CollatzResearch.WordTrace]
  refine ⟨240031159902932936264368649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160020773268621957509579099 240031159902932936264368649)
  ·
    refine ⟨180023369927199702198276487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240031159902932936264368649 180023369927199702198276487)
    ·
      refine ⟨270035054890799553297414731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180023369927199702198276487 270035054890799553297414731)
      ·
        refine ⟨405052582336199329946122097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270035054890799553297414731 405052582336199329946122097)
        ·
          refine ⟨303789436752149497459591573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405052582336199329946122097 303789436752149497459591573)
          ·
            refine ⟨14240129847757007693418355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 303789436752149497459591573 14240129847757007693418355)
            ·
              refine ⟨21360194771635511540127533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14240129847757007693418355 21360194771635511540127533)
              ·
                refine ⟨8010073039363316827547825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21360194771635511540127533 8010073039363316827547825)
                ·
                  refine ⟨6007554779522487620660869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8010073039363316827547825 6007554779522487620660869)
                  ·
                    refine ⟨1126416521160466428873913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007554779522487620660869 1126416521160466428873913)
                    ·
                      rfl

theorem cell23_6581065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_6581065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581065 prefixEnd_6581065 := by exact prefixLift 6581065
  have htrace : WordTrace (prefixWord ++ tailWord_6581065) baseStart_6581065 baseEnd_6581065 := by
    simpa [prefixWord, tailWord_6581065, baseEnd_6581065] using wordTrace_append hprefix tailTrace_6581065
  have hstable : (prefixWord ++ tailWord_6581065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581065).length < 2 ^ (prefixWord ++ tailWord_6581065).sum := by decide
  have hdescent : baseEnd_6581065 < baseStart_6581065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581068 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6581068 : Nat := 118140960795 + 6581068 * 2 ^ 59
def prefixEnd_6581068 : Nat := 4983230072969 + 3 ^ 40 * 6581068 * 2
def baseEnd_6581068 : Nat := 3379251103923362774884225

theorem tailTrace_6581068 : CollatzResearch.WordTrace tailWord_6581068 prefixEnd_6581068 3379251103923362774884225 := by
  unfold tailWord_6581068
  simp only [CollatzResearch.WordTrace]
  refine ⟨120015634660961033888363929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160020846214614711851151905 120015634660961033888363929)
  ·
    refine ⟨90011725995720775416272947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120015634660961033888363929 90011725995720775416272947)
    ·
      refine ⟨135017588993581163124409421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90011725995720775416272947 135017588993581163124409421)
      ·
        refine ⟨50631595872592936171653533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135017588993581163124409421 50631595872592936171653533)
        ·
          refine ⟨18986848452222351064370075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50631595872592936171653533 18986848452222351064370075)
          ·
            refine ⟨28480272678333526596555113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18986848452222351064370075 28480272678333526596555113)
            ·
              refine ⟨21360204508750144947416335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28480272678333526596555113 21360204508750144947416335)
              ·
                refine ⟨32040306763125217421124503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21360204508750144947416335 32040306763125217421124503)
                ·
                  refine ⟨48060460144687826131686755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32040306763125217421124503 48060460144687826131686755)
                  ·
                    refine ⟨72090690217031739197530133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48060460144687826131686755 72090690217031739197530133)
                    ·
                      refine ⟨3379251103923362774884225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72090690217031739197530133 3379251103923362774884225)
                      ·
                        rfl

theorem cell23_6581068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6581068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581068 prefixEnd_6581068 := by exact prefixLift 6581068
  have htrace : WordTrace (prefixWord ++ tailWord_6581068) baseStart_6581068 baseEnd_6581068 := by
    simpa [prefixWord, tailWord_6581068, baseEnd_6581068] using wordTrace_append hprefix tailTrace_6581068
  have hstable : (prefixWord ++ tailWord_6581068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581068).length < 2 ^ (prefixWord ++ tailWord_6581068).sum := by decide
  have hdescent : baseEnd_6581068 < baseStart_6581068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581069 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_6581069 : Nat := 118140960795 + 6581069 * 2 ^ 59
def prefixEnd_6581069 : Nat := 4983230072969 + 3 ^ 40 * 6581069 * 2
def baseEnd_6581069 : Nat := 1126417205801339090323907

theorem tailTrace_6581069 : CollatzResearch.WordTrace tailWord_6581069 prefixEnd_6581069 1126417205801339090323907 := by
  unfold tailWord_6581069
  simp only [CollatzResearch.WordTrace]
  refine ⟨240031305794918444947514261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160020870529945629965009507 240031305794918444947514261)
  ·
    refine ⟨11251467459136802106914731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240031305794918444947514261 11251467459136802106914731)
    ·
      refine ⟨16877201188705203160372097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251467459136802106914731 16877201188705203160372097)
      ·
        refine ⟨12657900891528902370279073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16877201188705203160372097 12657900891528902370279073)
        ·
          refine ⟨9493425668646676777709305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12657900891528902370279073 9493425668646676777709305)
          ·
            refine ⟨7120069251485007583281979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9493425668646676777709305 7120069251485007583281979)
            ·
              refine ⟨10680103877227511374922969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120069251485007583281979 10680103877227511374922969)
              ·
                refine ⟨8010077907920633531192227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10680103877227511374922969 8010077907920633531192227)
                ·
                  refine ⟨12015116861880950296788341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8010077907920633531192227 12015116861880950296788341)
                  ·
                    refine ⟨1126417205801339090323907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12015116861880950296788341 1126417205801339090323907)
                    ·
                      rfl

theorem cell23_6581069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_6581069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581069 prefixEnd_6581069 := by exact prefixLift 6581069
  have htrace : WordTrace (prefixWord ++ tailWord_6581069) baseStart_6581069 baseEnd_6581069 := by
    simpa [prefixWord, tailWord_6581069, baseEnd_6581069] using wordTrace_append hprefix tailTrace_6581069
  have hstable : (prefixWord ++ tailWord_6581069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581069).length < 2 ^ (prefixWord ++ tailWord_6581069).sum := by decide
  have hdescent : baseEnd_6581069 < baseStart_6581069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581106 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_6581106 : Nat := 118140960795 + 6581106 * 2 ^ 59
def prefixEnd_6581106 : Nat := 4983230072969 + 3 ^ 40 * 6581106 * 2
def baseEnd_6581106 : Nat := 3379270616188233626209051

theorem tailTrace_6581106 : CollatzResearch.WordTrace tailWord_6581106 prefixEnd_6581106 3379270616188233626209051 := by
  unfold tailWord_6581106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60008163823946100066652793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160021770197189600177740781 60008163823946100066652793)
  ·
    refine ⟨45006122867959575049989595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60008163823946100066652793 45006122867959575049989595)
    ·
      refine ⟨67509184301939362574984393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45006122867959575049989595 67509184301939362574984393)
      ·
        refine ⟨50631888226454521931238295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67509184301939362574984393 50631888226454521931238295)
        ·
          refine ⟨75947832339681782896857443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50631888226454521931238295 75947832339681782896857443)
          ·
            refine ⟨113921748509522674345286165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75947832339681782896857443 113921748509522674345286165)
            ·
              refine ⟨5340081961383875359935289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113921748509522674345286165 5340081961383875359935289)
              ·
                refine ⟨4005061471037906519951467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340081961383875359935289 4005061471037906519951467)
                ·
                  refine ⟨6007592206556859779927201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005061471037906519951467 6007592206556859779927201)
                  ·
                    refine ⟨4505694154917644834945401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007592206556859779927201 4505694154917644834945401)
                    ·
                      refine ⟨3379270616188233626209051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505694154917644834945401 3379270616188233626209051)
                      ·
                        rfl

theorem cell23_6581106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_6581106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581106 prefixEnd_6581106 := by exact prefixLift 6581106
  have htrace : WordTrace (prefixWord ++ tailWord_6581106) baseStart_6581106 baseEnd_6581106 := by
    simpa [prefixWord, tailWord_6581106, baseEnd_6581106] using wordTrace_append hprefix tailTrace_6581106
  have hstable : (prefixWord ++ tailWord_6581106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581106).length < 2 ^ (prefixWord ++ tailWord_6581106).sum := by decide
  have hdescent : baseEnd_6581106 < baseStart_6581106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581115 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 3, 3, 2]
def baseStart_6581115 : Nat := 118140960795 + 6581115 * 2 ^ 59
def prefixEnd_6581115 : Nat := 4983230072969 + 3 ^ 40 * 6581115 * 2
def baseEnd_6581115 : Nat := 3379275237514124090996509

theorem tailTrace_6581115 : CollatzResearch.WordTrace tailWord_6581115 prefixEnd_6581115 3379275237514124090996509 := by
  unfold tailWord_6581115
  simp only [CollatzResearch.WordTrace]
  refine ⟨240032983552751794803688799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160021989035167863202459199 240032983552751794803688799)
  ·
    refine ⟨360049475329127692205533199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240032983552751794803688799 360049475329127692205533199)
    ·
      refine ⟨540074212993691538308299799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360049475329127692205533199 540074212993691538308299799)
      ·
        refine ⟨810111319490537307462449699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540074212993691538308299799 810111319490537307462449699)
        ·
          refine ⟨1215166979235805961193674549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810111319490537307462449699 1215166979235805961193674549)
          ·
            refine ⟨113921904303356808861906989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1215166979235805961193674549 113921904303356808861906989)
            ·
              refine ⟨42720714113758803323215121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113921904303356808861906989 42720714113758803323215121)
              ·
                refine ⟨32040535585319102492411341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42720714113758803323215121 32040535585319102492411341)
                ·
                  refine ⟨12015200844494663434654253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32040535585319102492411341 12015200844494663434654253)
                  ·
                    refine ⟨4505700316685498787995345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12015200844494663434654253 4505700316685498787995345)
                    ·
                      refine ⟨3379275237514124090996509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505700316685498787995345 3379275237514124090996509)
                      ·
                        rfl

theorem cell23_6581115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3, 2].length) (baseStart_6581115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581115 prefixEnd_6581115 := by exact prefixLift 6581115
  have htrace : WordTrace (prefixWord ++ tailWord_6581115) baseStart_6581115 baseEnd_6581115 := by
    simpa [prefixWord, tailWord_6581115, baseEnd_6581115] using wordTrace_append hprefix tailTrace_6581115
  have hstable : (prefixWord ++ tailWord_6581115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581115).length < 2 ^ (prefixWord ++ tailWord_6581115).sum := by decide
  have hdescent : baseEnd_6581115 < baseStart_6581115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581172 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6581172 : Nat := 118140960795 + 6581172 * 2 ^ 59
def prefixEnd_6581172 : Nat := 4983230072969 + 3 ^ 40 * 6581172 * 2
def baseEnd_6581172 : Nat := 1126434835303810122661249

theorem tailTrace_6581172 : CollatzResearch.WordTrace tailWord_6581172 prefixEnd_6581172 1126434835303810122661249 := by
  unfold tailWord_6581172
  simp only [CollatzResearch.WordTrace]
  refine ⟨120017531256772646769256885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160023375009030195692342513 120017531256772646769256885)
  ·
    refine ⟨11251643555322435634617833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120017531256772646769256885 11251643555322435634617833)
    ·
      refine ⟨8438732666491826725963375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11251643555322435634617833 8438732666491826725963375)
      ·
        refine ⟨12658098999737740088945063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438732666491826725963375 12658098999737740088945063)
        ·
          refine ⟨18987148499606610133417595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12658098999737740088945063 18987148499606610133417595)
          ·
            refine ⟨28480722749409915200126393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18987148499606610133417595 28480722749409915200126393)
            ·
              refine ⟨21360542062057436400094795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28480722749409915200126393 21360542062057436400094795)
              ·
                refine ⟨32040813093086154600142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21360542062057436400094795 32040813093086154600142193)
                ·
                  refine ⟨24030609819814615950106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32040813093086154600142193 24030609819814615950106645)
                  ·
                    refine ⟨1126434835303810122661249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24030609819814615950106645 1126434835303810122661249)
                    ·
                      rfl

theorem cell23_6581172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6581172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581172 prefixEnd_6581172 := by exact prefixLift 6581172
  have htrace : WordTrace (prefixWord ++ tailWord_6581172) baseStart_6581172 baseEnd_6581172 := by
    simpa [prefixWord, tailWord_6581172, baseEnd_6581172] using wordTrace_append hprefix tailTrace_6581172
  have hstable : (prefixWord ++ tailWord_6581172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581172).length < 2 ^ (prefixWord ++ tailWord_6581172).sum := by decide
  have hdescent : baseEnd_6581172 < baseStart_6581172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581230 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_6581230 : Nat := 118140960795 + 6581230 * 2 ^ 59
def prefixEnd_6581230 : Nat := 4983230072969 + 3 ^ 40 * 6581230 * 2
def baseEnd_6581230 : Nat := 3379334287789391141058481

theorem tailTrace_6581230 : CollatzResearch.WordTrace tailWord_6581230 prefixEnd_6581230 3379334287789391141058481 := by
  unfold tailWord_6581230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004647243416896180515643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160024785298223446296083429 30004647243416896180515643)
  ·
    refine ⟨45006970865125344270773465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30004647243416896180515643 45006970865125344270773465)
    ·
      refine ⟨33755228148844008203080099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45006970865125344270773465 33755228148844008203080099)
      ·
        refine ⟨50632842223266012304620149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33755228148844008203080099 50632842223266012304620149)
        ·
          refine ⟨4746828958431188653558139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50632842223266012304620149 4746828958431188653558139)
          ·
            refine ⟨7120243437646782980337209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746828958431188653558139 7120243437646782980337209)
            ·
              refine ⟨5340182578235087235252907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7120243437646782980337209 5340182578235087235252907)
              ·
                refine ⟨8010273867352630852879361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340182578235087235252907 8010273867352630852879361)
                ·
                  refine ⟨6007705400514473139659521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8010273867352630852879361 6007705400514473139659521)
                  ·
                    refine ⟨4505779050385854854744641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007705400514473139659521 4505779050385854854744641)
                    ·
                      refine ⟨3379334287789391141058481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505779050385854854744641 3379334287789391141058481)
                      ·
                        rfl

theorem cell23_6581230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_6581230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581230 prefixEnd_6581230 := by exact prefixLift 6581230
  have htrace : WordTrace (prefixWord ++ tailWord_6581230) baseStart_6581230 baseEnd_6581230 := by
    simpa [prefixWord, tailWord_6581230, baseEnd_6581230] using wordTrace_append hprefix tailTrace_6581230
  have hstable : (prefixWord ++ tailWord_6581230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581230).length < 2 ^ (prefixWord ++ tailWord_6581230).sum := by decide
  have hdescent : baseEnd_6581230 < baseStart_6581230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581245 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_6581245 : Nat := 118140960795 + 6581245 * 2 ^ 59
def prefixEnd_6581245 : Nat := 4983230072969 + 3 ^ 40 * 6581245 * 2
def baseEnd_6581245 : Nat := 1126447329999736194123637

theorem tailTrace_6581245 : CollatzResearch.WordTrace tailWord_6581245 prefixEnd_6581245 1126447329999736194123637 := by
  unfold tailWord_6581245
  simp only [CollatzResearch.WordTrace]
  refine ⟨240037725042280827005921189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160025150028187218003947459 240037725042280827005921189)
  ·
    refine ⟨45007073445427655063610223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240037725042280827005921189 45007073445427655063610223)
    ·
      refine ⟨67510610168141482595415335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45007073445427655063610223 67510610168141482595415335)
      ·
        refine ⟨101265915252212223893123003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67510610168141482595415335 101265915252212223893123003)
        ·
          refine ⟨151898872878318335839684505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101265915252212223893123003 151898872878318335839684505)
          ·
            refine ⟨113924154658738751879763379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151898872878318335839684505 113924154658738751879763379)
            ·
              refine ⟨170886231988108127819645069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113924154658738751879763379 170886231988108127819645069)
              ·
                refine ⟨64082336995540547932366901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170886231988108127819645069 64082336995540547932366901)
                ·
                  refine ⟨6007719093331926368659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64082336995540547932366901 6007719093331926368659397)
                  ·
                    refine ⟨1126447329999736194123637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007719093331926368659397 1126447329999736194123637)
                    ·
                      rfl

theorem cell23_6581245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_6581245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581245 prefixEnd_6581245 := by exact prefixLift 6581245
  have htrace : WordTrace (prefixWord ++ tailWord_6581245) baseStart_6581245 baseEnd_6581245 := by
    simpa [prefixWord, tailWord_6581245, baseEnd_6581245] using wordTrace_append hprefix tailTrace_6581245
  have hstable : (prefixWord ++ tailWord_6581245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581245).length < 2 ^ (prefixWord ++ tailWord_6581245).sum := by decide
  have hdescent : baseEnd_6581245 < baseStart_6581245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581272 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6581272 : Nat := 118140960795 + 6581272 * 2 ^ 59
def prefixEnd_6581272 : Nat := 4983230072969 + 3 ^ 40 * 6581272 * 2
def baseEnd_6581272 : Nat := 3379355853976879976733287

theorem tailTrace_6581272 : CollatzResearch.WordTrace tailWord_6581272 prefixEnd_6581272 3379355853976879976733287 := by
  unfold tailWord_6581272
  simp only [CollatzResearch.WordTrace]
  refine ⟨120019354906591505308577035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160025806542122007078102713 120019354906591505308577035)
  ·
    refine ⟨180029032359887257962865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120019354906591505308577035 180029032359887257962865553)
    ·
      refine ⟨135021774269915443472149165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180029032359887257962865553 135021774269915443472149165)
      ·
        refine ⟨50633165351218291302055937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135021774269915443472149165 50633165351218291302055937)
        ·
          refine ⟨37974874013413718476541953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50633165351218291302055937 37974874013413718476541953)
          ·
            refine ⟨28481155510060288857406465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37974874013413718476541953 28481155510060288857406465)
            ·
              refine ⟨21360866632545216643054849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28481155510060288857406465 21360866632545216643054849)
              ·
                refine ⟨16020649974408912482291137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21360866632545216643054849 16020649974408912482291137)
                ·
                  refine ⟨12015487480806684361718353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16020649974408912482291137 12015487480806684361718353)
                  ·
                    refine ⟨9011615610605013271288765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12015487480806684361718353 9011615610605013271288765)
                    ·
                      refine ⟨3379355853976879976733287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9011615610605013271288765 3379355853976879976733287)
                      ·
                        rfl

theorem cell23_6581272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6581272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581272 prefixEnd_6581272 := by exact prefixLift 6581272
  have htrace : WordTrace (prefixWord ++ tailWord_6581272) baseStart_6581272 baseEnd_6581272 := by
    simpa [prefixWord, tailWord_6581272, baseEnd_6581272] using wordTrace_append hprefix tailTrace_6581272
  have hstable : (prefixWord ++ tailWord_6581272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581272).length < 2 ^ (prefixWord ++ tailWord_6581272).sum := by decide
  have hdescent : baseEnd_6581272 < baseStart_6581272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581279 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 1, 4]
def baseStart_6581279 : Nat := 118140960795 + 6581279 * 2 ^ 59
def prefixEnd_6581279 : Nat := 4983230072969 + 3 ^ 40 * 6581279 * 2
def baseEnd_6581279 : Nat := 1126453149447153816448585

theorem tailTrace_6581279 : CollatzResearch.WordTrace tailWord_6581279 prefixEnd_6581279 1126453149447153816448585 := by
  unfold tailWord_6581279
  simp only [CollatzResearch.WordTrace]
  refine ⟨240038965124157650812658891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160025976749438433875105927 240038965124157650812658891)
  ·
    refine ⟨360058447686236476218988337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240038965124157650812658891 360058447686236476218988337)
    ·
      refine ⟨270043835764677357164241253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360058447686236476218988337 270043835764677357164241253)
      ·
        refine ⟨50633219205877004468295235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270043835764677357164241253 50633219205877004468295235)
        ·
          refine ⟨75949828808815506702442853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50633219205877004468295235 75949828808815506702442853)
          ·
            refine ⟨14240592901652907506708035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75949828808815506702442853 14240592901652907506708035)
            ·
              refine ⟨21360889352479361260062053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14240592901652907506708035 21360889352479361260062053)
              ·
                refine ⟨4005166753589880236261635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21360889352479361260062053 4005166753589880236261635)
                ·
                  refine ⟨6007750130384820354392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005166753589880236261635 6007750130384820354392453)
                  ·
                    refine ⟨1126453149447153816448585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007750130384820354392453 1126453149447153816448585)
                    ·
                      rfl

theorem cell23_6581279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_6581279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581279 prefixEnd_6581279 := by exact prefixLift 6581279
  have htrace : WordTrace (prefixWord ++ tailWord_6581279) baseStart_6581279 baseEnd_6581279 := by
    simpa [prefixWord, tailWord_6581279, baseEnd_6581279] using wordTrace_append hprefix tailTrace_6581279
  have hstable : (prefixWord ++ tailWord_6581279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581279).length < 2 ^ (prefixWord ++ tailWord_6581279).sum := by decide
  have hdescent : baseEnd_6581279 < baseStart_6581279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581312 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2]
def baseStart_6581312 : Nat := 118140960795 + 6581312 * 2 ^ 59
def prefixEnd_6581312 : Nat := 4983230072969 + 3 ^ 40 * 6581312 * 2
def baseEnd_6581312 : Nat := 3379376393203059820233103

theorem tailTrace_6581312 : CollatzResearch.WordTrace tailWord_6581312 prefixEnd_6581312 3379376393203059820233103 := by
  unfold tailWord_6581312
  simp only [CollatzResearch.WordTrace]
  refine ⟨120020084366519048724305095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160026779155358731632406793 120020084366519048724305095)
  ·
    refine ⟨180030126549778573086457643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120020084366519048724305095 180030126549778573086457643)
    ·
      refine ⟨270045189824667859629686465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180030126549778573086457643 270045189824667859629686465)
      ·
        refine ⟨202533892368500894722264849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270045189824667859629686465 202533892368500894722264849)
        ·
          refine ⟨151900419276375671041698637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202533892368500894722264849 151900419276375671041698637)
          ·
            refine ⟨56962657228640876640636989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151900419276375671041698637 56962657228640876640636989)
            ·
              refine ⟨21360996460740328740238871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56962657228640876640636989 21360996460740328740238871)
              ·
                refine ⟨32041494691110493110358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21360996460740328740238871 32041494691110493110358307)
                ·
                  refine ⟨48062242036665739665537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32041494691110493110358307 48062242036665739665537461)
                  ·
                    refine ⟨4505835190937413093644137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48062242036665739665537461 4505835190937413093644137)
                    ·
                      refine ⟨3379376393203059820233103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505835190937413093644137 3379376393203059820233103)
                      ·
                        rfl

theorem cell23_6581312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_6581312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581312 prefixEnd_6581312 := by exact prefixLift 6581312
  have htrace : WordTrace (prefixWord ++ tailWord_6581312) baseStart_6581312 baseEnd_6581312 := by
    simpa [prefixWord, tailWord_6581312, baseEnd_6581312] using wordTrace_append hprefix tailTrace_6581312
  have hstable : (prefixWord ++ tailWord_6581312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581312).length < 2 ^ (prefixWord ++ tailWord_6581312).sum := by decide
  have hdescent : baseEnd_6581312 < baseStart_6581312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581345 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6581345 : Nat := 118140960795 + 6581345 * 2 ^ 59
def prefixEnd_6581345 : Nat := 4983230072969 + 3 ^ 40 * 6581345 * 2
def baseEnd_6581345 : Nat := 3379393338064658191120451

theorem tailTrace_6581345 : CollatzResearch.WordTrace tailWord_6581345 prefixEnd_6581345 3379393338064658191120451 := by
  unfold tailWord_6581345
  simp only [CollatzResearch.WordTrace]
  refine ⟨240041372341918544084561489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160027581561279029389707659 240041372341918544084561489)
  ·
    refine ⟨180031029256438908063421117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240041372341918544084561489 180031029256438908063421117)
    ·
      refine ⟨67511635971164590523782919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180031029256438908063421117 67511635971164590523782919)
      ·
        refine ⟨101267453956746885785674379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67511635971164590523782919 101267453956746885785674379)
        ·
          refine ⟨151901180935120328678511569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101267453956746885785674379 151901180935120328678511569)
          ·
            refine ⟨113925885701340246508883677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151901180935120328678511569 113925885701340246508883677)
            ·
              refine ⟨42722207138002592440831379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113925885701340246508883677 42722207138002592440831379)
              ·
                refine ⟨64083310707003888661247069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42722207138002592440831379 64083310707003888661247069)
                ·
                  refine ⟨24031241515126458247967651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64083310707003888661247069 24031241515126458247967651)
                  ·
                    refine ⟨36046862272689687371951477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24031241515126458247967651 36046862272689687371951477)
                    ·
                      refine ⟨3379393338064658191120451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36046862272689687371951477 3379393338064658191120451)
                      ·
                        rfl

theorem cell23_6581345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6581345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581345 prefixEnd_6581345 := by exact prefixLift 6581345
  have htrace : WordTrace (prefixWord ++ tailWord_6581345) baseStart_6581345 baseEnd_6581345 := by
    simpa [prefixWord, tailWord_6581345, baseEnd_6581345] using wordTrace_append hprefix tailTrace_6581345
  have hstable : (prefixWord ++ tailWord_6581345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581345).length < 2 ^ (prefixWord ++ tailWord_6581345).sum := by decide
  have hdescent : baseEnd_6581345 < baseStart_6581345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581359 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 3, 2, 2]
def baseStart_6581359 : Nat := 118140960795 + 6581359 * 2 ^ 59
def prefixEnd_6581359 : Nat := 4983230072969 + 3 ^ 40 * 6581359 * 2
def baseEnd_6581359 : Nat := 3379400526793821136345387

theorem tailTrace_6581359 : CollatzResearch.WordTrace tailWord_6581359 prefixEnd_6581359 3379400526793821136345387 := by
  unfold tailWord_6581359
  simp only [CollatzResearch.WordTrace]
  refine ⟨240041882963867824475571131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160027921975911882983714087 240041882963867824475571131)
  ·
    refine ⟨360062824445801736713356697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240041882963867824475571131 360062824445801736713356697)
    ·
      refine ⟨270047118334351302535017523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360062824445801736713356697 270047118334351302535017523)
      ·
        refine ⟨405070677501526953802526285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270047118334351302535017523 405070677501526953802526285)
        ·
          refine ⟨151901504063072607675947357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405070677501526953802526285 151901504063072607675947357)
          ·
            refine ⟨56963064023652227878480259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151901504063072607675947357 56963064023652227878480259)
            ·
              refine ⟨85444596035478341817720389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56963064023652227878480259 85444596035478341817720389)
              ·
                refine ⟨16020861756652189090822573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85444596035478341817720389 16020861756652189090822573)
                ·
                  refine ⟨6007823158744570909058465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16020861756652189090822573 6007823158744570909058465)
                  ·
                    refine ⟨4505867369058428181793849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007823158744570909058465 4505867369058428181793849)
                    ·
                      refine ⟨3379400526793821136345387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505867369058428181793849 3379400526793821136345387)
                      ·
                        rfl

theorem cell23_6581359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2, 2].length) (baseStart_6581359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581359 prefixEnd_6581359 := by exact prefixLift 6581359
  have htrace : WordTrace (prefixWord ++ tailWord_6581359) baseStart_6581359 baseEnd_6581359 := by
    simpa [prefixWord, tailWord_6581359, baseEnd_6581359] using wordTrace_append hprefix tailTrace_6581359
  have hstable : (prefixWord ++ tailWord_6581359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581359).length < 2 ^ (prefixWord ++ tailWord_6581359).sum := by decide
  have hdescent : baseEnd_6581359 < baseStart_6581359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581430 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6581430 : Nat := 118140960795 + 6581430 * 2 ^ 59
def prefixEnd_6581430 : Nat := 4983230072969 + 3 ^ 40 * 6581430 * 2
def baseEnd_6581430 : Nat := 3379436983920290358557561

theorem tailTrace_6581430 : CollatzResearch.WordTrace tailWord_6581430 prefixEnd_6581430 3379436983920290358557561 := by
  unfold tailWord_6581430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002779534163162725087859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160029648364407069067603829 15002779534163162725087859)
  ·
    refine ⟨22504169301244744087631789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15002779534163162725087859 22504169301244744087631789)
    ·
      refine ⟨8439063487966779032861921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22504169301244744087631789 8439063487966779032861921)
      ·
        refine ⟨6329297615975084274646441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439063487966779032861921 6329297615975084274646441)
        ·
          refine ⟨4746973211981313205984831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6329297615975084274646441 4746973211981313205984831)
          ·
            refine ⟨7120459817971969808977247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746973211981313205984831 7120459817971969808977247)
            ·
              refine ⟨10680689726957954713465871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120459817971969808977247 10680689726957954713465871)
              ·
                refine ⟨16021034590436932070198807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680689726957954713465871 16021034590436932070198807)
                ·
                  refine ⟨24031551885655398105298211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021034590436932070198807 24031551885655398105298211)
                  ·
                    refine ⟨36047327828483097157947317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24031551885655398105298211 36047327828483097157947317)
                    ·
                      refine ⟨3379436983920290358557561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36047327828483097157947317 3379436983920290358557561)
                      ·
                        rfl

theorem cell23_6581430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6581430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581430 prefixEnd_6581430 := by exact prefixLift 6581430
  have htrace : WordTrace (prefixWord ++ tailWord_6581430) baseStart_6581430 baseEnd_6581430 := by
    simpa [prefixWord, tailWord_6581430, baseEnd_6581430] using wordTrace_append hprefix tailTrace_6581430
  have hstable : (prefixWord ++ tailWord_6581430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581430).length < 2 ^ (prefixWord ++ tailWord_6581430).sum := by decide
  have hdescent : baseEnd_6581430 < baseStart_6581430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581435 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_6581435 : Nat := 118140960795 + 6581435 * 2 ^ 59
def prefixEnd_6581435 : Nat := 4983230072969 + 3 ^ 40 * 6581435 * 2
def baseEnd_6581435 : Nat := 3379439551323562838995037

theorem tailTrace_6581435 : CollatzResearch.WordTrace tailWord_6581435 prefixEnd_6581435 3379439551323562838995037 := by
  unfold tailWord_6581435
  simp only [CollatzResearch.WordTrace]
  refine ⟨240044654911592489455337759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160029769941061659636891839 240044654911592489455337759)
  ·
    refine ⟨360066982367388734183006639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240044654911592489455337759 360066982367388734183006639)
    ·
      refine ⟨540100473551083101274509959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360066982367388734183006639 540100473551083101274509959)
      ·
        refine ⟨810150710326624651911764939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540100473551083101274509959 810150710326624651911764939)
        ·
          refine ⟨1215226065489936977867647409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810150710326624651911764939 1215226065489936977867647409)
          ·
            refine ⟨911419549117452733400735557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215226065489936977867647409 911419549117452733400735557)
            ·
              refine ⟨170891165459522387512637917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 911419549117452733400735557 170891165459522387512637917)
              ·
                refine ⟨64084187047320895317239219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170891165459522387512637917 64084187047320895317239219)
                ·
                  refine ⟨96126280570981342975858829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64084187047320895317239219 96126280570981342975858829)
                  ·
                    refine ⟨36047355214118003615947061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96126280570981342975858829 36047355214118003615947061)
                    ·
                      refine ⟨3379439551323562838995037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36047355214118003615947061 3379439551323562838995037)
                      ·
                        rfl

theorem cell23_6581435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_6581435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581435 prefixEnd_6581435 := by exact prefixLift 6581435
  have htrace : WordTrace (prefixWord ++ tailWord_6581435) baseStart_6581435 baseEnd_6581435 := by
    simpa [prefixWord, tailWord_6581435, baseEnd_6581435] using wordTrace_append hprefix tailTrace_6581435
  have hstable : (prefixWord ++ tailWord_6581435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581435).length < 2 ^ (prefixWord ++ tailWord_6581435).sum := by decide
  have hdescent : baseEnd_6581435 < baseStart_6581435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581444 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_6581444 : Nat := 118140960795 + 6581444 * 2 ^ 59
def prefixEnd_6581444 : Nat := 4983230072969 + 3 ^ 40 * 6581444 * 2
def baseEnd_6581444 : Nat := 3379444172649453303782497

theorem tailTrace_6581444 : CollatzResearch.WordTrace tailWord_6581444 prefixEnd_6581444 3379444172649453303782497 := by
  unfold tailWord_6581444
  simp only [CollatzResearch.WordTrace]
  refine ⟨120022491584279941996207693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160029988779039922661610257 120022491584279941996207693)
  ·
    refine ⟨45008434344104978248577885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120022491584279941996207693 45008434344104978248577885)
    ·
      refine ⟨16878162879039366843216707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45008434344104978248577885 16878162879039366843216707)
      ·
        refine ⟨25317244318559050264825061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878162879039366843216707 25317244318559050264825061)
        ·
          refine ⟨4746983309729821924654699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25317244318559050264825061 4746983309729821924654699)
          ·
            refine ⟨7120474964594732886982049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746983309729821924654699 7120474964594732886982049)
            ·
              refine ⟨5340356223446049665236537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7120474964594732886982049 5340356223446049665236537)
              ·
                refine ⟨4005267167584537248927403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340356223446049665236537 4005267167584537248927403)
                ·
                  refine ⟨6007900751376805873391105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005267167584537248927403 6007900751376805873391105)
                  ·
                    refine ⟨4505925563532604405043329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007900751376805873391105 4505925563532604405043329)
                    ·
                      refine ⟨3379444172649453303782497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505925563532604405043329 3379444172649453303782497)
                      ·
                        rfl

theorem cell23_6581444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_6581444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581444 prefixEnd_6581444 := by exact prefixLift 6581444
  have htrace : WordTrace (prefixWord ++ tailWord_6581444) baseStart_6581444 baseEnd_6581444 := by
    simpa [prefixWord, tailWord_6581444, baseEnd_6581444] using wordTrace_append hprefix tailTrace_6581444
  have hstable : (prefixWord ++ tailWord_6581444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581444).length < 2 ^ (prefixWord ++ tailWord_6581444).sum := by decide
  have hdescent : baseEnd_6581444 < baseStart_6581444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581445 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6581445 : Nat := 118140960795 + 6581445 * 2 ^ 59
def prefixEnd_6581445 : Nat := 4983230072969 + 3 ^ 40 * 6581445 * 2
def baseEnd_6581445 : Nat := 3379444686130107799869991

theorem tailTrace_6581445 : CollatzResearch.WordTrace tailWord_6581445 prefixEnd_6581445 3379444686130107799869991 := by
  unfold tailWord_6581445
  simp only [CollatzResearch.WordTrace]
  refine ⟨240045019641556261163201789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160030013094370840775467859 240045019641556261163201789)
  ·
    refine ⟨90016882365583597936200671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240045019641556261163201789 90016882365583597936200671)
    ·
      refine ⟨135025323548375396904301007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90016882365583597936200671 135025323548375396904301007)
      ·
        refine ⟨202537985322563095356451511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135025323548375396904301007 202537985322563095356451511)
        ·
          refine ⟨303806977983844643034677267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202537985322563095356451511 303806977983844643034677267)
          ·
            refine ⟨455710466975766964552015901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303806977983844643034677267 455710466975766964552015901)
            ·
              refine ⟨170891425115912611707005963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455710466975766964552015901 170891425115912611707005963)
              ·
                refine ⟨256337137673868917560508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170891425115912611707005963 256337137673868917560508945)
                ·
                  refine ⟨192252853255401688170381709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256337137673868917560508945 192252853255401688170381709)
                  ·
                    refine ⟨72094819970775633063893141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192252853255401688170381709 72094819970775633063893141)
                    ·
                      refine ⟨3379444686130107799869991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72094819970775633063893141 3379444686130107799869991)
                      ·
                        rfl

theorem cell23_6581445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6581445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581445 prefixEnd_6581445 := by exact prefixLift 6581445
  have htrace : WordTrace (prefixWord ++ tailWord_6581445) baseStart_6581445 baseEnd_6581445 := by
    simpa [prefixWord, tailWord_6581445, baseEnd_6581445] using wordTrace_append hprefix tailTrace_6581445
  have hstable : (prefixWord ++ tailWord_6581445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581445).length < 2 ^ (prefixWord ++ tailWord_6581445).sum := by decide
  have hdescent : baseEnd_6581445 < baseStart_6581445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581449 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 8, 2, 2]
def baseStart_6581449 : Nat := 118140960795 + 6581449 * 2 ^ 59
def prefixEnd_6581449 : Nat := 4983230072969 + 3 ^ 40 * 6581449 * 2
def baseEnd_6581449 : Nat := 3379446740052725784219973

theorem tailTrace_6581449 : CollatzResearch.WordTrace tailWord_6581449 prefixEnd_6581449 3379446740052725784219973 := by
  unfold tailWord_6581449
  simp only [CollatzResearch.WordTrace]
  refine ⟨240045165533541769846347401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160030110355694513230898267 240045165533541769846347401)
  ·
    refine ⟨180033874150156327384760551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240045165533541769846347401 180033874150156327384760551)
    ·
      refine ⟨270050811225234491077140827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180033874150156327384760551 270050811225234491077140827)
      ·
        refine ⟨405076216837851736615711241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270050811225234491077140827 405076216837851736615711241)
        ·
          refine ⟨303807162628388802461783431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405076216837851736615711241 303807162628388802461783431)
          ·
            refine ⟨455710743942583203692675147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303807162628388802461783431 455710743942583203692675147)
            ·
              refine ⟨683566115913874805539012721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455710743942583203692675147 683566115913874805539012721)
              ·
                refine ⟨512674586935406104154259541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683566115913874805539012721 512674586935406104154259541)
                ·
                  refine ⟨6007905315649290283057729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 512674586935406104154259541 6007905315649290283057729)
                  ·
                    refine ⟨4505928986736967712293297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007905315649290283057729 4505928986736967712293297)
                    ·
                      refine ⟨3379446740052725784219973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505928986736967712293297 3379446740052725784219973)
                      ·
                        rfl

theorem cell23_6581449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2, 2].length) (baseStart_6581449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581449 prefixEnd_6581449 := by exact prefixLift 6581449
  have htrace : WordTrace (prefixWord ++ tailWord_6581449) baseStart_6581449 baseEnd_6581449 := by
    simpa [prefixWord, tailWord_6581449, baseEnd_6581449] using wordTrace_append hprefix tailTrace_6581449
  have hstable : (prefixWord ++ tailWord_6581449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581449).length < 2 ^ (prefixWord ++ tailWord_6581449).sum := by decide
  have hdescent : baseEnd_6581449 < baseStart_6581449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581472 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 7]
def baseStart_6581472 : Nat := 118140960795 + 6581472 * 2 ^ 59
def prefixEnd_6581472 : Nat := 4983230072969 + 3 ^ 40 * 6581472 * 2
def baseEnd_6581472 : Nat := 375495394456419910470263

theorem tailTrace_6581472 : CollatzResearch.WordTrace tailWord_6581472 prefixEnd_6581472 375495394456419910470263 := by
  unfold tailWord_6581472
  simp only [CollatzResearch.WordTrace]
  refine ⟨120023002206229222387217335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160030669608305629849623113 120023002206229222387217335)
  ·
    refine ⟨180034503309343833580826003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120023002206229222387217335 180034503309343833580826003)
    ·
      refine ⟨270051754964015750371239005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180034503309343833580826003 270051754964015750371239005)
      ·
        refine ⟨101269408111505906389214627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270051754964015750371239005 101269408111505906389214627)
        ·
          refine ⟨151904112167258859583821941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101269408111505906389214627 151904112167258859583821941)
          ·
            refine ⟨14241010515680518085983307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151904112167258859583821941 14241010515680518085983307)
            ·
              refine ⟨21361515773520777128974961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241010515680518085983307 21361515773520777128974961)
              ·
                refine ⟨16021136830140582846731221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21361515773520777128974961 16021136830140582846731221)
                ·
                  refine ⟨375495394456419910470263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16021136830140582846731221 375495394456419910470263)
                  ·
                    rfl

theorem cell23_6581472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_6581472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581472 prefixEnd_6581472 := by exact prefixLift 6581472
  have htrace : WordTrace (prefixWord ++ tailWord_6581472) baseStart_6581472 baseEnd_6581472 := by
    simpa [prefixWord, tailWord_6581472, baseEnd_6581472] using wordTrace_append hprefix tailTrace_6581472
  have hstable : (prefixWord ++ tailWord_6581472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581472).length < 2 ^ (prefixWord ++ tailWord_6581472).sum := by decide
  have hdescent : baseEnd_6581472 < baseStart_6581472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581500 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_6581500 : Nat := 118140960795 + 6581500 * 2 ^ 59
def prefixEnd_6581500 : Nat := 4983230072969 + 3 ^ 40 * 6581500 * 2
def baseEnd_6581500 : Nat := 3379472927566105084682239

theorem tailTrace_6581500 : CollatzResearch.WordTrace tailWord_6581500 prefixEnd_6581500 3379472927566105084682239 := by
  unfold tailWord_6581500
  simp only [CollatzResearch.WordTrace]
  refine ⟨120023512828178502778226977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160031350437571337037635969 120023512828178502778226977)
  ·
    refine ⟨90017634621133877083670233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120023512828178502778226977 90017634621133877083670233)
    ·
      refine ⟨67513225965850407812752675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90017634621133877083670233 67513225965850407812752675)
      ·
        refine ⟨101269838948775611719129013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67513225965850407812752675 101269838948775611719129013)
        ·
          refine ⟨9494047401447713598668345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101269838948775611719129013 9494047401447713598668345)
          ·
            refine ⟨7120535551085785199001259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9494047401447713598668345 7120535551085785199001259)
            ·
              refine ⟨10680803326628677798501889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120535551085785199001259 10680803326628677798501889)
              ·
                refine ⟨8010602494971508348876417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10680803326628677798501889 8010602494971508348876417)
                ·
                  refine ⟨6007951871228631261657313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8010602494971508348876417 6007951871228631261657313)
                  ·
                    refine ⟨4505963903421473446242985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007951871228631261657313 4505963903421473446242985)
                    ·
                      refine ⟨3379472927566105084682239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4505963903421473446242985 3379472927566105084682239)
                      ·
                        rfl

theorem cell23_6581500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_6581500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581500 prefixEnd_6581500 := by exact prefixLift 6581500
  have htrace : WordTrace (prefixWord ++ tailWord_6581500) baseStart_6581500 baseEnd_6581500 := by
    simpa [prefixWord, tailWord_6581500, baseEnd_6581500] using wordTrace_append hprefix tailTrace_6581500
  have hstable : (prefixWord ++ tailWord_6581500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581500).length < 2 ^ (prefixWord ++ tailWord_6581500).sum := by decide
  have hdescent : baseEnd_6581500 < baseStart_6581500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581506 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6581506 : Nat := 118140960795 + 6581506 * 2 ^ 59
def prefixEnd_6581506 : Nat := 4983230072969 + 3 ^ 40 * 6581506 * 2
def baseEnd_6581506 : Nat := 375497334272225784578579

theorem tailTrace_6581506 : CollatzResearch.WordTrace tailWord_6581506 prefixEnd_6581506 375497334272225784578579 := by
  unfold tailWord_6581506
  simp only [CollatzResearch.WordTrace]
  refine ⟨60011811123583817145293093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160031496329556845720781581 60011811123583817145293093)
  ·
    refine ⟨11252214585671965714742455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60011811123583817145293093 11252214585671965714742455)
    ·
      refine ⟨16878321878507948572113683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252214585671965714742455 16878321878507948572113683)
      ·
        refine ⟨25317482817761922858170525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878321878507948572113683 25317482817761922858170525)
        ·
          refine ⟨9494056056660721071813947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25317482817761922858170525 9494056056660721071813947)
          ·
            refine ⟨14241084084991081607720921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494056056660721071813947 14241084084991081607720921)
            ·
              refine ⟨10680813063743311205790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14241084084991081607720921 10680813063743311205790691)
              ·
                refine ⟨16021219595614966808686037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680813063743311205790691 16021219595614966808686037)
                ·
                  refine ⟨375497334272225784578579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16021219595614966808686037 375497334272225784578579)
                  ·
                    rfl

theorem cell23_6581506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6581506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581506 prefixEnd_6581506 := by exact prefixLift 6581506
  have htrace : WordTrace (prefixWord ++ tailWord_6581506) baseStart_6581506 baseEnd_6581506 := by
    simpa [prefixWord, tailWord_6581506, baseEnd_6581506] using wordTrace_append hprefix tailTrace_6581506
  have hstable : (prefixWord ++ tailWord_6581506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581506).length < 2 ^ (prefixWord ++ tailWord_6581506).sum := by decide
  have hdescent : baseEnd_6581506 < baseStart_6581506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581556 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6581556 : Nat := 118140960795 + 6581556 * 2 ^ 59
def prefixEnd_6581556 : Nat := 4983230072969 + 3 ^ 40 * 6581556 * 2
def baseEnd_6581556 : Nat := 3379501682482756865581981

theorem tailTrace_6581556 : CollatzResearch.WordTrace tailWord_6581556 prefixEnd_6581556 3379501682482756865581981 := by
  unfold tailWord_6581556
  simp only [CollatzResearch.WordTrace]
  refine ⟨120024534072077063560246261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160032712096102751413661681 120024534072077063560246261)
  ·
    refine ⟨11252300069257224708773087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120024534072077063560246261 11252300069257224708773087)
    ·
      refine ⟨16878450103885837063159631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252300069257224708773087 16878450103885837063159631)
      ·
        refine ⟨25317675155828755594739447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878450103885837063159631 25317675155828755594739447)
        ·
          refine ⟨37976512733743133392109171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25317675155828755594739447 37976512733743133392109171)
          ·
            refine ⟨56964769100614700088163757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37976512733743133392109171 56964769100614700088163757)
            ·
              refine ⟨21361788412730512533061409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56964769100614700088163757 21361788412730512533061409)
              ·
                refine ⟨16021341309547884399796057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21361788412730512533061409 16021341309547884399796057)
                ·
                  refine ⟨12016005982160913299847043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16021341309547884399796057 12016005982160913299847043)
                  ·
                    refine ⟨18024008973241369949770565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12016005982160913299847043 18024008973241369949770565)
                    ·
                      refine ⟨3379501682482756865581981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18024008973241369949770565 3379501682482756865581981)
                      ·
                        rfl

theorem cell23_6581556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6581556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581556 prefixEnd_6581556 := by exact prefixLift 6581556
  have htrace : WordTrace (prefixWord ++ tailWord_6581556) baseStart_6581556 baseEnd_6581556 := by
    simpa [prefixWord, tailWord_6581556, baseEnd_6581556] using wordTrace_append hprefix tailTrace_6581556
  have hstable : (prefixWord ++ tailWord_6581556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581556).length < 2 ^ (prefixWord ++ tailWord_6581556).sum := by decide
  have hdescent : baseEnd_6581556 < baseStart_6581556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581562 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_6581562 : Nat := 118140960795 + 6581562 * 2 ^ 59
def prefixEnd_6581562 : Nat := 4983230072969 + 3 ^ 40 * 6581562 * 2
def baseEnd_6581562 : Nat := 375500529262964871345217

theorem tailTrace_6581562 : CollatzResearch.WordTrace tailWord_6581562 prefixEnd_6581562 375500529262964871345217 := by
  unfold tailWord_6581562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60012321745533097536302735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160032857988088260096807293 60012321745533097536302735)
  ·
    refine ⟨90018482618299646304454103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60012321745533097536302735 90018482618299646304454103)
    ·
      refine ⟨135027723927449469456681155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90018482618299646304454103 135027723927449469456681155)
      ·
        refine ⟨202541585891174204185021733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135027723927449469456681155 202541585891174204185021733)
        ·
          refine ⟨37976547354595163284691575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202541585891174204185021733 37976547354595163284691575)
          ·
            refine ⟨56964821031892744927037363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37976547354595163284691575 56964821031892744927037363)
            ·
              refine ⟨85447231547839117390556045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56964821031892744927037363 85447231547839117390556045)
              ·
                refine ⟨32042711830439669021458517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85447231547839117390556045 32042711830439669021458517)
                ·
                  refine ⟨375500529262964871345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32042711830439669021458517 375500529262964871345217)
                  ·
                    rfl

theorem cell23_6581562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_6581562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581562 prefixEnd_6581562 := by exact prefixLift 6581562
  have htrace : WordTrace (prefixWord ++ tailWord_6581562) baseStart_6581562 baseEnd_6581562 := by
    simpa [prefixWord, tailWord_6581562, baseEnd_6581562] using wordTrace_append hprefix tailTrace_6581562
  have hstable : (prefixWord ++ tailWord_6581562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581562).length < 2 ^ (prefixWord ++ tailWord_6581562).sum := by decide
  have hdescent : baseEnd_6581562 < baseStart_6581562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581616 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2]
def baseStart_6581616 : Nat := 118140960795 + 6581616 * 2 ^ 59
def prefixEnd_6581616 : Nat := 4983230072969 + 3 ^ 40 * 6581616 * 2
def baseEnd_6581616 : Nat := 3379532491322026630831705

theorem tailTrace_6581616 : CollatzResearch.WordTrace tailWord_6581616 prefixEnd_6581616 3379532491322026630831705 := by
  unfold tailWord_6581616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120025628261968378683838351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160034171015957838245117801 120025628261968378683838351)
  ·
    refine ⟨180038442392952568025757527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120025628261968378683838351 180038442392952568025757527)
    ·
      refine ⟨270057663589428852038636291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180038442392952568025757527 270057663589428852038636291)
      ·
        refine ⟨405086495384143278057954437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270057663589428852038636291 405086495384143278057954437)
        ·
          refine ⟨75953717884526864635866457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405086495384143278057954437 75953717884526864635866457)
          ·
            refine ⟨56965288413395148476899843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75953717884526864635866457 56965288413395148476899843)
            ·
              refine ⟨85447932620092722715349765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56965288413395148476899843 85447932620092722715349765)
              ·
                refine ⟨16021487366267385509128081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85447932620092722715349765 16021487366267385509128081)
                ·
                  refine ⟨12016115524700539131846061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16021487366267385509128081 12016115524700539131846061)
                  ·
                    refine ⟨4506043321762702174442273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12016115524700539131846061 4506043321762702174442273)
                    ·
                      refine ⟨3379532491322026630831705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506043321762702174442273 3379532491322026630831705)
                      ·
                        rfl

theorem cell23_6581616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2].length) (baseStart_6581616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581616 prefixEnd_6581616 := by exact prefixLift 6581616
  have htrace : WordTrace (prefixWord ++ tailWord_6581616) baseStart_6581616 baseEnd_6581616 := by
    simpa [prefixWord, tailWord_6581616, baseEnd_6581616] using wordTrace_append hprefix tailTrace_6581616
  have hstable : (prefixWord ++ tailWord_6581616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581616).length < 2 ^ (prefixWord ++ tailWord_6581616).sum := by decide
  have hdescent : baseEnd_6581616 < baseStart_6581616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581623 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_6581623 : Nat := 118140960795 + 6581623 * 2 ^ 59
def prefixEnd_6581623 : Nat := 4983230072969 + 3 ^ 40 * 6581623 * 2
def baseEnd_6581623 : Nat := 3379536085686608103444173

theorem tailTrace_6581623 : CollatzResearch.WordTrace tailWord_6581623 prefixEnd_6581623 3379536085686608103444173 := by
  unfold tailWord_6581623
  simp only [CollatzResearch.WordTrace]
  refine ⟨240051511834911397563181523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160034341223274265042121015 240051511834911397563181523)
  ·
    refine ⟨360077267752367096344772285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240051511834911397563181523 360077267752367096344772285)
    ·
      refine ⟨135028975407137661129289607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360077267752367096344772285 135028975407137661129289607)
      ·
        refine ⟨202543463110706491693934411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135028975407137661129289607 202543463110706491693934411)
        ·
          refine ⟨303815194666059737540901617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202543463110706491693934411 303815194666059737540901617)
          ·
            refine ⟨227861395999544803155676213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303815194666059737540901617 227861395999544803155676213)
            ·
              refine ⟨21362005874957325295844645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227861395999544803155676213 21362005874957325295844645)
              ·
                refine ⟨4005376101554498492970871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21362005874957325295844645 4005376101554498492970871)
                ·
                  refine ⟨6008064152331747739456307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005376101554498492970871 6008064152331747739456307)
                  ·
                    refine ⟨9012096228497621609184461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008064152331747739456307 9012096228497621609184461)
                    ·
                      refine ⟨3379536085686608103444173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012096228497621609184461 3379536085686608103444173)
                      ·
                        rfl

theorem cell23_6581623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_6581623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581623 prefixEnd_6581623 := by exact prefixLift 6581623
  have htrace : WordTrace (prefixWord ++ tailWord_6581623) baseStart_6581623 baseEnd_6581623 := by
    simpa [prefixWord, tailWord_6581623, baseEnd_6581623] using wordTrace_append hprefix tailTrace_6581623
  have hstable : (prefixWord ++ tailWord_6581623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581623).length < 2 ^ (prefixWord ++ tailWord_6581623).sum := by decide
  have hdescent : baseEnd_6581623 < baseStart_6581623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581629 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_6581629 : Nat := 118140960795 + 6581629 * 2 ^ 59
def prefixEnd_6581629 : Nat := 4983230072969 + 3 ^ 40 * 6581629 * 2
def baseEnd_6581629 : Nat := 3379539166570535079969145

theorem tailTrace_6581629 : CollatzResearch.WordTrace tailWord_6581629 prefixEnd_6581629 3379539166570535079969145 := by
  unfold tailWord_6581629
  simp only [CollatzResearch.WordTrace]
  refine ⟨240051730672889660587899941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160034487115259773725266627 240051730672889660587899941)
  ·
    refine ⟨45009699501166811360231239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240051730672889660587899941 45009699501166811360231239)
    ·
      refine ⟨67514549251750217040346859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45009699501166811360231239 67514549251750217040346859)
      ·
        refine ⟨101271823877625325560520289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67514549251750217040346859 101271823877625325560520289)
        ·
          refine ⟨75953867908218994170390217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101271823877625325560520289 75953867908218994170390217)
          ·
            refine ⟨56965400931164245627792663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75953867908218994170390217 56965400931164245627792663)
            ·
              refine ⟨85448101396746368441688995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56965400931164245627792663 85448101396746368441688995)
              ·
                refine ⟨128172152095119552662533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85448101396746368441688995 128172152095119552662533493)
                ·
                  refine ⟨12016139258917458062112515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128172152095119552662533493 12016139258917458062112515)
                  ·
                    refine ⟨18024208888376187093168773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12016139258917458062112515 18024208888376187093168773)
                    ·
                      refine ⟨3379539166570535079969145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18024208888376187093168773 3379539166570535079969145)
                      ·
                        rfl

theorem cell23_6581629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_6581629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581629 prefixEnd_6581629 := by exact prefixLift 6581629
  have htrace : WordTrace (prefixWord ++ tailWord_6581629) baseStart_6581629 baseEnd_6581629 := by
    simpa [prefixWord, tailWord_6581629, baseEnd_6581629] using wordTrace_append hprefix tailTrace_6581629
  have hstable : (prefixWord ++ tailWord_6581629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581629).length < 2 ^ (prefixWord ++ tailWord_6581629).sum := by decide
  have hdescent : baseEnd_6581629 < baseStart_6581629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581639 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 6]
def baseStart_6581639 : Nat := 118140960795 + 6581639 * 2 ^ 59
def prefixEnd_6581639 : Nat := 4983230072969 + 3 ^ 40 * 6581639 * 2
def baseEnd_6581639 : Nat := 1126514767125693346948033

theorem tailTrace_6581639 : CollatzResearch.WordTrace tailWord_6581639 prefixEnd_6581639 1126514767125693346948033 := by
  unfold tailWord_6581639
  simp only [CollatzResearch.WordTrace]
  refine ⟨240052095402853432295763971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160034730268568954863842647 240052095402853432295763971)
  ·
    refine ⟨360078143104280148443645957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240052095402853432295763971 360078143104280148443645957)
    ·
      refine ⟨67514651832052527833183617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360078143104280148443645957 67514651832052527833183617)
      ·
        refine ⟨50635988874039395874887713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67514651832052527833183617 50635988874039395874887713)
        ·
          refine ⟨37976991655529546906165785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50635988874039395874887713 37976991655529546906165785)
          ·
            refine ⟨28482743741647160179624339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37976991655529546906165785 28482743741647160179624339)
            ·
              refine ⟨42724115612470740269436509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28482743741647160179624339 42724115612470740269436509)
              ·
                refine ⟨16021543354676527601038691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42724115612470740269436509 16021543354676527601038691)
                ·
                  refine ⟨24032315032014791401558037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021543354676527601038691 24032315032014791401558037)
                  ·
                    refine ⟨1126514767125693346948033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24032315032014791401558037 1126514767125693346948033)
                    ·
                      rfl

theorem cell23_6581639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_6581639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581639 prefixEnd_6581639 := by exact prefixLift 6581639
  have htrace : WordTrace (prefixWord ++ tailWord_6581639) baseStart_6581639 baseEnd_6581639 := by
    simpa [prefixWord, tailWord_6581639, baseEnd_6581639] using wordTrace_append hprefix tailTrace_6581639
  have hstable : (prefixWord ++ tailWord_6581639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581639).length < 2 ^ (prefixWord ++ tailWord_6581639).sum := by decide
  have hdescent : baseEnd_6581639 < baseStart_6581639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581650 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6581650 : Nat := 118140960795 + 6581650 * 2 ^ 59
def prefixEnd_6581650 : Nat := 4983230072969 + 3 ^ 40 * 6581650 * 2
def baseEnd_6581650 : Nat := 3379549949664279497806549

theorem tailTrace_6581650 : CollatzResearch.WordTrace tailWord_6581650 prefixEnd_6581650 3379549949664279497806549 := by
  unfold tailWord_6581650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60013124151453395293603601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160034997737209054116276269 60013124151453395293603601)
  ·
    refine ⟨45009843113590046470202701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60013124151453395293603601 45009843113590046470202701)
    ·
      refine ⟨16878691167596267426326013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45009843113590046470202701 16878691167596267426326013)
      ·
        refine ⟨6329509187848600284872255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16878691167596267426326013 6329509187848600284872255)
        ·
          refine ⟨9494263781772900427308383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329509187848600284872255 9494263781772900427308383)
          ·
            refine ⟨14241395672659350640962575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494263781772900427308383 14241395672659350640962575)
            ·
              refine ⟨21362093508989025961443863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241395672659350640962575 21362093508989025961443863)
              ·
                refine ⟨32043140263483538942165795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21362093508989025961443863 32043140263483538942165795)
                ·
                  refine ⟨48064710395225308413248693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32043140263483538942165795 48064710395225308413248693)
                  ·
                    refine ⟨4506066599552372663742065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48064710395225308413248693 4506066599552372663742065)
                    ·
                      refine ⟨3379549949664279497806549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506066599552372663742065 3379549949664279497806549)
                      ·
                        rfl

theorem cell23_6581650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6581650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581650 prefixEnd_6581650 := by exact prefixLift 6581650
  have htrace : WordTrace (prefixWord ++ tailWord_6581650) baseStart_6581650 baseEnd_6581650 := by
    simpa [prefixWord, tailWord_6581650, baseEnd_6581650] using wordTrace_append hprefix tailTrace_6581650
  have hstable : (prefixWord ++ tailWord_6581650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581650).length < 2 ^ (prefixWord ++ tailWord_6581650).sum := by decide
  have hdescent : baseEnd_6581650 < baseStart_6581650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581663 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6581663 : Nat := 118140960795 + 6581663 * 2 ^ 59
def prefixEnd_6581663 : Nat := 4983230072969 + 3 ^ 40 * 6581663 * 2
def baseEnd_6581663 : Nat := 3379556624912787946943989

theorem tailTrace_6581663 : CollatzResearch.WordTrace tailWord_6581663 prefixEnd_6581663 3379556624912787946943989 := by
  unfold tailWord_6581663
  simp only [CollatzResearch.WordTrace]
  refine ⟨240052970754766484394637643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160035313836510989596425095 240052970754766484394637643)
  ·
    refine ⟨360079456132149726591956465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240052970754766484394637643 360079456132149726591956465)
    ·
      refine ⟨270059592099112294943967349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360079456132149726591956465 270059592099112294943967349)
      ·
        refine ⟨25318086759291777650996939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270059592099112294943967349 25318086759291777650996939)
        ·
          refine ⟨37977130138937666476495409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25318086759291777650996939 37977130138937666476495409)
          ·
            refine ⟨28482847604203249857371557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37977130138937666476495409 28482847604203249857371557)
            ·
              refine ⟨5340533925788109348257167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28482847604203249857371557 5340533925788109348257167)
              ·
                refine ⟨8010800888682164022385751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340533925788109348257167 8010800888682164022385751)
                ·
                  refine ⟨12016201333023246033578627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8010800888682164022385751 12016201333023246033578627)
                  ·
                    refine ⟨18024301999534869050367941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12016201333023246033578627 18024301999534869050367941)
                    ·
                      refine ⟨3379556624912787946943989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18024301999534869050367941 3379556624912787946943989)
                      ·
                        rfl

theorem cell23_6581663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6581663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581663 prefixEnd_6581663 := by exact prefixLift 6581663
  have htrace : WordTrace (prefixWord ++ tailWord_6581663) baseStart_6581663 baseEnd_6581663 := by
    simpa [prefixWord, tailWord_6581663, baseEnd_6581663] using wordTrace_append hprefix tailTrace_6581663
  have hstable : (prefixWord ++ tailWord_6581663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581663).length < 2 ^ (prefixWord ++ tailWord_6581663).sum := by decide
  have hdescent : baseEnd_6581663 < baseStart_6581663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581679 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_6581679 : Nat := 118140960795 + 6581679 * 2 ^ 59
def prefixEnd_6581679 : Nat := 4983230072969 + 3 ^ 40 * 6581679 * 2
def baseEnd_6581679 : Nat := 3379564840603259884343915

theorem tailTrace_6581679 : CollatzResearch.WordTrace tailWord_6581679 prefixEnd_6581679 3379564840603259884343915 := by
  unfold tailWord_6581679
  simp only [CollatzResearch.WordTrace]
  refine ⟨240053554322708519127220091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160035702881805679418146727 240053554322708519127220091)
  ·
    refine ⟨360080331484062778690830137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240053554322708519127220091 360080331484062778690830137)
    ·
      refine ⟨270060248613047084018122603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360080331484062778690830137 270060248613047084018122603)
      ·
        refine ⟨405090372919570626027183905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270060248613047084018122603 405090372919570626027183905)
        ·
          refine ⟨303817779689677969520387929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405090372919570626027183905 303817779689677969520387929)
          ·
            refine ⟨227863334767258477140290947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303817779689677969520387929 227863334767258477140290947)
            ·
              refine ⟨341795002150887715710436421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227863334767258477140290947 341795002150887715710436421)
              ·
                refine ⟨64086562903291446695706829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341795002150887715710436421 64086562903291446695706829)
                ·
                  refine ⟨24032461088734292510890061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64086562903291446695706829 24032461088734292510890061)
                  ·
                    refine ⟨9012172908275359691583773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24032461088734292510890061 9012172908275359691583773)
                    ·
                      refine ⟨3379564840603259884343915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012172908275359691583773 3379564840603259884343915)
                      ·
                        rfl

theorem cell23_6581679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_6581679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581679 prefixEnd_6581679 := by exact prefixLift 6581679
  have htrace : WordTrace (prefixWord ++ tailWord_6581679) baseStart_6581679 baseEnd_6581679 := by
    simpa [prefixWord, tailWord_6581679, baseEnd_6581679] using wordTrace_append hprefix tailTrace_6581679
  have hstable : (prefixWord ++ tailWord_6581679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581679).length < 2 ^ (prefixWord ++ tailWord_6581679).sum := by decide
  have hdescent : baseEnd_6581679 < baseStart_6581679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581696 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_6581696 : Nat := 118140960795 + 6581696 * 2 ^ 59
def prefixEnd_6581696 : Nat := 4983230072969 + 3 ^ 40 * 6581696 * 2
def baseEnd_6581696 : Nat := 3379573569774386317831337

theorem tailTrace_6581696 : CollatzResearch.WordTrace tailWord_6581696 prefixEnd_6581696 3379573569774386317831337 := by
  unfold tailWord_6581696
  simp only [CollatzResearch.WordTrace]
  refine ⟨120027087181823465515294471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160036116242431287353725961 120027087181823465515294471)
  ·
    refine ⟨180040630772735198272941707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120027087181823465515294471 180040630772735198272941707)
    ·
      refine ⟨270060946159102797409412561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180040630772735198272941707 270060946159102797409412561)
      ·
        refine ⟨202545709619327098057059421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270060946159102797409412561 202545709619327098057059421)
        ·
          refine ⟨75954641107247661771397283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202545709619327098057059421 75954641107247661771397283)
          ·
            refine ⟨113931961660871492657095925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75954641107247661771397283 113931961660871492657095925)
            ·
              refine ⟨10681121405706702436602743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113931961660871492657095925 10681121405706702436602743)
              ·
                refine ⟨16021682108560053654904115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10681121405706702436602743 16021682108560053654904115)
                ·
                  refine ⟨24032523162840080482356173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021682108560053654904115 24032523162840080482356173)
                  ·
                    refine ⟨9012196186065030180883565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24032523162840080482356173 9012196186065030180883565)
                    ·
                      refine ⟨3379573569774386317831337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012196186065030180883565 3379573569774386317831337)
                      ·
                        rfl

theorem cell23_6581696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_6581696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581696 prefixEnd_6581696 := by exact prefixLift 6581696
  have htrace : WordTrace (prefixWord ++ tailWord_6581696) baseStart_6581696 baseEnd_6581696 := by
    simpa [prefixWord, tailWord_6581696, baseEnd_6581696] using wordTrace_append hprefix tailTrace_6581696
  have hstable : (prefixWord ++ tailWord_6581696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581696).length < 2 ^ (prefixWord ++ tailWord_6581696).sum := by decide
  have hdescent : baseEnd_6581696 < baseStart_6581696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581700 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6581700 : Nat := 118140960795 + 6581700 * 2 ^ 59
def prefixEnd_6581700 : Nat := 4983230072969 + 3 ^ 40 * 6581700 * 2
def baseEnd_6581700 : Nat := 3379575623697004302181319

theorem tailTrace_6581700 : CollatzResearch.WordTrace tailWord_6581700 prefixEnd_6581700 3379575623697004302181319 := by
  unfold tailWord_6581700
  simp only [CollatzResearch.WordTrace]
  refine ⟨120027160127816219856867277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160036213503754959809156369 120027160127816219856867277)
  ·
    refine ⟨45010185047931082446325229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120027160127816219856867277 45010185047931082446325229)
    ·
      refine ⟨16878819392974155917371961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45010185047931082446325229 16878819392974155917371961)
      ·
        refine ⟨12659114544730616938028971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16878819392974155917371961 12659114544730616938028971)
        ·
          refine ⟨18988671817095925407043457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12659114544730616938028971 18988671817095925407043457)
          ·
            refine ⟨14241503862821944055282593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18988671817095925407043457 14241503862821944055282593)
            ·
              refine ⟨10681127897116458041461945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14241503862821944055282593 10681127897116458041461945)
              ·
                refine ⟨8010845922837343531096459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10681127897116458041461945 8010845922837343531096459)
                ·
                  refine ⟨12016268884256015296644689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8010845922837343531096459 12016268884256015296644689)
                  ·
                    refine ⟨9012201663192011472483517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12016268884256015296644689 9012201663192011472483517)
                    ·
                      refine ⟨3379575623697004302181319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012201663192011472483517 3379575623697004302181319)
                      ·
                        rfl

theorem cell23_6581700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6581700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581700 prefixEnd_6581700 := by exact prefixLift 6581700
  have htrace : WordTrace (prefixWord ++ tailWord_6581700) baseStart_6581700 baseEnd_6581700 := by
    simpa [prefixWord, tailWord_6581700, baseEnd_6581700] using wordTrace_append hprefix tailTrace_6581700
  have hstable : (prefixWord ++ tailWord_6581700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581700).length < 2 ^ (prefixWord ++ tailWord_6581700).sum := by decide
  have hdescent : baseEnd_6581700 < baseStart_6581700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581786 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_6581786 : Nat := 118140960795 + 6581786 * 2 ^ 59
def prefixEnd_6581786 : Nat := 4983230072969 + 3 ^ 40 * 6581786 * 2
def baseEnd_6581786 : Nat := 3379619783033290965705923

theorem tailTrace_6581786 : CollatzResearch.WordTrace tailWord_6581786 prefixEnd_6581786 3379619783033290965705923 := by
  unfold tailWord_6581786
  simp only [CollatzResearch.WordTrace]
  refine ⟨60014364233330219100341303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160038304622213917600910141 60014364233330219100341303)
  ·
    refine ⟨90021546349995328650511955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60014364233330219100341303 90021546349995328650511955)
    ·
      refine ⟨135032319524992992975767933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90021546349995328650511955 135032319524992992975767933)
      ·
        refine ⟨50637119821872372365912975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135032319524992992975767933 50637119821872372365912975)
        ·
          refine ⟨75955679732808558548869463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50637119821872372365912975 75955679732808558548869463)
          ·
            refine ⟨113933519599212837823304195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75955679732808558548869463 113933519599212837823304195)
            ·
              refine ⟨170900279398819256734956293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113933519599212837823304195 170900279398819256734956293)
              ·
                refine ⟨32043802387278610637804305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170900279398819256734956293 32043802387278610637804305)
                ·
                  refine ⟨24032851790458957978353229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32043802387278610637804305 24032851790458957978353229)
                  ·
                    refine ⟨9012319421422109241882461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24032851790458957978353229 9012319421422109241882461)
                    ·
                      refine ⟨3379619783033290965705923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012319421422109241882461 3379619783033290965705923)
                      ·
                        rfl

theorem cell23_6581786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_6581786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581786 prefixEnd_6581786 := by exact prefixLift 6581786
  have htrace : WordTrace (prefixWord ++ tailWord_6581786) baseStart_6581786 baseEnd_6581786 := by
    simpa [prefixWord, tailWord_6581786, baseEnd_6581786] using wordTrace_append hprefix tailTrace_6581786
  have hstable : (prefixWord ++ tailWord_6581786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581786).length < 2 ^ (prefixWord ++ tailWord_6581786).sum := by decide
  have hdescent : baseEnd_6581786 < baseStart_6581786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581793 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 5]
def baseStart_6581793 : Nat := 118140960795 + 6581793 * 2 ^ 59
def prefixEnd_6581793 : Nat := 4983230072969 + 3 ^ 40 * 6581793 * 2
def baseEnd_6581793 : Nat := 375513708599763604257599

theorem tailTrace_6581793 : CollatzResearch.WordTrace tailWord_6581793 prefixEnd_6581793 375513708599763604257599 := by
  unfold tailWord_6581793
  simp only [CollatzResearch.WordTrace]
  refine ⟨240057712244295516596870033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160038474829530344397913355 240057712244295516596870033)
  ·
    refine ⟨180043284183221637447652525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240057712244295516596870033 180043284183221637447652525)
    ·
      refine ⟨67516231568708114042869697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180043284183221637447652525 67516231568708114042869697)
      ·
        refine ⟨50637173676531085532152273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67516231568708114042869697 50637173676531085532152273)
        ·
          refine ⟨37977880257398314149114205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50637173676531085532152273 37977880257398314149114205)
          ·
            refine ⟨14241705096524367805917827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37977880257398314149114205 14241705096524367805917827)
            ·
              refine ⟨21362557644786551708876741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14241705096524367805917827 21362557644786551708876741)
              ·
                refine ⟨4005479558397478445414389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21362557644786551708876741 4005479558397478445414389)
                ·
                  refine ⟨375513708599763604257599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4005479558397478445414389 375513708599763604257599)
                  ·
                    rfl

theorem cell23_6581793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 5].length) (baseStart_6581793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581793 prefixEnd_6581793 := by exact prefixLift 6581793
  have htrace : WordTrace (prefixWord ++ tailWord_6581793) baseStart_6581793 baseEnd_6581793 := by
    simpa [prefixWord, tailWord_6581793, baseEnd_6581793] using wordTrace_append hprefix tailTrace_6581793
  have hstable : (prefixWord ++ tailWord_6581793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581793).length < 2 ^ (prefixWord ++ tailWord_6581793).sum := by decide
  have hdescent : baseEnd_6581793 < baseStart_6581793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581823 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 2, 5]
def baseStart_6581823 : Nat := 118140960795 + 6581823 * 2 ^ 59
def prefixEnd_6581823 : Nat := 4983230072969 + 3 ^ 40 * 6581823 * 2
def baseEnd_6581823 : Nat := 1126546260605835773647751

theorem tailTrace_6581823 : CollatzResearch.WordTrace tailWord_6581823 prefixEnd_6581823 1126546260605835773647751 := by
  unfold tailWord_6581823
  simp only [CollatzResearch.WordTrace]
  refine ⟨240058806434186831720462123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160039204289457887813641415 240058806434186831720462123)
  ·
    refine ⟨360088209651280247580693185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240058806434186831720462123 360088209651280247580693185)
    ·
      refine ⟨270066157238460185685519889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360088209651280247580693185 270066157238460185685519889)
      ·
        refine ⟨202549617928845139264139917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270066157238460185685519889 202549617928845139264139917)
        ·
          refine ⟨75956106723316927224052469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202549617928845139264139917 75956106723316927224052469)
          ·
            refine ⟨7120885005310961927254919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75956106723316927224052469 7120885005310961927254919)
            ·
              refine ⟨10681327507966442890882379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120885005310961927254919 10681327507966442890882379)
              ·
                refine ⟨16021991261949664336323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10681327507966442890882379 16021991261949664336323569)
                ·
                  refine ⟨12016493446462248252242677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16021991261949664336323569 12016493446462248252242677)
                  ·
                    refine ⟨1126546260605835773647751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12016493446462248252242677 1126546260605835773647751)
                    ·
                      rfl

theorem cell23_6581823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_6581823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581823 prefixEnd_6581823 := by exact prefixLift 6581823
  have htrace : WordTrace (prefixWord ++ tailWord_6581823) baseStart_6581823 baseEnd_6581823 := by
    simpa [prefixWord, tailWord_6581823, baseEnd_6581823] using wordTrace_append hprefix tailTrace_6581823
  have hstable : (prefixWord ++ tailWord_6581823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581823).length < 2 ^ (prefixWord ++ tailWord_6581823).sum := by decide
  have hdescent : baseEnd_6581823 < baseStart_6581823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581936 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_6581936 : Nat := 118140960795 + 6581936 * 2 ^ 59
def prefixEnd_6581936 : Nat := 4983230072969 + 3 ^ 40 * 6581936 * 2
def baseEnd_6581936 : Nat := 3379696805131465378830233

theorem tailTrace_6581936 : CollatzResearch.WordTrace tailWord_6581936 prefixEnd_6581936 3379696805131465378830233 := by
  unfold tailWord_6581936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120031463941388726009662831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160041951921851634679550441 120031463941388726009662831)
  ·
    refine ⟨180047195912083089014494247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120031463941388726009662831 180047195912083089014494247)
    ·
      refine ⟨270070793868124633521741371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180047195912083089014494247 270070793868124633521741371)
      ·
        refine ⟨405106190802186950282612057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270070793868124633521741371 405106190802186950282612057)
        ·
          refine ⟨303829643101640212711959043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405106190802186950282612057 303829643101640212711959043)
          ·
            refine ⟨455744464652460319067938565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303829643101640212711959043 455744464652460319067938565)
            ·
              refine ⟨85452087122336309825238481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455744464652460319067938565 85452087122336309825238481)
              ·
                refine ⟨64089065341752232368928861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85452087122336309825238481 64089065341752232368928861)
                ·
                  refine ⟨24033399503157087138348323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64089065341752232368928861 24033399503157087138348323)
                  ·
                    refine ⟨36050099254735630707522485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24033399503157087138348323 36050099254735630707522485)
                    ·
                      refine ⟨3379696805131465378830233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36050099254735630707522485 3379696805131465378830233)
                      ·
                        rfl

theorem cell23_6581936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_6581936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581936 prefixEnd_6581936 := by exact prefixLift 6581936
  have htrace : WordTrace (prefixWord ++ tailWord_6581936) baseStart_6581936 baseEnd_6581936 := by
    simpa [prefixWord, tailWord_6581936, baseEnd_6581936] using wordTrace_append hprefix tailTrace_6581936
  have hstable : (prefixWord ++ tailWord_6581936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581936).length < 2 ^ (prefixWord ++ tailWord_6581936).sum := by decide
  have hdescent : baseEnd_6581936 < baseStart_6581936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581943 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 6]
def baseStart_6581943 : Nat := 118140960795 + 6581943 * 2 ^ 59
def prefixEnd_6581943 : Nat := 4983230072969 + 3 ^ 40 * 6581943 * 2
def baseEnd_6581943 : Nat := 1126566799832015617147567

theorem tailTrace_6581943 : CollatzResearch.WordTrace tailWord_6581943 prefixEnd_6581943 1126566799832015617147567 := by
  unfold tailWord_6581943
  simp only [CollatzResearch.WordTrace]
  refine ⟨240063183193752092214830483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160042122129168061476553655 240063183193752092214830483)
  ·
    refine ⟨360094774790628138322245725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240063183193752092214830483 360094774790628138322245725)
    ·
      refine ⟨135035540546485551870842147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360094774790628138322245725 135035540546485551870842147)
      ·
        refine ⟨202553310819728327806263221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135035540546485551870842147 202553310819728327806263221)
        ·
          refine ⟨18989372889349530731837177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202553310819728327806263221 18989372889349530731837177)
          ·
            refine ⟨14242029667012148048877883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18989372889349530731837177 14242029667012148048877883)
            ·
              refine ⟨21363044500518222073316825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242029667012148048877883 21363044500518222073316825)
              ·
                refine ⟨16022283375388666554987619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21363044500518222073316825 16022283375388666554987619)
                ·
                  refine ⟨24033425063082999832481429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16022283375388666554987619 24033425063082999832481429)
                  ·
                    refine ⟨1126566799832015617147567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24033425063082999832481429 1126566799832015617147567)
                    ·
                      rfl

theorem cell23_6581943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_6581943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581943 prefixEnd_6581943 := by exact prefixLift 6581943
  have htrace : WordTrace (prefixWord ++ tailWord_6581943) baseStart_6581943 baseEnd_6581943 := by
    simpa [prefixWord, tailWord_6581943, baseEnd_6581943] using wordTrace_append hprefix tailTrace_6581943
  have hstable : (prefixWord ++ tailWord_6581943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581943).length < 2 ^ (prefixWord ++ tailWord_6581943).sum := by decide
  have hdescent : baseEnd_6581943 < baseStart_6581943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581960 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_6581960 : Nat := 118140960795 + 6581960 * 2 ^ 59
def prefixEnd_6581960 : Nat := 4983230072969 + 3 ^ 40 * 6581960 * 2
def baseEnd_6581960 : Nat := 1126569709555724428310041

theorem tailTrace_6581960 : CollatzResearch.WordTrace tailWord_6581960 prefixEnd_6581960 1126569709555724428310041 := by
  unfold tailWord_6581960
  simp only [CollatzResearch.WordTrace]
  refine ⟨120031901617345252059099667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160042535489793669412132889 120031901617345252059099667)
  ·
    refine ⟨180047852426017878088649501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120031901617345252059099667 180047852426017878088649501)
    ·
      refine ⟨67517944659756704283243563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180047852426017878088649501 67517944659756704283243563)
      ·
        refine ⟨101276916989635056424865345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67517944659756704283243563 101276916989635056424865345)
        ·
          refine ⟨75957687742226292318649009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101276916989635056424865345 75957687742226292318649009)
          ·
            refine ⟨56968265806669719238986757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75957687742226292318649009 56968265806669719238986757)
            ·
              refine ⟨10681549838750572357310017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56968265806669719238986757 10681549838750572357310017)
              ·
                refine ⟨8011162379062929267982513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10681549838750572357310017 8011162379062929267982513)
                ·
                  refine ⟨6008371784297196950986885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8011162379062929267982513 6008371784297196950986885)
                  ·
                    refine ⟨1126569709555724428310041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008371784297196950986885 1126569709555724428310041)
                    ·
                      rfl

theorem cell23_6581960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_6581960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581960 prefixEnd_6581960 := by exact prefixLift 6581960
  have htrace : WordTrace (prefixWord ++ tailWord_6581960) baseStart_6581960 baseEnd_6581960 := by
    simpa [prefixWord, tailWord_6581960, baseEnd_6581960] using wordTrace_append hprefix tailTrace_6581960
  have hstable : (prefixWord ++ tailWord_6581960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581960).length < 2 ^ (prefixWord ++ tailWord_6581960).sum := by decide
  have hdescent : baseEnd_6581960 < baseStart_6581960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581970 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6581970 : Nat := 118140960795 + 6581970 * 2 ^ 59
def prefixEnd_6581970 : Nat := 4983230072969 + 3 ^ 40 * 6581970 * 2
def baseEnd_6581970 : Nat := 3379714263473718245805077

theorem tailTrace_6581970 : CollatzResearch.WordTrace tailWord_6581970 prefixEnd_6581970 3379714263473718245805077 := by
  unfold tailWord_6581970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016041991163568956515841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160042778643102850550708909 60016041991163568956515841)
  ·
    refine ⟨45012031493372676717386881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60016041991163568956515841 45012031493372676717386881)
    ·
      refine ⟨33759023620029507538040161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45012031493372676717386881 33759023620029507538040161)
      ·
        refine ⟨25319267715022130653530121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33759023620029507538040161 25319267715022130653530121)
        ·
          refine ⟨18989450786266597990147591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25319267715022130653530121 18989450786266597990147591)
          ·
            refine ⟨28484176179399896985221387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18989450786266597990147591 28484176179399896985221387)
            ·
              refine ⟨42726264269099845477832081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28484176179399896985221387 42726264269099845477832081)
              ·
                refine ⟨32044698201824884108374061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42726264269099845477832081 32044698201824884108374061)
                ·
                  refine ⟨12016761825684331540640273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32044698201824884108374061 12016761825684331540640273)
                  ·
                    refine ⟨9012571369263248655480205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12016761825684331540640273 9012571369263248655480205)
                    ·
                      refine ⟨3379714263473718245805077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012571369263248655480205 3379714263473718245805077)
                      ·
                        rfl

theorem cell23_6581970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6581970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6581970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6581970 prefixEnd_6581970 := by exact prefixLift 6581970
  have htrace : WordTrace (prefixWord ++ tailWord_6581970) baseStart_6581970 baseEnd_6581970 := by
    simpa [prefixWord, tailWord_6581970, baseEnd_6581970] using wordTrace_append hprefix tailTrace_6581970
  have hstable : (prefixWord ++ tailWord_6581970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581970).length < 2 ^ (prefixWord ++ tailWord_6581970).sum := by decide
  have hdescent : baseEnd_6581970 < baseStart_6581970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582016 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_6582016 : Nat := 118140960795 + 6582016 * 2 ^ 59
def prefixEnd_6582016 : Nat := 4983230072969 + 3 ^ 40 * 6582016 * 2
def baseEnd_6582016 : Nat := 1126579294527941688609955

theorem tailTrace_6582016 : CollatzResearch.WordTrace tailWord_6582016 prefixEnd_6582016 1126579294527941688609955 := by
  unfold tailWord_6582016
  simp only [CollatzResearch.WordTrace]
  refine ⟨120032922861243812841118951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160043897148325083788158601 120032922861243812841118951)
  ·
    refine ⟨180049384291865719261678427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120032922861243812841118951 180049384291865719261678427)
    ·
      refine ⟨270074076437798578892517641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180049384291865719261678427 270074076437798578892517641)
      ·
        refine ⟨202555557328348934169388231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270074076437798578892517641 202555557328348934169388231)
        ·
          refine ⟨303833335992523401254082347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202555557328348934169388231 303833335992523401254082347)
          ·
            refine ⟨455750003988785101881123521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303833335992523401254082347 455750003988785101881123521)
            ·
              refine ⟨341812502991588826410842641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455750003988785101881123521 341812502991588826410842641)
              ·
                refine ⟨256359377243691619808131981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341812502991588826410842641 256359377243691619808131981)
                ·
                  refine ⟨96134766466384357428049493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256359377243691619808131981 96134766466384357428049493)
                  ·
                    refine ⟨1126579294527941688609955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96134766466384357428049493 1126579294527941688609955)
                    ·
                      rfl

theorem cell23_6582016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_6582016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582016 prefixEnd_6582016 := by exact prefixLift 6582016
  have htrace : WordTrace (prefixWord ++ tailWord_6582016) baseStart_6582016 baseEnd_6582016 := by
    simpa [prefixWord, tailWord_6582016, baseEnd_6582016] using wordTrace_append hprefix tailTrace_6582016
  have hstable : (prefixWord ++ tailWord_6582016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582016).length < 2 ^ (prefixWord ++ tailWord_6582016).sum := by decide
  have hdescent : baseEnd_6582016 < baseStart_6582016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582017 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_6582017 : Nat := 118140960795 + 6582017 * 2 ^ 59
def prefixEnd_6582017 : Nat := 4983230072969 + 3 ^ 40 * 6582017 * 2
def baseEnd_6582017 : Nat := 3379738397064479561917361

theorem tailTrace_6582017 : CollatzResearch.WordTrace tailWord_6582017 prefixEnd_6582017 3379738397064479561917361 := by
  unfold tailWord_6582017
  simp only [CollatzResearch.WordTrace]
  refine ⟨240065882195484002853024305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160043921463656001902016203 240065882195484002853024305)
  ·
    refine ⟨180049411646613002139768229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240065882195484002853024305 180049411646613002139768229)
    ·
      refine ⟨33759264683739937901206543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180049411646613002139768229 33759264683739937901206543)
      ·
        refine ⟨50638897025609906851809815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33759264683739937901206543 50638897025609906851809815)
        ·
          refine ⟨75958345538414860277714723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50638897025609906851809815 75958345538414860277714723)
          ·
            refine ⟨113937518307622290416572085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75958345538414860277714723 113937518307622290416572085)
            ·
              refine ⟨10681642341339589726553633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113937518307622290416572085 10681642341339589726553633)
              ·
                refine ⟨8011231756004692294915225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10681642341339589726553633 8011231756004692294915225)
                ·
                  refine ⟨6008423817003519221186419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8011231756004692294915225 6008423817003519221186419)
                  ·
                    refine ⟨9012635725505278831779629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008423817003519221186419 9012635725505278831779629)
                    ·
                      refine ⟨3379738397064479561917361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012635725505278831779629 3379738397064479561917361)
                      ·
                        rfl

theorem cell23_6582017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_6582017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582017 prefixEnd_6582017 := by exact prefixLift 6582017
  have htrace : WordTrace (prefixWord ++ tailWord_6582017) baseStart_6582017 baseEnd_6582017 := by
    simpa [prefixWord, tailWord_6582017, baseEnd_6582017] using wordTrace_append hprefix tailTrace_6582017
  have hstable : (prefixWord ++ tailWord_6582017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582017).length < 2 ^ (prefixWord ++ tailWord_6582017).sum := by decide
  have hdescent : baseEnd_6582017 < baseStart_6582017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582034 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6582034 : Nat := 118140960795 + 6582034 * 2 ^ 59
def prefixEnd_6582034 : Nat := 4983230072969 + 3 ^ 40 * 6582034 * 2
def baseEnd_6582034 : Nat := 3379747126235605995404783

theorem tailTrace_6582034 : CollatzResearch.WordTrace tailWord_6582034 prefixEnd_6582034 3379747126235605995404783 := by
  unfold tailWord_6582034
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016625559105603689098289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160044334824281609837595437 60016625559105603689098289)
  ·
    refine ⟨45012469169329202766823717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60016625559105603689098289 45012469169329202766823717)
    ·
      refine ⟨8439837969249225518779447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45012469169329202766823717 8439837969249225518779447)
      ·
        refine ⟨12659756953873838278169171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439837969249225518779447 12659756953873838278169171)
        ·
          refine ⟨18989635430810757417253757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12659756953873838278169171 18989635430810757417253757)
          ·
            refine ⟨7121113286554034031470159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18989635430810757417253757 7121113286554034031470159)
            ·
              refine ⟨10681669929831051047205239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121113286554034031470159 10681669929831051047205239)
              ·
                refine ⟨16022504894746576570807859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10681669929831051047205239 16022504894746576570807859)
                ·
                  refine ⟨24033757342119864856211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16022504894746576570807859 24033757342119864856211789)
                  ·
                    refine ⟨9012659003294949321079421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24033757342119864856211789 9012659003294949321079421)
                    ·
                      refine ⟨3379747126235605995404783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012659003294949321079421 3379747126235605995404783)
                      ·
                        rfl

theorem cell23_6582034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6582034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582034 prefixEnd_6582034 := by exact prefixLift 6582034
  have htrace : WordTrace (prefixWord ++ tailWord_6582034) baseStart_6582034 baseEnd_6582034 := by
    simpa [prefixWord, tailWord_6582034, baseEnd_6582034] using wordTrace_append hprefix tailTrace_6582034
  have hstable : (prefixWord ++ tailWord_6582034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582034).length < 2 ^ (prefixWord ++ tailWord_6582034).sum := by decide
  have hdescent : baseEnd_6582034 < baseStart_6582034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582143 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_6582143 : Nat := 118140960795 + 6582143 * 2 ^ 59
def prefixEnd_6582143 : Nat := 4983230072969 + 3 ^ 40 * 6582143 * 2
def baseEnd_6582143 : Nat := 3379803095626946068941781

theorem tailTrace_6582143 : CollatzResearch.WordTrace tailWord_6582143 prefixEnd_6582143 3379803095626946068941781 := by
  unfold tailWord_6582143
  simp only [CollatzResearch.WordTrace]
  refine ⟨240070477793027526372111083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160046985195351684248074055 240070477793027526372111083)
  ·
    refine ⟨360105716689541289558166625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240070477793027526372111083 360105716689541289558166625)
    ·
      refine ⟨270079287517155967168624969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360105716689541289558166625 270079287517155967168624969)
      ·
        refine ⟨202559465637866975376468727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270079287517155967168624969 202559465637866975376468727)
        ·
          refine ⟨303839198456800463064703091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202559465637866975376468727 303839198456800463064703091)
          ·
            refine ⟨455758797685200694597054637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303839198456800463064703091 455758797685200694597054637)
            ·
              refine ⟨170909549131950260473895489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455758797685200694597054637 170909549131950260473895489)
              ·
                refine ⟨128182161848962695355421617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170909549131950260473895489 128182161848962695355421617)
                ·
                  refine ⟨96136621386722021516566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128182161848962695355421617 96136621386722021516566213)
                  ·
                    refine ⟨18025616510010379034356165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96136621386722021516566213 18025616510010379034356165)
                    ·
                      refine ⟨3379803095626946068941781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18025616510010379034356165 3379803095626946068941781)
                      ·
                        rfl

theorem cell23_6582143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_6582143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582143 prefixEnd_6582143 := by exact prefixLift 6582143
  have htrace : WordTrace (prefixWord ++ tailWord_6582143) baseStart_6582143 baseEnd_6582143 := by
    simpa [prefixWord, tailWord_6582143, baseEnd_6582143] using wordTrace_append hprefix tailTrace_6582143
  have hstable : (prefixWord ++ tailWord_6582143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582143).length < 2 ^ (prefixWord ++ tailWord_6582143).sum := by decide
  have hdescent : baseEnd_6582143 < baseStart_6582143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582147 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 4, 2]
def baseStart_6582147 : Nat := 118140960795 + 6582147 * 2 ^ 59
def prefixEnd_6582147 : Nat := 4983230072969 + 3 ^ 40 * 6582147 * 2
def baseEnd_6582147 : Nat := 3379805149549564053291763

theorem tailTrace_6582147 : CollatzResearch.WordTrace tailWord_6582147 prefixEnd_6582147 3379805149549564053291763 := by
  unfold tailWord_6582147
  simp only [CollatzResearch.WordTrace]
  refine ⟨240070623685013035055256695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160047082456675356703504463 240070623685013035055256695)
  ·
    refine ⟨360105935527519552582885043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240070623685013035055256695 360105935527519552582885043)
    ·
      refine ⟨540158903291279328874327565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360105935527519552582885043 540158903291279328874327565)
      ·
        refine ⟨202559588734229748327872837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540158903291279328874327565 202559588734229748327872837)
        ·
          refine ⟨37979922887668077811476157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202559588734229748327872837 37979922887668077811476157)
          ·
            refine ⟨14242471082875529179303559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37979922887668077811476157 14242471082875529179303559)
            ·
              refine ⟨21363706624313293768955339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242471082875529179303559 21363706624313293768955339)
              ·
                refine ⟨32045559936469940653433009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21363706624313293768955339 32045559936469940653433009)
                ·
                  refine ⟨24034169952352455490074757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32045559936469940653433009 24034169952352455490074757)
                  ·
                    refine ⟨4506406866066085404389017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24034169952352455490074757 4506406866066085404389017)
                    ·
                      refine ⟨3379805149549564053291763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506406866066085404389017 3379805149549564053291763)
                      ·
                        rfl

theorem cell23_6582147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_6582147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582147 prefixEnd_6582147 := by exact prefixLift 6582147
  have htrace : WordTrace (prefixWord ++ tailWord_6582147) baseStart_6582147 baseEnd_6582147 := by
    simpa [prefixWord, tailWord_6582147, baseEnd_6582147] using wordTrace_append hprefix tailTrace_6582147
  have hstable : (prefixWord ++ tailWord_6582147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582147).length < 2 ^ (prefixWord ++ tailWord_6582147).sum := by decide
  have hdescent : baseEnd_6582147 < baseStart_6582147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582164 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6582164 : Nat := 118140960795 + 6582164 * 2 ^ 59
def prefixEnd_6582164 : Nat := 4983230072969 + 3 ^ 40 * 6582164 * 2
def baseEnd_6582164 : Nat := 3379813878720690486779185

theorem tailTrace_6582164 : CollatzResearch.WordTrace tailWord_6582164 prefixEnd_6582164 3379813878720690486779185 := by
  unfold tailWord_6582164
  simp only [CollatzResearch.WordTrace]
  refine ⟨120035621862975723479312773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160047495817300964639083697 120035621862975723479312773)
  ·
    refine ⟨22506679099307948152371145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120035621862975723479312773 22506679099307948152371145)
    ·
      refine ⟨16880009324480961114278359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22506679099307948152371145 16880009324480961114278359)
      ·
        refine ⟨25320013986721441671417539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16880009324480961114278359 25320013986721441671417539)
        ·
          refine ⟨37980020980082162507126309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25320013986721441671417539 37980020980082162507126309)
          ·
            refine ⟨7121253933765405470086183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37980020980082162507126309 7121253933765405470086183)
            ·
              refine ⟨10681880900648108205129275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121253933765405470086183 10681880900648108205129275)
              ·
                refine ⟨16022821350972162307693913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10681880900648108205129275 16022821350972162307693913)
                ·
                  refine ⟨12017116013229121730770435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16022821350972162307693913 12017116013229121730770435)
                  ·
                    refine ⟨18025674019843682596155653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12017116013229121730770435 18025674019843682596155653)
                    ·
                      refine ⟨3379813878720690486779185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18025674019843682596155653 3379813878720690486779185)
                      ·
                        rfl

theorem cell23_6582164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6582164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582164 prefixEnd_6582164 := by exact prefixLift 6582164
  have htrace : WordTrace (prefixWord ++ tailWord_6582164) baseStart_6582164 baseEnd_6582164 := by
    simpa [prefixWord, tailWord_6582164, baseEnd_6582164] using wordTrace_append hprefix tailTrace_6582164
  have hstable : (prefixWord ++ tailWord_6582164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582164).length < 2 ^ (prefixWord ++ tailWord_6582164).sum := by decide
  have hdescent : baseEnd_6582164 < baseStart_6582164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582167 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_6582167 : Nat := 118140960795 + 6582167 * 2 ^ 59
def prefixEnd_6582167 : Nat := 4983230072969 + 3 ^ 40 * 6582167 * 2
def baseEnd_6582167 : Nat := 3379815419162653975041671

theorem tailTrace_6582167 : CollatzResearch.WordTrace tailWord_6582167 prefixEnd_6582167 3379815419162653975041671 := by
  unfold tailWord_6582167
  simp only [CollatzResearch.WordTrace]
  refine ⟨240071353144940578470984755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160047568763293718980656503 240071353144940578470984755)
  ·
    refine ⟨360107029717410867706477133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240071353144940578470984755 360107029717410867706477133)
    ·
      refine ⟨135040136144029075389928925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360107029717410867706477133 135040136144029075389928925)
      ·
        refine ⟨50640051054010903271223347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135040136144029075389928925 50640051054010903271223347)
        ·
          refine ⟨75960076581016354906835021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50640051054010903271223347 75960076581016354906835021)
          ·
            refine ⟨28485028717881133090063133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75960076581016354906835021 28485028717881133090063133)
            ·
              refine ⟨10681885769205424908773675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28485028717881133090063133 10681885769205424908773675)
              ·
                refine ⟨16022828653808137363160513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10681885769205424908773675 16022828653808137363160513)
                ·
                  refine ⟨12017121490356103022370385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16022828653808137363160513 12017121490356103022370385)
                  ·
                    refine ⟨9012841117767077266777789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12017121490356103022370385 9012841117767077266777789)
                    ·
                      refine ⟨3379815419162653975041671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9012841117767077266777789 3379815419162653975041671)
                      ·
                        rfl

theorem cell23_6582167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_6582167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582167 prefixEnd_6582167 := by exact prefixLift 6582167
  have htrace : WordTrace (prefixWord ++ tailWord_6582167) baseStart_6582167 baseEnd_6582167 := by
    simpa [prefixWord, tailWord_6582167, baseEnd_6582167] using wordTrace_append hprefix tailTrace_6582167
  have hstable : (prefixWord ++ tailWord_6582167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582167).length < 2 ^ (prefixWord ++ tailWord_6582167).sum := by decide
  have hdescent : baseEnd_6582167 < baseStart_6582167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582250 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6582250 : Nat := 118140960795 + 6582250 * 2 ^ 59
def prefixEnd_6582250 : Nat := 4983230072969 + 3 ^ 40 * 6582250 * 2
def baseEnd_6582250 : Nat := 3379858038056977150303789

theorem tailTrace_6582250 : CollatzResearch.WordTrace tailWord_6582250 prefixEnd_6582250 3379858038056977150303789 := by
  unfold tailWord_6582250
  simp only [CollatzResearch.WordTrace]
  refine ⟨60018595100909970911564051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160049586935759922430837469 60018595100909970911564051)
  ·
    refine ⟨90027892651364956367346077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60018595100909970911564051 90027892651364956367346077)
    ·
      refine ⟨33760459744261858637754779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90027892651364956367346077 33760459744261858637754779)
      ·
        refine ⟨50640689616392787956632169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33760459744261858637754779 50640689616392787956632169)
        ·
          refine ⟨37980517212294590967474127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50640689616392787956632169 37980517212294590967474127)
          ·
            refine ⟨56970775818441886451211191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37980517212294590967474127 56970775818441886451211191)
            ·
              refine ⟨85456163727662829676816787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56970775818441886451211191 85456163727662829676816787)
              ·
                refine ⟨128184245591494244515225181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85456163727662829676816787 128184245591494244515225181)
                ·
                  refine ⟨48069092096810341693209443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128184245591494244515225181 48069092096810341693209443)
                  ·
                    refine ⟨72103638145215512539814165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48069092096810341693209443 72103638145215512539814165)
                    ·
                      refine ⟨3379858038056977150303789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72103638145215512539814165 3379858038056977150303789)
                      ·
                        rfl

theorem cell23_6582250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6582250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582250 prefixEnd_6582250 := by exact prefixLift 6582250
  have htrace : WordTrace (prefixWord ++ tailWord_6582250) baseStart_6582250 baseEnd_6582250 := by
    simpa [prefixWord, tailWord_6582250, baseEnd_6582250] using wordTrace_append hprefix tailTrace_6582250
  have hstable : (prefixWord ++ tailWord_6582250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582250).length < 2 ^ (prefixWord ++ tailWord_6582250).sum := by decide
  have hdescent : baseEnd_6582250 < baseStart_6582250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582264 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_6582264 : Nat := 118140960795 + 6582264 * 2 ^ 59
def prefixEnd_6582264 : Nat := 4983230072969 + 3 ^ 40 * 6582264 * 2
def baseEnd_6582264 : Nat := 1126621742262046698509575

theorem tailTrace_6582264 : CollatzResearch.WordTrace tailWord_6582264 prefixEnd_6582264 1126621742262046698509575 := by
  unfold tailWord_6582264
  simp only [CollatzResearch.WordTrace]
  refine ⟨120037445512794582018632923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160049927350392776024843897 120037445512794582018632923)
  ·
    refine ⟨180056168269191873027949385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120037445512794582018632923 180056168269191873027949385)
    ·
      refine ⟨135042126201893904770962039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180056168269191873027949385 135042126201893904770962039)
      ·
        refine ⟨202563189302840857156443059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135042126201893904770962039 202563189302840857156443059)
        ·
          refine ⟨303844783954261285734664589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202563189302840857156443059 303844783954261285734664589)
          ·
            refine ⟨113941793982847982150499221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303844783954261285734664589 113941793982847982150499221)
            ·
              refine ⟨5341021592945999163304651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113941793982847982150499221 5341021592945999163304651)
              ·
                refine ⟨8011532389418998744956977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341021592945999163304651 8011532389418998744956977)
                ·
                  refine ⟨6008649292064249058717733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8011532389418998744956977 6008649292064249058717733)
                  ·
                    refine ⟨1126621742262046698509575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008649292064249058717733 1126621742262046698509575)
                    ·
                      rfl

theorem cell23_6582264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_6582264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582264 prefixEnd_6582264 := by exact prefixLift 6582264
  have htrace : WordTrace (prefixWord ++ tailWord_6582264) baseStart_6582264 baseEnd_6582264 := by
    simpa [prefixWord, tailWord_6582264, baseEnd_6582264] using wordTrace_append hprefix tailTrace_6582264
  have hstable : (prefixWord ++ tailWord_6582264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582264).length < 2 ^ (prefixWord ++ tailWord_6582264).sum := by decide
  have hdescent : baseEnd_6582264 < baseStart_6582264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582285 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6582285 : Nat := 118140960795 + 6582285 * 2 ^ 59
def prefixEnd_6582285 : Nat := 4983230072969 + 3 ^ 40 * 6582285 * 2
def baseEnd_6582285 : Nat := 1126625336626628171122043

theorem tailTrace_6582285 : CollatzResearch.WordTrace tailWord_6582285 prefixEnd_6582285 1126625336626628171122043 := by
  unfold tailWord_6582285
  simp only [CollatzResearch.WordTrace]
  refine ⟨240075656958513084623780309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160050437972342056415853539 240075656958513084623780309)
  ·
    refine ⟨5626773209965150420869851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 240075656958513084623780309 5626773209965150420869851)
    ·
      refine ⟨8440159814947725631304777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5626773209965150420869851 8440159814947725631304777)
      ·
        refine ⟨6330119861210794223478583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440159814947725631304777 6330119861210794223478583)
        ·
          refine ⟨9495179791816191335217875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330119861210794223478583 9495179791816191335217875)
          ·
            refine ⟨14242769687724287002826813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495179791816191335217875 14242769687724287002826813)
            ·
              refine ⟨5341038632896607626060055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14242769687724287002826813 5341038632896607626060055)
              ·
                refine ⟨8011557949344911439090083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341038632896607626060055 8011557949344911439090083)
                ·
                  refine ⟨12017336924017367158635125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011557949344911439090083 12017336924017367158635125)
                  ·
                    refine ⟨1126625336626628171122043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12017336924017367158635125 1126625336626628171122043)
                    ·
                      rfl

theorem cell23_6582285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6582285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582285 prefixEnd_6582285 := by exact prefixLift 6582285
  have htrace : WordTrace (prefixWord ++ tailWord_6582285) baseStart_6582285 baseEnd_6582285 := by
    simpa [prefixWord, tailWord_6582285, baseEnd_6582285] using wordTrace_append hprefix tailTrace_6582285
  have hstable : (prefixWord ++ tailWord_6582285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582285).length < 2 ^ (prefixWord ++ tailWord_6582285).sum := by decide
  have hdescent : baseEnd_6582285 < baseStart_6582285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582311 : List Nat := [1, 1, 7, 1, 3, 1, 1, 8]
def baseStart_6582311 : Nat := 118140960795 + 6582311 * 2 ^ 59
def prefixEnd_6582311 : Nat := 4983230072969 + 3 ^ 40 * 6582311 * 2
def baseEnd_6582311 : Nat := 125181087421366718949667

theorem tailTrace_6582311 : CollatzResearch.WordTrace tailWord_6582311 prefixEnd_6582311 125181087421366718949667 := by
  unfold tailWord_6582311
  simp only [CollatzResearch.WordTrace]
  refine ⟨240076605256418891064226787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160051070170945927376151191 240076605256418891064226787)
  ·
    refine ⟨360114907884628336596340181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240076605256418891064226787 360114907884628336596340181)
    ·
      refine ⟨8440193153545976638976723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 360114907884628336596340181 8440193153545976638976723)
      ·
        refine ⟨12660289730318964958465085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8440193153545976638976723 12660289730318964958465085)
        ·
          refine ⟨4747608648869611859424407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12660289730318964958465085 4747608648869611859424407)
          ·
            refine ⟨7121412973304417789136611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747608648869611859424407 7121412973304417789136611)
            ·
              refine ⟨10682119459956626683704917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121412973304417789136611 10682119459956626683704917)
              ·
                refine ⟨125181087421366718949667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10682119459956626683704917 125181087421366718949667)
                ·
                  rfl

theorem cell23_6582311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 8].length) (baseStart_6582311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582311 prefixEnd_6582311 := by exact prefixLift 6582311
  have htrace : WordTrace (prefixWord ++ tailWord_6582311) baseStart_6582311 baseEnd_6582311 := by
    simpa [prefixWord, tailWord_6582311, baseEnd_6582311] using wordTrace_append hprefix tailTrace_6582311
  have hstable : (prefixWord ++ tailWord_6582311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582311).length < 2 ^ (prefixWord ++ tailWord_6582311).sum := by decide
  have hdescent : baseEnd_6582311 < baseStart_6582311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582320 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_6582320 : Nat := 118140960795 + 6582320 * 2 ^ 59
def prefixEnd_6582320 : Nat := 4983230072969 + 3 ^ 40 * 6582320 * 2
def baseEnd_6582320 : Nat := 1126631327234263958809489

theorem tailTrace_6582320 : CollatzResearch.WordTrace tailWord_6582320 prefixEnd_6582320 1126631327234263958809489 := by
  unfold tailWord_6582320
  simp only [CollatzResearch.WordTrace]
  refine ⟨120038466756693142800652207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160051289008924190400869609 120038466756693142800652207)
  ·
    refine ⟨180057700135039714200978311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120038466756693142800652207 180057700135039714200978311)
    ·
      refine ⟨270086550202559571301467467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180057700135039714200978311 270086550202559571301467467)
      ·
        refine ⟨405129825303839356952201201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270086550202559571301467467 405129825303839356952201201)
        ·
          refine ⟨303847368977879517714150901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405129825303839356952201201 303847368977879517714150901)
          ·
            refine ⟨28485690841676204785701647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303847368977879517714150901 28485690841676204785701647)
            ·
              refine ⟨42728536262514307178552471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28485690841676204785701647 42728536262514307178552471)
              ·
                refine ⟨64092804393771460767828707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42728536262514307178552471 64092804393771460767828707)
                ·
                  refine ⟨96139206590657191151743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64092804393771460767828707 96139206590657191151743061)
                  ·
                    refine ⟨1126631327234263958809489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96139206590657191151743061 1126631327234263958809489)
                    ·
                      rfl

theorem cell23_6582320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_6582320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582320 prefixEnd_6582320 := by exact prefixLift 6582320
  have htrace : WordTrace (prefixWord ++ tailWord_6582320) baseStart_6582320 baseEnd_6582320 := by
    simpa [prefixWord, tailWord_6582320, baseEnd_6582320] using wordTrace_append hprefix tailTrace_6582320
  have hstable : (prefixWord ++ tailWord_6582320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582320).length < 2 ^ (prefixWord ++ tailWord_6582320).sum := by decide
  have hdescent : baseEnd_6582320 < baseStart_6582320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582357 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6582357 : Nat := 118140960795 + 6582357 * 2 ^ 59
def prefixEnd_6582357 : Nat := 4983230072969 + 3 ^ 40 * 6582357 * 2
def baseEnd_6582357 : Nat := 3379912980487008231665797

theorem tailTrace_6582357 : CollatzResearch.WordTrace tailWord_6582357 prefixEnd_6582357 3379912980487008231665797 := by
  unfold tailWord_6582357
  simp only [CollatzResearch.WordTrace]
  refine ⟨240078283014252240920401325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160052188676168160613600883 240078283014252240920401325)
  ·
    refine ⟨90029356130344590345150497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240078283014252240920401325 90029356130344590345150497)
    ·
      refine ⟨67522017097758442758862873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90029356130344590345150497 67522017097758442758862873)
      ·
        refine ⟨50641512823318832069147155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67522017097758442758862873 50641512823318832069147155)
        ·
          refine ⟨75962269234978248103720733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50641512823318832069147155 75962269234978248103720733)
          ·
            refine ⟨28485850963116843038895275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75962269234978248103720733 28485850963116843038895275)
            ·
              refine ⟨42728776444675264558342913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28485850963116843038895275 42728776444675264558342913)
              ·
                refine ⟨32046582333506448418757185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42728776444675264558342913 32046582333506448418757185)
                ·
                  refine ⟨24034936750129836314067889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32046582333506448418757185 24034936750129836314067889)
                  ·
                    refine ⟨18026202562597377235550917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24034936750129836314067889 18026202562597377235550917)
                    ·
                      refine ⟨3379912980487008231665797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18026202562597377235550917 3379912980487008231665797)
                      ·
                        rfl

theorem cell23_6582357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6582357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582357 prefixEnd_6582357 := by exact prefixLift 6582357
  have htrace : WordTrace (prefixWord ++ tailWord_6582357) baseStart_6582357 baseEnd_6582357 := by
    simpa [prefixWord, tailWord_6582357, baseEnd_6582357] using wordTrace_append hprefix tailTrace_6582357
  have hstable : (prefixWord ++ tailWord_6582357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582357).length < 2 ^ (prefixWord ++ tailWord_6582357).sum := by decide
  have hdescent : baseEnd_6582357 < baseStart_6582357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582377 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_6582377 : Nat := 118140960795 + 6582377 * 2 ^ 59
def prefixEnd_6582377 : Nat := 4983230072969 + 3 ^ 40 * 6582377 * 2
def baseEnd_6582377 : Nat := 3379923250100098153415705

theorem tailTrace_6582377 : CollatzResearch.WordTrace tailWord_6582377 prefixEnd_6582377 3379923250100098153415705 := by
  unfold tailWord_6582377
  simp only [CollatzResearch.WordTrace]
  refine ⟨240079012474179784336129385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160052674982786522890752923 240079012474179784336129385)
  ·
    refine ⟨180059259355634838252097039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240079012474179784336129385 180059259355634838252097039)
    ·
      refine ⟨270088889033452257378145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180059259355634838252097039 270088889033452257378145559)
      ·
        refine ⟨405133333550178386067218339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270088889033452257378145559 405133333550178386067218339)
        ·
          refine ⟨607700000325267579100827509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405133333550178386067218339 607700000325267579100827509)
          ·
            refine ⟨56971875030493835540702579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 607700000325267579100827509 56971875030493835540702579)
            ·
              refine ⟨85457812545740753311053869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56971875030493835540702579 85457812545740753311053869)
              ·
                refine ⟨32046679704652782491645201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85457812545740753311053869 32046679704652782491645201)
                ·
                  refine ⟨24035009778489586868733901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32046679704652782491645201 24035009778489586868733901)
                  ·
                    refine ⟨9013128666933595075775213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24035009778489586868733901 9013128666933595075775213)
                    ·
                      refine ⟨3379923250100098153415705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013128666933595075775213 3379923250100098153415705)
                      ·
                        rfl

theorem cell23_6582377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_6582377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582377 prefixEnd_6582377 := by exact prefixLift 6582377
  have htrace : WordTrace (prefixWord ++ tailWord_6582377) baseStart_6582377 baseEnd_6582377 := by
    simpa [prefixWord, tailWord_6582377, baseEnd_6582377] using wordTrace_append hprefix tailTrace_6582377
  have hstable : (prefixWord ++ tailWord_6582377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582377).length < 2 ^ (prefixWord ++ tailWord_6582377).sum := by decide
  have hdescent : baseEnd_6582377 < baseStart_6582377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582378 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_6582378 : Nat := 118140960795 + 6582378 * 2 ^ 59
def prefixEnd_6582378 : Nat := 4983230072969 + 3 ^ 40 * 6582378 * 2
def baseEnd_6582378 : Nat := 3379923763580752649503201

theorem tailTrace_6582378 : CollatzResearch.WordTrace tailWord_6582378 prefixEnd_6582378 3379923763580752649503201 := by
  unfold tailWord_6582378
  simp only [CollatzResearch.WordTrace]
  refine ⟨60019762236794040376728947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160052699298117441004610525 60019762236794040376728947)
  ·
    refine ⟨90029643355191060565093421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60019762236794040376728947 90029643355191060565093421)
    ·
      refine ⟨33761116258196647711910033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90029643355191060565093421 33761116258196647711910033)
      ·
        refine ⟨25320837193647485783932525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33761116258196647711910033 25320837193647485783932525)
        ·
          refine ⟨9495313947617807168974697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25320837193647485783932525 9495313947617807168974697)
          ·
            refine ⟨7121485460713355376731023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9495313947617807168974697 7121485460713355376731023)
            ·
              refine ⟨10682228191070033065096535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121485460713355376731023 10682228191070033065096535)
              ·
                refine ⟨16023342286605049597644803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682228191070033065096535 16023342286605049597644803)
                ·
                  refine ⟨24035013429907574396467205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16023342286605049597644803 24035013429907574396467205)
                  ·
                    refine ⟨4506565018107670199337601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24035013429907574396467205 4506565018107670199337601)
                    ·
                      refine ⟨3379923763580752649503201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506565018107670199337601 3379923763580752649503201)
                      ·
                        rfl

theorem cell23_6582378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_6582378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582378 prefixEnd_6582378 := by exact prefixLift 6582378
  have htrace : WordTrace (prefixWord ++ tailWord_6582378) baseStart_6582378 baseEnd_6582378 := by
    simpa [prefixWord, tailWord_6582378, baseEnd_6582378] using wordTrace_append hprefix tailTrace_6582378
  have hstable : (prefixWord ++ tailWord_6582378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582378).length < 2 ^ (prefixWord ++ tailWord_6582378).sum := by decide
  have hdescent : baseEnd_6582378 < baseStart_6582378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582397 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_6582397 : Nat := 118140960795 + 6582397 * 2 ^ 59
def prefixEnd_6582397 : Nat := 4983230072969 + 3 ^ 40 * 6582397 * 2
def baseEnd_6582397 : Nat := 1126644506571062691721871

theorem tailTrace_6582397 : CollatzResearch.WordTrace tailWord_6582397 prefixEnd_6582397 1126644506571062691721871 := by
  unfold tailWord_6582397
  simp only [CollatzResearch.WordTrace]
  refine ⟨240079741934107327751857445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160053161289404885167904963 240079741934107327751857445)
  ·
    refine ⟨45014951612645123953473271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240079741934107327751857445 45014951612645123953473271)
    ·
      refine ⟨67522427418967685930209907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45014951612645123953473271 67522427418967685930209907)
      ·
        refine ⟨101283641128451528895314861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67522427418967685930209907 101283641128451528895314861)
        ·
          refine ⟨37981365423169323335743073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101283641128451528895314861 37981365423169323335743073)
          ·
            refine ⟨28486024067376992501807305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37981365423169323335743073 28486024067376992501807305)
            ·
              refine ⟨21364518050532744376355479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28486024067376992501807305 21364518050532744376355479)
              ·
                refine ⟨32046777075799116564533219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364518050532744376355479 32046777075799116564533219)
                ·
                  refine ⟨48070165613698674846799829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32046777075799116564533219 48070165613698674846799829)
                  ·
                    refine ⟨1126644506571062691721871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48070165613698674846799829 1126644506571062691721871)
                    ·
                      rfl

theorem cell23_6582397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_6582397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582397 prefixEnd_6582397 := by exact prefixLift 6582397
  have htrace : WordTrace (prefixWord ++ tailWord_6582397) baseStart_6582397 baseEnd_6582397 := by
    simpa [prefixWord, tailWord_6582397, baseEnd_6582397] using wordTrace_append hprefix tailTrace_6582397
  have hstable : (prefixWord ++ tailWord_6582397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582397).length < 2 ^ (prefixWord ++ tailWord_6582397).sum := by decide
  have hdescent : baseEnd_6582397 < baseStart_6582397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582424 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6582424 : Nat := 118140960795 + 6582424 * 2 ^ 59
def prefixEnd_6582424 : Nat := 4983230072969 + 3 ^ 40 * 6582424 * 2
def baseEnd_6582424 : Nat := 3379947383690859469527989

theorem tailTrace_6582424 : CollatzResearch.WordTrace tailWord_6582424 prefixEnd_6582424 3379947383690859469527989 := by
  unfold tailWord_6582424
  simp only [CollatzResearch.WordTrace]
  refine ⟨120040363352504755681545163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160053817803339674242060217 120040363352504755681545163)
  ·
    refine ⟨180060545028757133522317745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120040363352504755681545163 180060545028757133522317745)
    ·
      refine ⟨135045408771567850141738309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180060545028757133522317745 135045408771567850141738309)
      ·
        refine ⟨25321014144668971901575933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135045408771567850141738309 25321014144668971901575933)
        ·
          refine ⟨9495380304250864463090975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25321014144668971901575933 9495380304250864463090975)
          ·
            refine ⟨14243070456376296694636463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495380304250864463090975 14243070456376296694636463)
            ·
              refine ⟨21364605684564445041954695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243070456376296694636463 21364605684564445041954695)
              ·
                refine ⟨32046908526846667562932043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364605684564445041954695 32046908526846667562932043)
                ·
                  refine ⟨48070362790270001344398065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32046908526846667562932043 48070362790270001344398065)
                  ·
                    refine ⟨36052772092702501008298549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48070362790270001344398065 36052772092702501008298549)
                    ·
                      refine ⟨3379947383690859469527989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36052772092702501008298549 3379947383690859469527989)
                      ·
                        rfl

theorem cell23_6582424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6582424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582424 prefixEnd_6582424 := by exact prefixLift 6582424
  have htrace : WordTrace (prefixWord ++ tailWord_6582424) baseStart_6582424 baseEnd_6582424 := by
    simpa [prefixWord, tailWord_6582424, baseEnd_6582424] using wordTrace_append hprefix tailTrace_6582424
  have hstable : (prefixWord ++ tailWord_6582424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582424).length < 2 ^ (prefixWord ++ tailWord_6582424).sum := by decide
  have hdescent : baseEnd_6582424 < baseStart_6582424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582427 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 7, 4]
def baseStart_6582427 : Nat := 118140960795 + 6582427 * 2 ^ 59
def prefixEnd_6582427 : Nat := 4983230072969 + 3 ^ 40 * 6582427 * 2
def baseEnd_6582427 : Nat := 1126649641377607652596825

theorem tailTrace_6582427 : CollatzResearch.WordTrace tailWord_6582427 prefixEnd_6582427 1126649641377607652596825 := by
  unfold tailWord_6582427
  simp only [CollatzResearch.WordTrace]
  refine ⟨240080836123998642875449535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160053890749332428583633023 240080836123998642875449535)
  ·
    refine ⟨360121254185997964313174303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240080836123998642875449535 360121254185997964313174303)
    ·
      refine ⟨540181881278996946469761455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360121254185997964313174303 540181881278996946469761455)
      ·
        refine ⟨810272821918495419704642183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540181881278996946469761455 810272821918495419704642183)
        ·
          refine ⟨1215409232877743129556963275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810272821918495419704642183 1215409232877743129556963275)
          ·
            refine ⟨1823113849316614694335444913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215409232877743129556963275 1823113849316614694335444913)
            ·
              refine ⟨1367335386987461020751583685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823113849316614694335444913 1367335386987461020751583685)
              ·
                refine ⟨256375385060148941390921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1367335386987461020751583685 256375385060148941390921941)
                ·
                  refine ⟨6008798087347240813849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 256375385060148941390921941 6008798087347240813849733)
                  ·
                    refine ⟨1126649641377607652596825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008798087347240813849733 1126649641377607652596825)
                    ·
                      rfl

theorem cell23_6582427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 4].length) (baseStart_6582427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582427 prefixEnd_6582427 := by exact prefixLift 6582427
  have htrace : WordTrace (prefixWord ++ tailWord_6582427) baseStart_6582427 baseEnd_6582427 := by
    simpa [prefixWord, tailWord_6582427, baseEnd_6582427] using wordTrace_append hprefix tailTrace_6582427
  have hstable : (prefixWord ++ tailWord_6582427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582427).length < 2 ^ (prefixWord ++ tailWord_6582427).sum := by decide
  have hdescent : baseEnd_6582427 < baseStart_6582427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582461 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_6582461 : Nat := 118140960795 + 6582461 * 2 ^ 59
def prefixEnd_6582461 : Nat := 4983230072969 + 3 ^ 40 * 6582461 * 2
def baseEnd_6582461 : Nat := 1126655460825025274921773

theorem tailTrace_6582461 : CollatzResearch.WordTrace tailWord_6582461 prefixEnd_6582461 1126655460825025274921773 := by
  unfold tailWord_6582461
  simp only [CollatzResearch.WordTrace]
  refine ⟨240082076205875466682187237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160054717470583644454791491 240082076205875466682187237)
  ·
    refine ⟨45015389288601650002910107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240082076205875466682187237 45015389288601650002910107)
    ·
      refine ⟨67523083932902475004365161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45015389288601650002910107 67523083932902475004365161)
      ·
        refine ⟨50642312949676856253273871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67523083932902475004365161 50642312949676856253273871)
        ·
          refine ⟨75963469424515284379910807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50642312949676856253273871 75963469424515284379910807)
          ·
            refine ⟨113945204136772926569866211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75963469424515284379910807 113945204136772926569866211)
            ·
              refine ⟨170917806205159389854799317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113945204136772926569866211 170917806205159389854799317)
              ·
                refine ⟨4005886082933423199721859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170917806205159389854799317 4005886082933423199721859)
                ·
                  refine ⟨6008829124400134799582789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005886082933423199721859 6008829124400134799582789)
                  ·
                    refine ⟨1126655460825025274921773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008829124400134799582789 1126655460825025274921773)
                    ·
                      rfl

theorem cell23_6582461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_6582461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582461 prefixEnd_6582461 := by exact prefixLift 6582461
  have htrace : WordTrace (prefixWord ++ tailWord_6582461) baseStart_6582461 baseEnd_6582461 := by
    simpa [prefixWord, tailWord_6582461, baseEnd_6582461] using wordTrace_append hprefix tailTrace_6582461
  have hstable : (prefixWord ++ tailWord_6582461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582461).length < 2 ^ (prefixWord ++ tailWord_6582461).sum := by decide
  have hdescent : baseEnd_6582461 < baseStart_6582461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582467 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3]
def baseStart_6582467 : Nat := 118140960795 + 6582467 * 2 ^ 59
def prefixEnd_6582467 : Nat := 4983230072969 + 3 ^ 40 * 6582467 * 2
def baseEnd_6582467 : Nat := 3379969463359002801290291

theorem tailTrace_6582467 : CollatzResearch.WordTrace tailWord_6582467 prefixEnd_6582467 3379969463359002801290291 := by
  unfold tailWord_6582467
  simp only [CollatzResearch.WordTrace]
  refine ⟨240082295043853729706905655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160054863362569153137937103 240082295043853729706905655)
  ·
    refine ⟨360123442565780594560358483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240082295043853729706905655 360123442565780594560358483)
    ·
      refine ⟨540185163848670891840537725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360123442565780594560358483 540185163848670891840537725)
      ·
        refine ⟨202569436443251584440201647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540185163848670891840537725 202569436443251584440201647)
        ·
          refine ⟨303854154664877376660302471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202569436443251584440201647 303854154664877376660302471)
          ·
            refine ⟨455781231997316064990453707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303854154664877376660302471 455781231997316064990453707)
            ·
              refine ⟨683671847995974097485680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455781231997316064990453707 683671847995974097485680561)
              ·
                refine ⟨512753885996980573114260421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683671847995974097485680561 512753885996980573114260421)
                ·
                  refine ⟨96141353624433857458923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512753885996980573114260421 96141353624433857458923829)
                  ·
                    refine ⟨9013251902290674136774109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96141353624433857458923829 9013251902290674136774109)
                    ·
                      refine ⟨3379969463359002801290291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013251902290674136774109 3379969463359002801290291)
                      ·
                        rfl

theorem cell23_6582467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_6582467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582467 prefixEnd_6582467 := by exact prefixLift 6582467
  have htrace : WordTrace (prefixWord ++ tailWord_6582467) baseStart_6582467 baseEnd_6582467 := by
    simpa [prefixWord, tailWord_6582467, baseEnd_6582467] using wordTrace_append hprefix tailTrace_6582467
  have hstable : (prefixWord ++ tailWord_6582467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582467).length < 2 ^ (prefixWord ++ tailWord_6582467).sum := by decide
  have hdescent : baseEnd_6582467 < baseStart_6582467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582474 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_6582474 : Nat := 118140960795 + 6582474 * 2 ^ 59
def prefixEnd_6582474 : Nat := 4983230072969 + 3 ^ 40 * 6582474 * 2
def baseEnd_6582474 : Nat := 375552561969287141544751

theorem tailTrace_6582474 : CollatzResearch.WordTrace tailWord_6582474 prefixEnd_6582474 375552561969287141544751 := by
  unfold tailWord_6582474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60020637588707092475602619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160055033569885579934940317 60020637588707092475602619)
  ·
    refine ⟨90030956383060638713403929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60020637588707092475602619 90030956383060638713403929)
    ·
      refine ⟨67523217287295479035052947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90030956383060638713403929 67523217287295479035052947)
      ·
        refine ⟨101284825930943218552579421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67523217287295479035052947 101284825930943218552579421)
        ·
          refine ⟨37981809724103706957217283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101284825930943218552579421 37981809724103706957217283)
          ·
            refine ⟨56972714586155560435825925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37981809724103706957217283 56972714586155560435825925)
            ·
              refine ⟨10682383984904167581717361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56972714586155560435825925 10682383984904167581717361)
              ·
                refine ⟨8011787988678125686288021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10682383984904167581717361 8011787988678125686288021)
                ·
                  refine ⟨375552561969287141544751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8011787988678125686288021 375552561969287141544751)
                  ·
                    rfl

theorem cell23_6582474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_6582474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582474 prefixEnd_6582474 := by exact prefixLift 6582474
  have htrace : WordTrace (prefixWord ++ tailWord_6582474) baseStart_6582474 baseEnd_6582474 := by
    simpa [prefixWord, tailWord_6582474, baseEnd_6582474] using wordTrace_append hprefix tailTrace_6582474
  have hstable : (prefixWord ++ tailWord_6582474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582474).length < 2 ^ (prefixWord ++ tailWord_6582474).sum := by decide
  have hdescent : baseEnd_6582474 < baseStart_6582474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582478 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_6582478 : Nat := 118140960795 + 6582478 * 2 ^ 59
def prefixEnd_6582478 : Nat := 4983230072969 + 3 ^ 40 * 6582478 * 2
def baseEnd_6582478 : Nat := 1126658370548734086084247

theorem tailTrace_6582478 : CollatzResearch.WordTrace tailWord_6582478 prefixEnd_6582478 1126658370548734086084247 := by
  unfold tailWord_6582478
  simp only [CollatzResearch.WordTrace]
  refine ⟨30010337030851734823194511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160055130831209252390370725 30010337030851734823194511)
  ·
    refine ⟨45015505546277602234791767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30010337030851734823194511 45015505546277602234791767)
    ·
      refine ⟨67523258319416403352187651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45015505546277602234791767 67523258319416403352187651)
      ·
        refine ⟨101284887479124605028281477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67523258319416403352187651 101284887479124605028281477)
        ·
          refine ⟨18990916402335863442802777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101284887479124605028281477 18990916402335863442802777)
          ·
            refine ⟨14243187301751897582102083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18990916402335863442802777 14243187301751897582102083)
            ·
              refine ⟨21364780952627846373153125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243187301751897582102083 21364780952627846373153125)
              ·
                refine ⟨4005896428617721194966211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21364780952627846373153125 4005896428617721194966211)
                ·
                  refine ⟨6008844642926581792449317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005896428617721194966211 6008844642926581792449317)
                  ·
                    refine ⟨1126658370548734086084247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008844642926581792449317 1126658370548734086084247)
                    ·
                      rfl

theorem cell23_6582478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_6582478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582478 prefixEnd_6582478 := by exact prefixLift 6582478
  have htrace : WordTrace (prefixWord ++ tailWord_6582478) baseStart_6582478 baseEnd_6582478 := by
    simpa [prefixWord, tailWord_6582478, baseEnd_6582478] using wordTrace_append hprefix tailTrace_6582478
  have hstable : (prefixWord ++ tailWord_6582478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582478).length < 2 ^ (prefixWord ++ tailWord_6582478).sum := by decide
  have hdescent : baseEnd_6582478 < baseStart_6582478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582497 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6582497 : Nat := 118140960795 + 6582497 * 2 ^ 59
def prefixEnd_6582497 : Nat := 4983230072969 + 3 ^ 40 * 6582497 * 2
def baseEnd_6582497 : Nat := 3379984867778637683915153

theorem tailTrace_6582497 : CollatzResearch.WordTrace tailWord_6582497 prefixEnd_6582497 3379984867778637683915153 := by
  unfold tailWord_6582497
  simp only [CollatzResearch.WordTrace]
  refine ⟨240083389233745044830497745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160055592822496696553665163 240083389233745044830497745)
  ·
    refine ⟨180062541925308783622873309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240083389233745044830497745 180062541925308783622873309)
    ·
      refine ⟨67523453221990793858577491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180062541925308783622873309 67523453221990793858577491)
      ·
        refine ⟨101285179832986190787866237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67523453221990793858577491 101285179832986190787866237)
        ·
          refine ⟨37981942437369821545449839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101285179832986190787866237 37981942437369821545449839)
          ·
            refine ⟨56972913656054732318174759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37981942437369821545449839 56972913656054732318174759)
            ·
              refine ⟨85459370484082098477262139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56972913656054732318174759 85459370484082098477262139)
              ·
                refine ⟨128189055726123147715893209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85459370484082098477262139 128189055726123147715893209)
                ·
                  refine ⟨96141791794592360786919907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128189055726123147715893209 96141791794592360786919907)
                  ·
                    refine ⟨144212687691888541180379861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96141791794592360786919907 144212687691888541180379861)
                    ·
                      refine ⟨3379984867778637683915153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144212687691888541180379861 3379984867778637683915153)
                      ·
                        rfl

theorem cell23_6582497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6582497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582497 prefixEnd_6582497 := by exact prefixLift 6582497
  have htrace : WordTrace (prefixWord ++ tailWord_6582497) baseStart_6582497 baseEnd_6582497 := by
    simpa [prefixWord, tailWord_6582497, baseEnd_6582497] using wordTrace_append hprefix tailTrace_6582497
  have hstable : (prefixWord ++ tailWord_6582497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582497).length < 2 ^ (prefixWord ++ tailWord_6582497).sum := by decide
  have hdescent : baseEnd_6582497 < baseStart_6582497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582501 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6582501 : Nat := 118140960795 + 6582501 * 2 ^ 59
def prefixEnd_6582501 : Nat := 4983230072969 + 3 ^ 40 * 6582501 * 2
def baseEnd_6582501 : Nat := 3379986921701255668265135

theorem tailTrace_6582501 : CollatzResearch.WordTrace tailWord_6582501 prefixEnd_6582501 3379986921701255668265135 := by
  unfold tailWord_6582501
  simp only [CollatzResearch.WordTrace]
  refine ⟨240083535125730553513643357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160055690083820369009095571 240083535125730553513643357)
  ·
    refine ⟨90031325672148957567616259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240083535125730553513643357 90031325672148957567616259)
    ·
      refine ⟨135046988508223436351424389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90031325672148957567616259 135046988508223436351424389)
      ·
        refine ⟨25321310345291894315892073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135046988508223436351424389 25321310345291894315892073)
        ·
          refine ⟨18990982758968920736919055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25321310345291894315892073 18990982758968920736919055)
          ·
            refine ⟨28486474138453381105378583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18990982758968920736919055 28486474138453381105378583)
            ·
              refine ⟨42729711207680071658067875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28486474138453381105378583 42729711207680071658067875)
              ·
                refine ⟨64094566811520107487101813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42729711207680071658067875 64094566811520107487101813)
                ·
                  refine ⟨6008865638580010076915795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64094566811520107487101813 6008865638580010076915795)
                  ·
                    refine ⟨9013298457870015115373693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008865638580010076915795 9013298457870015115373693)
                    ·
                      refine ⟨3379986921701255668265135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013298457870015115373693 3379986921701255668265135)
                      ·
                        rfl

theorem cell23_6582501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6582501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582501 prefixEnd_6582501 := by exact prefixLift 6582501
  have htrace : WordTrace (prefixWord ++ tailWord_6582501) baseStart_6582501 baseEnd_6582501 := by
    simpa [prefixWord, tailWord_6582501, baseEnd_6582501] using wordTrace_append hprefix tailTrace_6582501
  have hstable : (prefixWord ++ tailWord_6582501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582501).length < 2 ^ (prefixWord ++ tailWord_6582501).sum := by decide
  have hdescent : baseEnd_6582501 < baseStart_6582501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582504 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6582504 : Nat := 118140960795 + 6582504 * 2 ^ 59
def prefixEnd_6582504 : Nat := 4983230072969 + 3 ^ 40 * 6582504 * 2
def baseEnd_6582504 : Nat := 1126662820714406385509207

theorem tailTrace_6582504 : CollatzResearch.WordTrace tailWord_6582504 prefixEnd_6582504 1126662820714406385509207 := by
  unfold tailWord_6582504
  simp only [CollatzResearch.WordTrace]
  refine ⟨120041822272359842513001283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160055763029813123350668377 120041822272359842513001283)
  ·
    refine ⟨180062733408539763769501925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120041822272359842513001283 180062733408539763769501925)
    ·
      refine ⟨33761762514101205706781611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180062733408539763769501925 33761762514101205706781611)
      ·
        refine ⟨50642643771151808560172417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33761762514101205706781611 50642643771151808560172417)
        ·
          refine ⟨37981982828363856420129313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50642643771151808560172417 37981982828363856420129313)
          ·
            refine ⟨28486487121272892315096985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37981982828363856420129313 28486487121272892315096985)
            ·
              refine ⟨21364865340954669236322739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28486487121272892315096985 21364865340954669236322739)
              ·
                refine ⟨32047298011432003854484109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364865340954669236322739 32047298011432003854484109)
                ·
                  refine ⟨12017736754287001445431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32047298011432003854484109 12017736754287001445431541)
                  ·
                    refine ⟨1126662820714406385509207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12017736754287001445431541 1126662820714406385509207)
                    ·
                      rfl

theorem cell23_6582504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6582504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582504 prefixEnd_6582504 := by exact prefixLift 6582504
  have htrace : WordTrace (prefixWord ++ tailWord_6582504) baseStart_6582504 baseEnd_6582504 := by
    simpa [prefixWord, tailWord_6582504, baseEnd_6582504] using wordTrace_append hprefix tailTrace_6582504
  have hstable : (prefixWord ++ tailWord_6582504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582504).length < 2 ^ (prefixWord ++ tailWord_6582504).sum := by decide
  have hdescent : baseEnd_6582504 < baseStart_6582504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582511 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 5, 2]
def baseStart_6582511 : Nat := 118140960795 + 6582511 * 2 ^ 59
def prefixEnd_6582511 : Nat := 4983230072969 + 3 ^ 40 * 6582511 * 2
def baseEnd_6582511 : Nat := 3379992056507800629140089

theorem tailTrace_6582511 : CollatzResearch.WordTrace tailWord_6582511 prefixEnd_6582511 3379992056507800629140089 := by
  unfold tailWord_6582511
  simp only [CollatzResearch.WordTrace]
  refine ⟨240083899855694325221507387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160055933237129550147671591 240083899855694325221507387)
  ·
    refine ⟨360125849783541487832261081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240083899855694325221507387 360125849783541487832261081)
    ·
      refine ⟨270094387337656115874195811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360125849783541487832261081 270094387337656115874195811)
      ·
        refine ⟨405141581006484173811293717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270094387337656115874195811 405141581006484173811293717)
        ·
          refine ⟨18991011609678945647404393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405141581006484173811293717 18991011609678945647404393)
          ·
            refine ⟨14243258707259209235553295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18991011609678945647404393 14243258707259209235553295)
            ·
              refine ⟨21364888060888813853329943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243258707259209235553295 21364888060888813853329943)
              ·
                refine ⟨32047332091333220779994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364888060888813853329943 32047332091333220779994915)
                ·
                  refine ⟨48070998136999831169992373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32047332091333220779994915 48070998136999831169992373)
                  ·
                    refine ⟨4506656075343734172186785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48070998136999831169992373 4506656075343734172186785)
                    ·
                      refine ⟨3379992056507800629140089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506656075343734172186785 3379992056507800629140089)
                      ·
                        rfl

theorem cell23_6582511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5, 2].length) (baseStart_6582511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582511 prefixEnd_6582511 := by exact prefixLift 6582511
  have htrace : WordTrace (prefixWord ++ tailWord_6582511) baseStart_6582511 baseEnd_6582511 := by
    simpa [prefixWord, tailWord_6582511, baseEnd_6582511] using wordTrace_append hprefix tailTrace_6582511
  have hstable : (prefixWord ++ tailWord_6582511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582511).length < 2 ^ (prefixWord ++ tailWord_6582511).sum := by decide
  have hdescent : baseEnd_6582511 < baseStart_6582511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582535 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6582535 : Nat := 118140960795 + 6582535 * 2 ^ 59
def prefixEnd_6582535 : Nat := 4983230072969 + 3 ^ 40 * 6582535 * 2
def baseEnd_6582535 : Nat := 3380004380043508535239979

theorem tailTrace_6582535 : CollatzResearch.WordTrace tailWord_6582535 prefixEnd_6582535 3380004380043508535239979 := by
  unfold tailWord_6582535
  simp only [CollatzResearch.WordTrace]
  refine ⟨240084775207607377320381059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160056516805071584880254039 240084775207607377320381059)
  ·
    refine ⟨360127162811411065980571589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240084775207607377320381059 360127162811411065980571589)
    ·
      refine ⟨67523843027139574871357173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360127162811411065980571589 67523843027139574871357173)
      ·
        refine ⟨6330360283794335144189735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67523843027139574871357173 6330360283794335144189735)
        ·
          refine ⟨9495540425691502716284603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330360283794335144189735 9495540425691502716284603)
          ·
            refine ⟨14243310638537254074426905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495540425691502716284603 14243310638537254074426905)
            ·
              refine ⟨10682482978902940555820179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14243310638537254074426905 10682482978902940555820179)
              ·
                refine ⟨16023724468354410833730269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682482978902940555820179 16023724468354410833730269)
                ·
                  refine ⟨6008896675632904062648851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16023724468354410833730269 6008896675632904062648851)
                  ·
                    refine ⟨9013345013449356093973277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008896675632904062648851 9013345013449356093973277)
                    ·
                      refine ⟨3380004380043508535239979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013345013449356093973277 3380004380043508535239979)
                      ·
                        rfl

theorem cell23_6582535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6582535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582535 prefixEnd_6582535 := by exact prefixLift 6582535
  have htrace : WordTrace (prefixWord ++ tailWord_6582535) baseStart_6582535 baseEnd_6582535 := by
    simpa [prefixWord, tailWord_6582535, baseEnd_6582535] using wordTrace_append hprefix tailTrace_6582535
  have hstable : (prefixWord ++ tailWord_6582535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582535).length < 2 ^ (prefixWord ++ tailWord_6582535).sum := by decide
  have hdescent : baseEnd_6582535 < baseStart_6582535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582551 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 6]
def baseStart_6582551 : Nat := 118140960795 + 6582551 * 2 ^ 59
def prefixEnd_6582551 : Nat := 4983230072969 + 3 ^ 40 * 6582551 * 2
def baseEnd_6582551 : Nat := 1126670865244660157546635

theorem tailTrace_6582551 : CollatzResearch.WordTrace tailWord_6582551 prefixEnd_6582551 1126670865244660157546635 := by
  unfold tailWord_6582551
  simp only [CollatzResearch.WordTrace]
  refine ⟨240085358775549412052963507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160056905850366274701975671 240085358775549412052963507)
  ·
    refine ⟨360128038163324118079445261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240085358775549412052963507 360128038163324118079445261)
    ·
      refine ⟨135048014311246544279791973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360128038163324118079445261 135048014311246544279791973)
      ·
        refine ⟨25321502683358727052460995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135048014311246544279791973 25321502683358727052460995)
        ·
          refine ⟨37982254025038090578691493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25321502683358727052460995 37982254025038090578691493)
          ·
            refine ⟨7121672629694641983504655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37982254025038090578691493 7121672629694641983504655)
            ·
              refine ⟨10682508944541962975256983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121672629694641983504655 10682508944541962975256983)
              ·
                refine ⟨16023763416812944462885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682508944541962975256983 16023763416812944462885475)
                ·
                  refine ⟨24035645125219416694328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16023763416812944462885475 24035645125219416694328213)
                  ·
                    refine ⟨1126670865244660157546635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24035645125219416694328213 1126670865244660157546635)
                    ·
                      rfl

theorem cell23_6582551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_6582551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582551 prefixEnd_6582551 := by exact prefixLift 6582551
  have htrace : WordTrace (prefixWord ++ tailWord_6582551) baseStart_6582551 baseEnd_6582551 := by
    simpa [prefixWord, tailWord_6582551, baseEnd_6582551] using wordTrace_append hprefix tailTrace_6582551
  have hstable : (prefixWord ++ tailWord_6582551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582551).length < 2 ^ (prefixWord ++ tailWord_6582551).sum := by decide
  have hdescent : baseEnd_6582551 < baseStart_6582551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582561 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6582561 : Nat := 118140960795 + 6582561 * 2 ^ 59
def prefixEnd_6582561 : Nat := 4983230072969 + 3 ^ 40 * 6582561 * 2
def baseEnd_6582561 : Nat := 3380017730540525433514859

theorem tailTrace_6582561 : CollatzResearch.WordTrace tailWord_6582561 prefixEnd_6582561 3380017730540525433514859 := by
  unfold tailWord_6582561
  simp only [CollatzResearch.WordTrace]
  refine ⟨240085723505513183760827537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160057149003675455840551691 240085723505513183760827537)
  ·
    refine ⟨180064292629134887820620653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240085723505513183760827537 180064292629134887820620653)
    ·
      refine ⟨67524109735925582932732745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180064292629134887820620653 67524109735925582932732745)
      ·
        refine ⟨50643082301944187199549559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67524109735925582932732745 50643082301944187199549559)
        ·
          refine ⟨75964623452916280799324339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50643082301944187199549559 75964623452916280799324339)
          ·
            refine ⟨113946935179374421198986509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75964623452916280799324339 113946935179374421198986509)
            ·
              refine ⟨42730100692265407949619941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113946935179374421198986509 42730100692265407949619941)
              ·
                refine ⟨8011893879799763990553739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42730100692265407949619941 8011893879799763990553739)
                ·
                  refine ⟨12017840819699645985830609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011893879799763990553739 12017840819699645985830609)
                  ·
                    refine ⟨9013380614774734489372957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12017840819699645985830609 9013380614774734489372957)
                    ·
                      refine ⟨3380017730540525433514859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013380614774734489372957 3380017730540525433514859)
                      ·
                        rfl

theorem cell23_6582561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6582561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582561 prefixEnd_6582561 := by exact prefixLift 6582561
  have htrace : WordTrace (prefixWord ++ tailWord_6582561) baseStart_6582561 baseEnd_6582561 := by
    simpa [prefixWord, tailWord_6582561, baseEnd_6582561] using wordTrace_append hprefix tailTrace_6582561
  have hstable : (prefixWord ++ tailWord_6582561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582561).length < 2 ^ (prefixWord ++ tailWord_6582561).sum := by decide
  have hdescent : baseEnd_6582561 < baseStart_6582561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582564 : List Nat := [2, 3, 1, 3, 1, 3, 1, 9]
def baseStart_6582564 : Nat := 118140960795 + 6582564 * 2 ^ 59
def prefixEnd_6582564 : Nat := 4983230072969 + 3 ^ 40 * 6582564 * 2
def baseEnd_6582564 : Nat := 125185898925277367473235

theorem tailTrace_6582564 : CollatzResearch.WordTrace tailWord_6582564 prefixEnd_6582564 125185898925277367473235 := by
  unfold tailWord_6582564
  simp only [CollatzResearch.WordTrace]
  refine ⟨120042916462251157636593373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160057221949668210182124497 120042916462251157636593373)
  ·
    refine ⟨45016093673344184113722515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120042916462251157636593373 45016093673344184113722515)
    ·
      refine ⟨67524140510016276170583773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45016093673344184113722515 67524140510016276170583773)
      ·
        refine ⟨25321552691256103563968915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67524140510016276170583773 25321552691256103563968915)
        ·
          refine ⟨37982329036884155345953373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25321552691256103563968915 37982329036884155345953373)
          ·
            refine ⟨14243373388831558254732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37982329036884155345953373 14243373388831558254732515)
            ·
              refine ⟨21365060083247337382098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243373388831558254732515 21365060083247337382098773)
              ·
                refine ⟨125185898925277367473235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21365060083247337382098773 125185898925277367473235)
                ·
                  rfl

theorem cell23_6582564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 9].length) (baseStart_6582564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582564 prefixEnd_6582564 := by exact prefixLift 6582564
  have htrace : WordTrace (prefixWord ++ tailWord_6582564) baseStart_6582564 baseEnd_6582564 := by
    simpa [prefixWord, tailWord_6582564, baseEnd_6582564] using wordTrace_append hprefix tailTrace_6582564
  have hstable : (prefixWord ++ tailWord_6582564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582564).length < 2 ^ (prefixWord ++ tailWord_6582564).sum := by decide
  have hdescent : baseEnd_6582564 < baseStart_6582564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582575 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 1, 2, 2]
def baseStart_6582575 : Nat := 118140960795 + 6582575 * 2 ^ 59
def prefixEnd_6582575 : Nat := 4983230072969 + 3 ^ 40 * 6582575 * 2
def baseEnd_6582575 : Nat := 3380024919269688378739795

theorem tailTrace_6582575 : CollatzResearch.WordTrace tailWord_6582575 prefixEnd_6582575 3380024919269688378739795 := by
  unfold tailWord_6582575
  simp only [CollatzResearch.WordTrace]
  refine ⟨240086234127462464151837179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160057489418308309434558119 240086234127462464151837179)
  ·
    refine ⟨360129351191193696227755769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240086234127462464151837179 360129351191193696227755769)
    ·
      refine ⟨270097013393395272170816827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360129351191193696227755769 270097013393395272170816827)
      ·
        refine ⟨405145520090092908256225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270097013393395272170816827 405145520090092908256225241)
        ·
          refine ⟨303859140067569681192168931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405145520090092908256225241 303859140067569681192168931)
          ·
            refine ⟨455788710101354521788253397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303859140067569681192168931 455788710101354521788253397)
            ·
              refine ⟨10682547893000496604412189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 455788710101354521788253397 10682547893000496604412189)
              ·
                refine ⟨4005955459875186226654571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10682547893000496604412189 4005955459875186226654571)
                ·
                  refine ⟨6008933189812779339981857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005955459875186226654571 6008933189812779339981857)
                  ·
                    refine ⟨4506699892359584504986393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6008933189812779339981857 4506699892359584504986393)
                    ·
                      refine ⟨3380024919269688378739795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506699892359584504986393 3380024919269688378739795)
                      ·
                        rfl

theorem cell23_6582575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 2, 2].length) (baseStart_6582575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582575 prefixEnd_6582575 := by exact prefixLift 6582575
  have htrace : WordTrace (prefixWord ++ tailWord_6582575) baseStart_6582575 baseEnd_6582575 := by
    simpa [prefixWord, tailWord_6582575, baseEnd_6582575] using wordTrace_append hprefix tailTrace_6582575
  have hstable : (prefixWord ++ tailWord_6582575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582575).length < 2 ^ (prefixWord ++ tailWord_6582575).sum := by decide
  have hdescent : baseEnd_6582575 < baseStart_6582575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582591 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_6582591 : Nat := 118140960795 + 6582591 * 2 ^ 59
def prefixEnd_6582591 : Nat := 4983230072969 + 3 ^ 40 * 6582591 * 2
def baseEnd_6582591 : Nat := 3380033134960160316139721

theorem tailTrace_6582591 : CollatzResearch.WordTrace tailWord_6582591 prefixEnd_6582591 3380033134960160316139721 := by
  unfold tailWord_6582591
  simp only [CollatzResearch.WordTrace]
  refine ⟨240086817695404498884419627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160057878463602999256279751 240086817695404498884419627)
  ·
    refine ⟨360130226543106748326629441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240086817695404498884419627 360130226543106748326629441)
    ·
      refine ⟨270097669907330061244972081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360130226543106748326629441 270097669907330061244972081)
      ·
        refine ⟨202573252430497545933729061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270097669907330061244972081 202573252430497545933729061)
        ·
          refine ⟨37982484830718289862574199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202573252430497545933729061 37982484830718289862574199)
          ·
            refine ⟨56973727246077434793861299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37982484830718289862574199 56973727246077434793861299)
            ·
              refine ⟨85460590869116152190791949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56973727246077434793861299 85460590869116152190791949)
              ·
                refine ⟨32047721575918557071546981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85460590869116152190791949 32047721575918557071546981)
                ·
                  refine ⟨6008947795484729450915059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32047721575918557071546981 6008947795484729450915059)
                  ·
                    refine ⟨9013421693227094176372589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008947795484729450915059 9013421693227094176372589)
                    ·
                      refine ⟨3380033134960160316139721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013421693227094176372589 3380033134960160316139721)
                      ·
                        rfl

theorem cell23_6582591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_6582591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582591 prefixEnd_6582591 := by exact prefixLift 6582591
  have htrace : WordTrace (prefixWord ++ tailWord_6582591) baseStart_6582591 baseEnd_6582591 := by
    simpa [prefixWord, tailWord_6582591, baseEnd_6582591] using wordTrace_append hprefix tailTrace_6582591
  have hstable : (prefixWord ++ tailWord_6582591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582591).length < 2 ^ (prefixWord ++ tailWord_6582591).sum := by decide
  have hdescent : baseEnd_6582591 < baseStart_6582591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582601 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 3, 3, 2]
def baseStart_6582601 : Nat := 118140960795 + 6582601 * 2 ^ 59
def prefixEnd_6582601 : Nat := 4983230072969 + 3 ^ 40 * 6582601 * 2
def baseEnd_6582601 : Nat := 3380038269766705277014675

theorem tailTrace_6582601 : CollatzResearch.WordTrace tailWord_6582601 prefixEnd_6582601 3380038269766705277014675 := by
  unfold tailWord_6582601
  simp only [CollatzResearch.WordTrace]
  refine ⟨240087182425368270592283657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160058121616912180394855771 240087182425368270592283657)
  ·
    refine ⟨180065386819026202944212743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240087182425368270592283657 180065386819026202944212743)
    ·
      refine ⟨270098080228539304416319115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180065386819026202944212743 270098080228539304416319115)
      ·
        refine ⟨405147120342808956624478673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270098080228539304416319115 405147120342808956624478673)
        ·
          refine ⟨303860340257106717468359005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405147120342808956624478673 303860340257106717468359005)
          ·
            refine ⟨113947627596415019050634627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303860340257106717468359005 113947627596415019050634627)
            ·
              refine ⟨170921441394622528575951941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113947627596415019050634627 170921441394622528575951941)
              ·
                refine ⟨32047770261491724107990989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170921441394622528575951941 32047770261491724107990989)
                ·
                  refine ⟨12017913848059396540496621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32047770261491724107990989 12017913848059396540496621)
                  ·
                    refine ⟨4506717693022273702686233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12017913848059396540496621 4506717693022273702686233)
                    ·
                      refine ⟨3380038269766705277014675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506717693022273702686233 3380038269766705277014675)
                      ·
                        rfl

theorem cell23_6582601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3, 2].length) (baseStart_6582601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582601 prefixEnd_6582601 := by exact prefixLift 6582601
  have htrace : WordTrace (prefixWord ++ tailWord_6582601) baseStart_6582601 baseEnd_6582601 := by
    simpa [prefixWord, tailWord_6582601, baseEnd_6582601] using wordTrace_append hprefix tailTrace_6582601
  have hstable : (prefixWord ++ tailWord_6582601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582601).length < 2 ^ (prefixWord ++ tailWord_6582601).sum := by decide
  have hdescent : baseEnd_6582601 < baseStart_6582601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582608 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_6582608 : Nat := 118140960795 + 6582608 * 2 ^ 59
def prefixEnd_6582608 : Nat := 4983230072969 + 3 ^ 40 * 6582608 * 2
def baseEnd_6582608 : Nat := 3380041864131286749627143

theorem tailTrace_6582608 : CollatzResearch.WordTrace tailWord_6582608 prefixEnd_6582608 3380041864131286749627143 := by
  unfold tailWord_6582608
  simp only [CollatzResearch.WordTrace]
  refine ⟨120043718868171455393894239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160058291824228607191858985 120043718868171455393894239)
  ·
    refine ⟨180065578302257183090841359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120043718868171455393894239 180065578302257183090841359)
    ·
      refine ⟨270098367453385774636262039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180065578302257183090841359 270098367453385774636262039)
      ·
        refine ⟨405147551180078661954393059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270098367453385774636262039 405147551180078661954393059)
        ·
          refine ⟨607721326770117992931589589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405147551180078661954393059 607721326770117992931589589)
          ·
            refine ⟨14243468596174640459334131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 607721326770117992931589589 14243468596174640459334131)
            ·
              refine ⟨21365202894261960689001197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243468596174640459334131 21365202894261960689001197)
              ·
                refine ⟨8011951085348235258375449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21365202894261960689001197 8011951085348235258375449)
                ·
                  refine ⟨6008963314011176443781587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8011951085348235258375449 6008963314011176443781587)
                  ·
                    refine ⟨9013444971016764665672381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6008963314011176443781587 9013444971016764665672381)
                    ·
                      refine ⟨3380041864131286749627143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013444971016764665672381 3380041864131286749627143)
                      ·
                        rfl

theorem cell23_6582608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_6582608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582608 prefixEnd_6582608 := by exact prefixLift 6582608
  have htrace : WordTrace (prefixWord ++ tailWord_6582608) baseStart_6582608 baseEnd_6582608 := by
    simpa [prefixWord, tailWord_6582608, baseEnd_6582608] using wordTrace_append hprefix tailTrace_6582608
  have hstable : (prefixWord ++ tailWord_6582608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582608).length < 2 ^ (prefixWord ++ tailWord_6582608).sum := by decide
  have hdescent : baseEnd_6582608 < baseStart_6582608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582665 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 2, 2, 2]
def baseStart_6582665 : Nat := 118140960795 + 6582665 * 2 ^ 59
def prefixEnd_6582665 : Nat := 4983230072969 + 3 ^ 40 * 6582665 * 2
def baseEnd_6582665 : Nat := 3380071132528593026614381

theorem tailTrace_6582665 : CollatzResearch.WordTrace tailWord_6582665 prefixEnd_6582665 3380071132528593026614381 := by
  unfold tailWord_6582665
  simp only [CollatzResearch.WordTrace]
  refine ⟨240089516697136409522613449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160059677798090939681742299 240089516697136409522613449)
  ·
    refine ⟨180067137522852307141960087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240089516697136409522613449 180067137522852307141960087)
    ·
      refine ⟨270100706284278460712940131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180067137522852307141960087 270100706284278460712940131)
      ·
        refine ⟨405151059426417691069410197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270100706284278460712940131 405151059426417691069410197)
        ·
          refine ⟨18991455910613329268878603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405151059426417691069410197 18991455910613329268878603)
          ·
            refine ⟨28487183865919993903317905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18991455910613329268878603 28487183865919993903317905)
            ·
              refine ⟨21365387899439995427488429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28487183865919993903317905 21365387899439995427488429)
              ·
                refine ⟨8012020462289998285308161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21365387899439995427488429 8012020462289998285308161)
                ·
                  refine ⟨6009015346717498713981121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8012020462289998285308161 6009015346717498713981121)
                  ·
                    refine ⟨4506761510038124035485841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6009015346717498713981121 4506761510038124035485841)
                    ·
                      refine ⟨3380071132528593026614381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4506761510038124035485841 3380071132528593026614381)
                      ·
                        rfl

theorem cell23_6582665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2, 2].length) (baseStart_6582665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582665 prefixEnd_6582665 := by exact prefixLift 6582665
  have htrace : WordTrace (prefixWord ++ tailWord_6582665) baseStart_6582665 baseEnd_6582665 := by
    simpa [prefixWord, tailWord_6582665, baseEnd_6582665] using wordTrace_append hprefix tailTrace_6582665
  have hstable : (prefixWord ++ tailWord_6582665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582665).length < 2 ^ (prefixWord ++ tailWord_6582665).sum := by decide
  have hdescent : baseEnd_6582665 < baseStart_6582665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582688 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 5]
def baseStart_6582688 : Nat := 118140960795 + 6582688 * 2 ^ 59
def prefixEnd_6582688 : Nat := 4983230072969 + 3 ^ 40 * 6582688 * 2
def baseEnd_6582688 : Nat := 375564771398182937402975

theorem tailTrace_6582688 : CollatzResearch.WordTrace tailWord_6582688 prefixEnd_6582688 375564771398182937402975 := by
  unfold tailWord_6582688
  simp only [CollatzResearch.WordTrace]
  refine ⟨120045177788026542225350359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160060237050702056300467145 120045177788026542225350359)
  ·
    refine ⟨180067766682039813338025539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120045177788026542225350359 180067766682039813338025539)
    ·
      refine ⟨270101650023059720007038309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180067766682039813338025539 270101650023059720007038309)
      ·
        refine ⟨50644059379323697501319683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270101650023059720007038309 50644059379323697501319683)
        ·
          refine ⟨75966089068985546251979525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50644059379323697501319683 75966089068985546251979525)
          ·
            refine ⟨14243641700434789922246161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75966089068985546251979525 14243641700434789922246161)
            ·
              refine ⟨10682731275326092441684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14243641700434789922246161 10682731275326092441684621)
              ·
                refine ⟨4006024228247284665631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10682731275326092441684621 4006024228247284665631733)
                ·
                  refine ⟨375564771398182937402975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4006024228247284665631733 375564771398182937402975)
                  ·
                    rfl

theorem cell23_6582688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 5].length) (baseStart_6582688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582688 prefixEnd_6582688 := by exact prefixLift 6582688
  have htrace : WordTrace (prefixWord ++ tailWord_6582688) baseStart_6582688 baseEnd_6582688 := by
    simpa [prefixWord, tailWord_6582688, baseEnd_6582688] using wordTrace_append hprefix tailTrace_6582688
  have hstable : (prefixWord ++ tailWord_6582688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582688).length < 2 ^ (prefixWord ++ tailWord_6582688).sum := by decide
  have hdescent : baseEnd_6582688 < baseStart_6582688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582765 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_6582765 : Nat := 118140960795 + 6582765 * 2 ^ 59
def prefixEnd_6582765 : Nat := 4983230072969 + 3 ^ 40 * 6582765 * 2
def baseEnd_6582765 : Nat := 1126707493531347545121307

theorem tailTrace_6582765 : CollatzResearch.WordTrace tailWord_6582765 prefixEnd_6582765 1126707493531347545121307 := by
  unfold tailWord_6582765
  simp only [CollatzResearch.WordTrace]
  refine ⟨240093163996774126601253749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160062109331182751067502499 240093163996774126601253749)
  ·
    refine ⟨22508734124697574368867539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240093163996774126601253749 22508734124697574368867539)
    ·
      refine ⟨33763101187046361553301309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22508734124697574368867539 33763101187046361553301309)
      ·
        refine ⟨12661162945142385582487991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33763101187046361553301309 12661162945142385582487991)
        ·
          refine ⟨18991744417713578373731987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661162945142385582487991 18991744417713578373731987)
          ·
            refine ⟨28487616626570367560597981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18991744417713578373731987 28487616626570367560597981)
            ·
              refine ⟨10682856234963887835224243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28487616626570367560597981 10682856234963887835224243)
              ·
                refine ⟨16024284352445831752836365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682856234963887835224243 16024284352445831752836365)
                ·
                  refine ⟨6009106632167186907313637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16024284352445831752836365 6009106632167186907313637)
                  ·
                    refine ⟨1126707493531347545121307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009106632167186907313637 1126707493531347545121307)
                    ·
                      rfl

theorem cell23_6582765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_6582765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582765 prefixEnd_6582765 := by exact prefixLift 6582765
  have htrace : WordTrace (prefixWord ++ tailWord_6582765) baseStart_6582765 baseEnd_6582765 := by
    simpa [prefixWord, tailWord_6582765, baseEnd_6582765] using wordTrace_append hprefix tailTrace_6582765
  have hstable : (prefixWord ++ tailWord_6582765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582765).length < 2 ^ (prefixWord ++ tailWord_6582765).sum := by decide
  have hdescent : baseEnd_6582765 < baseStart_6582765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582816 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 1, 4]
def baseStart_6582816 : Nat := 118140960795 + 6582816 * 2 ^ 59
def prefixEnd_6582816 : Nat := 4983230072969 + 3 ^ 40 * 6582816 * 2
def baseEnd_6582816 : Nat := 1126716222702473978608729

theorem tailTrace_6582816 : CollatzResearch.WordTrace tailWord_6582816 prefixEnd_6582816 1126716222702473978608729 := by
  unfold tailWord_6582816
  simp only [CollatzResearch.WordTrace]
  refine ⟨120047512059794681155680151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160063349413059574874240201 120047512059794681155680151)
  ·
    refine ⟨180071268089692021733520227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120047512059794681155680151 180071268089692021733520227)
    ·
      refine ⟨270106902134538032600280341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180071268089692021733520227 270106902134538032600280341)
      ·
        refine ⟨12661261037556470278138141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270106902134538032600280341 12661261037556470278138141)
        ·
          refine ⟨4747972889083676354301803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12661261037556470278138141 4747972889083676354301803)
          ·
            refine ⟨7121959333625514531452705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747972889083676354301803 7121959333625514531452705)
            ·
              refine ⟨5341469500219135898589529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121959333625514531452705 5341469500219135898589529)
              ·
                refine ⟨4006102125164351923942147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341469500219135898589529 4006102125164351923942147)
                ·
                  refine ⟨6009153187746527885913221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006102125164351923942147 6009153187746527885913221)
                  ·
                    refine ⟨1126716222702473978608729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009153187746527885913221 1126716222702473978608729)
                    ·
                      rfl

theorem cell23_6582816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_6582816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582816 prefixEnd_6582816 := by exact prefixLift 6582816
  have htrace : WordTrace (prefixWord ++ tailWord_6582816) baseStart_6582816 baseEnd_6582816 := by
    simpa [prefixWord, tailWord_6582816, baseEnd_6582816] using wordTrace_append hprefix tailTrace_6582816
  have hstable : (prefixWord ++ tailWord_6582816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582816).length < 2 ^ (prefixWord ++ tailWord_6582816).sum := by decide
  have hdescent : baseEnd_6582816 < baseStart_6582816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582848 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_6582848 : Nat := 118140960795 + 6582848 * 2 ^ 59
def prefixEnd_6582848 : Nat := 4983230072969 + 3 ^ 40 * 6582848 * 2
def baseEnd_6582848 : Nat := 3380165099488365810626039

theorem tailTrace_6582848 : CollatzResearch.WordTrace tailWord_6582848 prefixEnd_6582848 3380165099488365810626039 := by
  unfold tailWord_6582848
  simp only [CollatzResearch.WordTrace]
  refine ⟨120048095627736715888262599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160064127503648954517683465 120048095627736715888262599)
  ·
    refine ⟨180072143441605073832393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120048095627736715888262599 180072143441605073832393899)
    ·
      refine ⟨270108215162407610748590849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180072143441605073832393899 270108215162407610748590849)
      ·
        refine ⟨202581161371805708061443137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270108215162407610748590849 202581161371805708061443137)
        ·
          refine ⟨151935871028854281046082353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202581161371805708061443137 151935871028854281046082353)
          ·
            refine ⟨113951903271640710784561765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151935871028854281046082353 113951903271640710784561765)
            ·
              refine ⟨21365981863432633272105331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113951903271640710784561765 21365981863432633272105331)
              ·
                refine ⟨32048972795148949908157997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21365981863432633272105331 32048972795148949908157997)
                ·
                  refine ⟨12018364798180856215559249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32048972795148949908157997 12018364798180856215559249)
                  ·
                    refine ⟨9013773598635642161669437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12018364798180856215559249 9013773598635642161669437)
                    ·
                      refine ⟨3380165099488365810626039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013773598635642161669437 3380165099488365810626039)
                      ·
                        rfl

theorem cell23_6582848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_6582848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582848 prefixEnd_6582848 := by exact prefixLift 6582848
  have htrace : WordTrace (prefixWord ++ tailWord_6582848) baseStart_6582848 baseEnd_6582848 := by
    simpa [prefixWord, tailWord_6582848, baseEnd_6582848] using wordTrace_append hprefix tailTrace_6582848
  have hstable : (prefixWord ++ tailWord_6582848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582848).length < 2 ^ (prefixWord ++ tailWord_6582848).sum := by decide
  have hdescent : baseEnd_6582848 < baseStart_6582848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582858 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_6582858 : Nat := 118140960795 + 6582858 * 2 ^ 59
def prefixEnd_6582858 : Nat := 4983230072969 + 3 ^ 40 * 6582858 * 2
def baseEnd_6582858 : Nat := 3380170234294910771500993

theorem tailTrace_6582858 : CollatzResearch.WordTrace tailWord_6582858 prefixEnd_6582858 3380170234294910771500993 := by
  unfold tailWord_6582858
  simp only [CollatzResearch.WordTrace]
  refine ⟨60024138996359300871097307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160064370656958135656259485 60024138996359300871097307)
  ·
    refine ⟨90036208494538951306645961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60024138996359300871097307 90036208494538951306645961)
    ·
      refine ⟨67527156370904213479984471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90036208494538951306645961 67527156370904213479984471)
      ·
        refine ⟨101290734556356320219976707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67527156370904213479984471 101290734556356320219976707)
        ·
          refine ⟨151936101834534480329965061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101290734556356320219976707 151936101834534480329965061)
          ·
            refine ⟨28488019093975215061868449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151936101834534480329965061 28488019093975215061868449)
            ·
              refine ⟨21366014320481411296401337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28488019093975215061868449 21366014320481411296401337)
              ·
                refine ⟨16024510740361058472301003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21366014320481411296401337 16024510740361058472301003)
                ·
                  refine ⟨24036766110541587708451505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16024510740361058472301003 24036766110541587708451505)
                  ·
                    refine ⟨18027574582906190781338629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24036766110541587708451505 18027574582906190781338629)
                    ·
                      refine ⟨3380170234294910771500993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18027574582906190781338629 3380170234294910771500993)
                      ·
                        rfl

theorem cell23_6582858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_6582858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582858 prefixEnd_6582858 := by exact prefixLift 6582858
  have htrace : WordTrace (prefixWord ++ tailWord_6582858) baseStart_6582858 baseEnd_6582858 := by
    simpa [prefixWord, tailWord_6582858, baseEnd_6582858] using wordTrace_append hprefix tailTrace_6582858
  have hstable : (prefixWord ++ tailWord_6582858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582858).length < 2 ^ (prefixWord ++ tailWord_6582858).sum := by decide
  have hdescent : baseEnd_6582858 < baseStart_6582858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582865 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_6582865 : Nat := 118140960795 + 6582865 * 2 ^ 59
def prefixEnd_6582865 : Nat := 4983230072969 + 3 ^ 40 * 6582865 * 2
def baseEnd_6582865 : Nat := 3380173828659492244113461

theorem tailTrace_6582865 : CollatzResearch.WordTrace tailWord_6582865 prefixEnd_6582865 3380173828659492244113461 := by
  unfold tailWord_6582865
  simp only [CollatzResearch.WordTrace]
  refine ⟨240096811296411843679894049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160064540864274562453262699 240096811296411843679894049)
  ·
    refine ⟨180072608472308882759920537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240096811296411843679894049 180072608472308882759920537)
    ·
      refine ⟨135054456354231662069940403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180072608472308882759920537 135054456354231662069940403)
      ·
        refine ⟨202581684531347493104910605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135054456354231662069940403 202581684531347493104910605)
        ·
          refine ⟨75968131699255309914341477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202581684531347493104910605 75968131699255309914341477)
          ·
            refine ⟨14244024693610370608939027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75968131699255309914341477 14244024693610370608939027)
            ·
              refine ⟨21366037040415555913408541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14244024693610370608939027 21366037040415555913408541)
              ·
                refine ⟨8012263890155833467528203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21366037040415555913408541 8012263890155833467528203)
                ·
                  refine ⟨12018395835233750201292305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012263890155833467528203 12018395835233750201292305)
                  ·
                    refine ⟨9013796876425312650969229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12018395835233750201292305 9013796876425312650969229)
                    ·
                      refine ⟨3380173828659492244113461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013796876425312650969229 3380173828659492244113461)
                      ·
                        rfl

theorem cell23_6582865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_6582865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582865 prefixEnd_6582865 := by exact prefixLift 6582865
  have htrace : WordTrace (prefixWord ++ tailWord_6582865) baseStart_6582865 baseEnd_6582865 := by
    simpa [prefixWord, tailWord_6582865, baseEnd_6582865] using wordTrace_append hprefix tailTrace_6582865
  have hstable : (prefixWord ++ tailWord_6582865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582865).length < 2 ^ (prefixWord ++ tailWord_6582865).sum := by decide
  have hdescent : baseEnd_6582865 < baseStart_6582865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582882 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6582882 : Nat := 118140960795 + 6582882 * 2 ^ 59
def prefixEnd_6582882 : Nat := 4983230072969 + 3 ^ 40 * 6582882 * 2
def baseEnd_6582882 : Nat := 3380182557830618677600883

theorem tailTrace_6582882 : CollatzResearch.WordTrace tailWord_6582882 prefixEnd_6582882 3380182557830618677600883 := by
  unfold tailWord_6582882
  simp only [CollatzResearch.WordTrace]
  refine ⟨60024357834337563895815725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160064954224900170388841933 60024357834337563895815725)
  ·
    refine ⟨22509134187876586460930897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60024357834337563895815725 22509134187876586460930897)
    ·
      refine ⟨16881850640907439845698173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22509134187876586460930897 16881850640907439845698173)
      ·
        refine ⟨6330693990340289942136815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16881850640907439845698173 6330693990340289942136815)
        ·
          refine ⟨9496040985510434913205223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330693990340289942136815 9496040985510434913205223)
          ·
            refine ⟨14244061478265652369807835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9496040985510434913205223 14244061478265652369807835)
            ·
              refine ⟨21366092217398478554711753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14244061478265652369807835 21366092217398478554711753)
              ·
                refine ⟨16024569163048858916033815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21366092217398478554711753 16024569163048858916033815)
                ·
                  refine ⟨24036853744573288374050723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16024569163048858916033815 24036853744573288374050723)
                  ·
                    refine ⟨36055280616859932561076085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24036853744573288374050723 36055280616859932561076085)
                    ·
                      refine ⟨3380182557830618677600883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36055280616859932561076085 3380182557830618677600883)
                      ·
                        rfl

theorem cell23_6582882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6582882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582882 prefixEnd_6582882 := by exact prefixLift 6582882
  have htrace : WordTrace (prefixWord ++ tailWord_6582882) baseStart_6582882 baseEnd_6582882 := by
    simpa [prefixWord, tailWord_6582882, baseEnd_6582882] using wordTrace_append hprefix tailTrace_6582882
  have hstable : (prefixWord ++ tailWord_6582882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582882).length < 2 ^ (prefixWord ++ tailWord_6582882).sum := by decide
  have hdescent : baseEnd_6582882 < baseStart_6582882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582895 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_6582895 : Nat := 118140960795 + 6582895 * 2 ^ 59
def prefixEnd_6582895 : Nat := 4983230072969 + 3 ^ 40 * 6582895 * 2
def baseEnd_6582895 : Nat := 3380189233079127126738323

theorem tailTrace_6582895 : CollatzResearch.WordTrace tailWord_6582895 prefixEnd_6582895 3380189233079127126738323 := by
  unfold tailWord_6582895
  simp only [CollatzResearch.WordTrace]
  refine ⟨240097905486303158803486139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160065270324202105868990759 240097905486303158803486139)
  ·
    refine ⟨360146858229454738205229209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240097905486303158803486139 360146858229454738205229209)
    ·
      refine ⟨270110143672091053653921907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360146858229454738205229209 270110143672091053653921907)
      ·
        refine ⟨405165215508136580480882861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270110143672091053653921907 405165215508136580480882861)
        ·
          refine ⟨151936955815551217680331073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405165215508136580480882861 151936955815551217680331073)
          ·
            refine ⟨113952716861663413260248305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151936955815551217680331073 113952716861663413260248305)
            ·
              refine ⟨85464537646247559945186229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113952716861663413260248305 85464537646247559945186229)
              ·
                refine ⟨8012300404335708744861209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85464537646247559945186229 8012300404335708744861209)
                ·
                  refine ⟨6009225303251781558645907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8012300404335708744861209 6009225303251781558645907)
                  ·
                    refine ⟨9013837954877672337968861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6009225303251781558645907 9013837954877672337968861)
                    ·
                      refine ⟨3380189233079127126738323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013837954877672337968861 3380189233079127126738323)
                      ·
                        rfl

theorem cell23_6582895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_6582895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582895 prefixEnd_6582895 := by exact prefixLift 6582895
  have htrace : WordTrace (prefixWord ++ tailWord_6582895) baseStart_6582895 baseEnd_6582895 := by
    simpa [prefixWord, tailWord_6582895, baseEnd_6582895] using wordTrace_append hprefix tailTrace_6582895
  have hstable : (prefixWord ++ tailWord_6582895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582895).length < 2 ^ (prefixWord ++ tailWord_6582895).sum := by decide
  have hdescent : baseEnd_6582895 < baseStart_6582895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582902 : List Nat := [5, 1, 1, 2, 3, 2, 2, 7]
def baseStart_6582902 : Nat := 118140960795 + 6582902 * 2 ^ 59
def prefixEnd_6582902 : Nat := 4983230072969 + 3 ^ 40 * 6582902 * 2
def baseEnd_6582902 : Nat := 125192326942359577753733

theorem tailTrace_6582902 : CollatzResearch.WordTrace tailWord_6582902 prefixEnd_6582902 125192326942359577753733 := by
  unfold tailWord_6582902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006135049829862437436935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160065440531518532665993973 15006135049829862437436935)
  ·
    refine ⟨22509202574744793656155403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15006135049829862437436935 22509202574744793656155403)
    ·
      refine ⟨33763803862117190484233105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22509202574744793656155403 33763803862117190484233105)
      ·
        refine ⟨25322852896587892863174829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33763803862117190484233105 25322852896587892863174829)
        ·
          refine ⟨9496069836220459823690561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25322852896587892863174829 9496069836220459823690561)
          ·
            refine ⟨7122052377165344867767921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496069836220459823690561 7122052377165344867767921)
            ·
              refine ⟨5341539282874008650825941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122052377165344867767921 5341539282874008650825941)
              ·
                refine ⟨125192326942359577753733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5341539282874008650825941 125192326942359577753733)
                ·
                  rfl

theorem cell23_6582902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_6582902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582902 prefixEnd_6582902 := by exact prefixLift 6582902
  have htrace : WordTrace (prefixWord ++ tailWord_6582902) baseStart_6582902 baseEnd_6582902 := by
    simpa [prefixWord, tailWord_6582902, baseEnd_6582902] using wordTrace_append hprefix tailTrace_6582902
  have hstable : (prefixWord ++ tailWord_6582902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582902).length < 2 ^ (prefixWord ++ tailWord_6582902).sum := by decide
  have hdescent : baseEnd_6582902 < baseStart_6582902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 6]
def baseStart_6582911 : Nat := 118140960795 + 6582911 * 2 ^ 59
def prefixEnd_6582911 : Nat := 4983230072969 + 3 ^ 40 * 6582911 * 2
def baseEnd_6582911 : Nat := 1126732482923199688046083

theorem tailTrace_6582911 : CollatzResearch.WordTrace tailWord_6582911 prefixEnd_6582911 1126732482923199688046083 := by
  unfold tailWord_6582911
  simp only [CollatzResearch.WordTrace]
  refine ⟨240098489054245193536068587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160065659369496795690712391 240098489054245193536068587)
  ·
    refine ⟨360147733581367790304102881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240098489054245193536068587 360147733581367790304102881)
    ·
      refine ⟨270110800186025842728077161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360147733581367790304102881 270110800186025842728077161)
      ·
        refine ⟨202583100139519382046057871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270110800186025842728077161 202583100139519382046057871)
        ·
          refine ⟨303874650209279073069086807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202583100139519382046057871 303874650209279073069086807)
          ·
            refine ⟨455811975313918609603630211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303874650209279073069086807 455811975313918609603630211)
            ·
              refine ⟨683717962970877914405445317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455811975313918609603630211 683717962970877914405445317)
              ·
                refine ⟨128197118057039608951020997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683717962970877914405445317 128197118057039608951020997)
                ·
                  refine ⟨24036959635694926678316437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128197118057039608951020997 24036959635694926678316437)
                  ·
                    refine ⟨1126732482923199688046083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24036959635694926678316437 1126732482923199688046083)
                    ·
                      rfl

theorem cell23_6582911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_6582911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582911 prefixEnd_6582911 := by exact prefixLift 6582911
  have htrace : WordTrace (prefixWord ++ tailWord_6582911) baseStart_6582911 baseEnd_6582911 := by
    simpa [prefixWord, tailWord_6582911, baseEnd_6582911] using wordTrace_append hprefix tailTrace_6582911
  have hstable : (prefixWord ++ tailWord_6582911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582911).length < 2 ^ (prefixWord ++ tailWord_6582911).sum := by decide
  have hdescent : baseEnd_6582911 < baseStart_6582911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582948 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_6582948 : Nat := 118140960795 + 6582948 * 2 ^ 59
def prefixEnd_6582948 : Nat := 4983230072969 + 3 ^ 40 * 6582948 * 2
def baseEnd_6582948 : Nat := 3380216447553815419375579

theorem tailTrace_6582948 : CollatzResearch.WordTrace tailWord_6582948 prefixEnd_6582948 3380216447553815419375579 := by
  unfold tailWord_6582948
  simp only [CollatzResearch.WordTrace]
  refine ⟨120049919277555574427582749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160066559036740765903443665 120049919277555574427582749)
  ·
    refine ⟨45018719729083340410343531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120049919277555574427582749 45018719729083340410343531)
    ·
      refine ⟨67528079593625010615515297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45018719729083340410343531 67528079593625010615515297)
      ·
        refine ⟨50646059695218757961636473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67528079593625010615515297 50646059695218757961636473)
        ·
          refine ⟨37984544771414068471227355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50646059695218757961636473 37984544771414068471227355)
          ·
            refine ⟨56976817157121102706841033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37984544771414068471227355 56976817157121102706841033)
            ·
              refine ⟨42732612867840827030130775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56976817157121102706841033 42732612867840827030130775)
              ·
                refine ⟨64098919301761240545196163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42732612867840827030130775 64098919301761240545196163)
                ·
                  refine ⟨96148378952641860817794245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64098919301761240545196163 96148378952641860817794245)
                  ·
                    refine ⟨18027821053620348903336421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96148378952641860817794245 18027821053620348903336421)
                    ·
                      refine ⟨3380216447553815419375579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18027821053620348903336421 3380216447553815419375579)
                      ·
                        rfl

theorem cell23_6582948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_6582948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582948 prefixEnd_6582948 := by exact prefixLift 6582948
  have htrace : WordTrace (prefixWord ++ tailWord_6582948) baseStart_6582948 baseEnd_6582948 := by
    simpa [prefixWord, tailWord_6582948, baseEnd_6582948] using wordTrace_append hprefix tailTrace_6582948
  have hstable : (prefixWord ++ tailWord_6582948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582948).length < 2 ^ (prefixWord ++ tailWord_6582948).sum := by decide
  have hdescent : baseEnd_6582948 < baseStart_6582948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582968 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_6582968 : Nat := 118140960795 + 6582968 * 2 ^ 59
def prefixEnd_6582968 : Nat := 4983230072969 + 3 ^ 40 * 6582968 * 2
def baseEnd_6582968 : Nat := 3380226717166905341125487

theorem tailTrace_6582968 : CollatzResearch.WordTrace tailWord_6582968 prefixEnd_6582968 3380226717166905341125487 := by
  unfold tailWord_6582968
  simp only [CollatzResearch.WordTrace]
  refine ⟨120050284007519346135446779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160067045343359128180595705 120050284007519346135446779)
  ·
    refine ⟨180075426011279019203170169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120050284007519346135446779 180075426011279019203170169)
    ·
      refine ⟨135056569508459264402377627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180075426011279019203170169 135056569508459264402377627)
      ·
        refine ⟨202584854262688896603566441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135056569508459264402377627 202584854262688896603566441)
        ·
          refine ⟨151938640697016672452674831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202584854262688896603566441 151938640697016672452674831)
          ·
            refine ⟨227907961045525008679012247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151938640697016672452674831 227907961045525008679012247)
            ·
              refine ⟨341861941568287513018518371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227907961045525008679012247 341861941568287513018518371)
              ·
                refine ⟨512792912352431269527777557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341861941568287513018518371 512792912352431269527777557)
                ·
                  refine ⟨24037167766520215759114573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 512792912352431269527777557 24037167766520215759114573)
                  ·
                    refine ⟨9013937912445080909667965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24037167766520215759114573 9013937912445080909667965)
                    ·
                      refine ⟨3380226717166905341125487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9013937912445080909667965 3380226717166905341125487)
                      ·
                        rfl

theorem cell23_6582968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_6582968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6582968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6582968 prefixEnd_6582968 := by exact prefixLift 6582968
  have htrace : WordTrace (prefixWord ++ tailWord_6582968) baseStart_6582968 baseEnd_6582968 := by
    simpa [prefixWord, tailWord_6582968, baseEnd_6582968] using wordTrace_append hprefix tailTrace_6582968
  have hstable : (prefixWord ++ tailWord_6582968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582968).length < 2 ^ (prefixWord ++ tailWord_6582968).sum := by decide
  have hdescent : baseEnd_6582968 < baseStart_6582968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583008 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_6583008 : Nat := 118140960795 + 6583008 * 2 ^ 59
def prefixEnd_6583008 : Nat := 4983230072969 + 3 ^ 40 * 6583008 * 2
def baseEnd_6583008 : Nat := 3380247256393085184625303

theorem tailTrace_6583008 : CollatzResearch.WordTrace tailWord_6583008 prefixEnd_6583008 3380247256393085184625303 := by
  unfold tailWord_6583008
  simp only [CollatzResearch.WordTrace]
  refine ⟨120051013467446889551174839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160068017956595852734899785 120051013467446889551174839)
  ·
    refine ⟨180076520201170334326762259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120051013467446889551174839 180076520201170334326762259)
    ·
      refine ⟨270114780301755501490143389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180076520201170334326762259 270114780301755501490143389)
      ·
        refine ⟨101293042613158313058803771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270114780301755501490143389 101293042613158313058803771)
        ·
          refine ⟨151939563919737469588205657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101293042613158313058803771 151939563919737469588205657)
          ·
            refine ⟨113954672939803102191154243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151939563919737469588205657 113954672939803102191154243)
            ·
              refine ⟨170932009409704653286731365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113954672939803102191154243 170932009409704653286731365)
              ·
                refine ⟨32049751764319622491262131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170932009409704653286731365 32049751764319622491262131)
                ·
                  refine ⟨48074627646479433736893197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32049751764319622491262131 48074627646479433736893197)
                  ·
                    refine ⟨18027985367429787651334949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48074627646479433736893197 18027985367429787651334949)
                    ·
                      refine ⟨3380247256393085184625303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18027985367429787651334949 3380247256393085184625303)
                      ·
                        rfl

theorem cell23_6583008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_6583008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583008 prefixEnd_6583008 := by exact prefixLift 6583008
  have htrace : WordTrace (prefixWord ++ tailWord_6583008) baseStart_6583008 baseEnd_6583008 := by
    simpa [prefixWord, tailWord_6583008, baseEnd_6583008] using wordTrace_append hprefix tailTrace_6583008
  have hstable : (prefixWord ++ tailWord_6583008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583008).length < 2 ^ (prefixWord ++ tailWord_6583008).sum := by decide
  have hdescent : baseEnd_6583008 < baseStart_6583008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583022 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_6583022 : Nat := 118140960795 + 6583022 * 2 ^ 59
def prefixEnd_6583022 : Nat := 4983230072969 + 3 ^ 40 * 6583022 * 2
def baseEnd_6583022 : Nat := 1126751481707416043283413

theorem tailTrace_6583022 : CollatzResearch.WordTrace tailWord_6583022 prefixEnd_6583022 1126751481707416043283413 := by
  unfold tailWord_6583022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30012817194605382436669915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160068358371228706328906213 30012817194605382436669915)
  ·
    refine ⟨45019225791908073655004873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30012817194605382436669915 45019225791908073655004873)
    ·
      refine ⟨33764419343931055241253655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45019225791908073655004873 33764419343931055241253655)
      ·
        refine ⟨50646629015896582861880483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33764419343931055241253655 50646629015896582861880483)
        ·
          refine ⟨75969943523844874292820725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50646629015896582861880483 75969943523844874292820725)
          ·
            refine ⟨7122182205360456964951943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75969943523844874292820725 7122182205360456964951943)
            ·
              refine ⟨10683273308040685447427915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122182205360456964951943 10683273308040685447427915)
              ·
                refine ⟨16024909962061028171141873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683273308040685447427915 16024909962061028171141873)
                ·
                  refine ⟨12018682471545771128356405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16024909962061028171141873 12018682471545771128356405)
                  ·
                    refine ⟨1126751481707416043283413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12018682471545771128356405 1126751481707416043283413)
                    ·
                      rfl

theorem cell23_6583022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_6583022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583022 prefixEnd_6583022 := by exact prefixLift 6583022
  have htrace : WordTrace (prefixWord ++ tailWord_6583022) baseStart_6583022 baseEnd_6583022 := by
    simpa [prefixWord, tailWord_6583022, baseEnd_6583022] using wordTrace_append hprefix tailTrace_6583022
  have hstable : (prefixWord ++ tailWord_6583022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583022).length < 2 ^ (prefixWord ++ tailWord_6583022).sum := by decide
  have hdescent : baseEnd_6583022 < baseStart_6583022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583025 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_6583025 : Nat := 118140960795 + 6583025 * 2 ^ 59
def prefixEnd_6583025 : Nat := 4983230072969 + 3 ^ 40 * 6583025 * 2
def baseEnd_6583025 : Nat := 3380255985564211618112725

theorem tailTrace_6583025 : CollatzResearch.WordTrace tailWord_6583025 prefixEnd_6583025 3380255985564211618112725 := by
  unfold tailWord_6583025
  simp only [CollatzResearch.WordTrace]
  refine ⟨240102646975832191005718529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160068431317221460670479019 240102646975832191005718529)
  ·
    refine ⟨180076985231874143254288897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240102646975832191005718529 180076985231874143254288897)
    ·
      refine ⟨135057738923905607440716673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180076985231874143254288897 135057738923905607440716673)
      ·
        refine ⟨101293304192929205580537505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135057738923905607440716673 101293304192929205580537505)
        ·
          refine ⟨75969978144696904185403129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101293304192929205580537505 75969978144696904185403129)
          ·
            refine ⟨56977483608522678139052347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75969978144696904185403129 56977483608522678139052347)
            ·
              refine ⟨85466225412784017208578521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56977483608522678139052347 85466225412784017208578521)
              ·
                refine ⟨64099669059588012906433891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85466225412784017208578521 64099669059588012906433891)
                ·
                  refine ⟨96149503589382019359650837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64099669059588012906433891 96149503589382019359650837)
                  ·
                    refine ⟨4507007980752282157483633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96149503589382019359650837 4507007980752282157483633)
                    ·
                      refine ⟨3380255985564211618112725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507007980752282157483633 3380255985564211618112725)
                      ·
                        rfl

theorem cell23_6583025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_6583025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583025 prefixEnd_6583025 := by exact prefixLift 6583025
  have htrace : WordTrace (prefixWord ++ tailWord_6583025) baseStart_6583025 baseEnd_6583025 := by
    simpa [prefixWord, tailWord_6583025, baseEnd_6583025] using wordTrace_append hprefix tailTrace_6583025
  have hstable : (prefixWord ++ tailWord_6583025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583025).length < 2 ^ (prefixWord ++ tailWord_6583025).sum := by decide
  have hdescent : baseEnd_6583025 < baseStart_6583025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583045 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_6583045 : Nat := 118140960795 + 6583045 * 2 ^ 59
def prefixEnd_6583045 : Nat := 4983230072969 + 3 ^ 40 * 6583045 * 2
def baseEnd_6583045 : Nat := 3380266255177301539862633

theorem tailTrace_6583045 : CollatzResearch.WordTrace tailWord_6583045 prefixEnd_6583045 3380266255177301539862633 := by
  unfold tailWord_6583045
  simp only [CollatzResearch.WordTrace]
  refine ⟨240103376435759734421446589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160068917623839822947631059 240103376435759734421446589)
  ·
    refine ⟨90038766163409900408042471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240103376435759734421446589 90038766163409900408042471)
    ·
      refine ⟨135058149245114850612063707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90038766163409900408042471 135058149245114850612063707)
      ·
        refine ⟨202587223867672275918095561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135058149245114850612063707 202587223867672275918095561)
        ·
          refine ⟨151940417900754206938571671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202587223867672275918095561 151940417900754206938571671)
          ·
            refine ⟨227910626851131310407857507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151940417900754206938571671 227910626851131310407857507)
            ·
              refine ⟨341865940276696965611786261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227910626851131310407857507 341865940276696965611786261)
              ·
                refine ⟨16024965950470170263052481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341865940276696965611786261 16024965950470170263052481)
                ·
                  refine ⟨12018724462852627697289361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16024965950470170263052481 12018724462852627697289361)
                  ·
                    refine ⟨9014043347139470772967021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12018724462852627697289361 9014043347139470772967021)
                    ·
                      refine ⟨3380266255177301539862633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014043347139470772967021 3380266255177301539862633)
                      ·
                        rfl

theorem cell23_6583045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_6583045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583045 prefixEnd_6583045 := by exact prefixLift 6583045
  have htrace : WordTrace (prefixWord ++ tailWord_6583045) baseStart_6583045 baseEnd_6583045 := by
    simpa [prefixWord, tailWord_6583045, baseEnd_6583045] using wordTrace_append hprefix tailTrace_6583045
  have hstable : (prefixWord ++ tailWord_6583045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583045).length < 2 ^ (prefixWord ++ tailWord_6583045).sum := by decide
  have hdescent : baseEnd_6583045 < baseStart_6583045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583086 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6583086 : Nat := 118140960795 + 6583086 * 2 ^ 59
def prefixEnd_6583086 : Nat := 4983230072969 + 3 ^ 40 * 6583086 * 2
def baseEnd_6583086 : Nat := 1126762435961378626483315

theorem tailTrace_6583086 : CollatzResearch.WordTrace tailWord_6583086 prefixEnd_6583086 1126762435961378626483315 := by
  unfold tailWord_6583086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013108978576399802961139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160069914552407465615792741 30013108978576399802961139)
  ·
    refine ⟨45019663467864599704441709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30013108978576399802961139 45019663467864599704441709)
    ·
      refine ⟨16882373800449224889165641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45019663467864599704441709 16882373800449224889165641)
      ·
        refine ⟨12661780350336918666874231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16882373800449224889165641 12661780350336918666874231)
        ·
          refine ⟨18992670525505378000311347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661780350336918666874231 18992670525505378000311347)
          ·
            refine ⟨28489005788258067000467021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18992670525505378000311347 28489005788258067000467021)
            ·
              refine ⟨10683377170596775125175133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28489005788258067000467021 10683377170596775125175133)
              ·
                refine ⟨4006266438973790671940675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10683377170596775125175133 4006266438973790671940675)
                ·
                  refine ⟨6009399658460686007911013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006266438973790671940675 6009399658460686007911013)
                  ·
                    refine ⟨1126762435961378626483315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009399658460686007911013 1126762435961378626483315)
                    ·
                      rfl

theorem cell23_6583086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6583086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583086 prefixEnd_6583086 := by exact prefixLift 6583086
  have htrace : WordTrace (prefixWord ++ tailWord_6583086) baseStart_6583086 baseEnd_6583086 := by
    simpa [prefixWord, tailWord_6583086, baseEnd_6583086] using wordTrace_append hprefix tailTrace_6583086
  have hstable : (prefixWord ++ tailWord_6583086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583086).length < 2 ^ (prefixWord ++ tailWord_6583086).sum := by decide
  have hdescent : baseEnd_6583086 < baseStart_6583086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583095 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 1, 5]
def baseStart_6583095 : Nat := 118140960795 + 6583095 * 2 ^ 59
def prefixEnd_6583095 : Nat := 4983230072969 + 3 ^ 40 * 6583095 * 2
def baseEnd_6583095 : Nat := 1126763976403342114745801

theorem tailTrace_6583095 : CollatzResearch.WordTrace tailWord_6583095 prefixEnd_6583095 1126763976403342114745801 := by
  unfold tailWord_6583095
  simp only [CollatzResearch.WordTrace]
  refine ⟨240105200085578592960766739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160070133390385728640511159 240105200085578592960766739)
  ·
    refine ⟨360157800128367889441150109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240105200085578592960766739 360157800128367889441150109)
    ·
      refine ⟨135059175048137958540431291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360157800128367889441150109 135059175048137958540431291)
      ·
        refine ⟨202588762572206937810646937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135059175048137958540431291 202588762572206937810646937)
        ·
          refine ⟨151941571929155203357985203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202588762572206937810646937 151941571929155203357985203)
          ·
            refine ⟨227912357893732805036977805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151941571929155203357985203 227912357893732805036977805)
            ·
              refine ⟨85467134210149801888866677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227912357893732805036977805 85467134210149801888866677)
              ·
                refine ⟨8012543832201543927081251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85467134210149801888866677 8012543832201543927081251)
                ·
                  refine ⟨12018815748302315890621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012543832201543927081251 12018815748302315890621877)
                  ·
                    refine ⟨1126763976403342114745801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12018815748302315890621877 1126763976403342114745801)
                    ·
                      rfl

theorem cell23_6583095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_6583095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583095 prefixEnd_6583095 := by exact prefixLift 6583095
  have htrace : WordTrace (prefixWord ++ tailWord_6583095) baseStart_6583095 baseEnd_6583095 := by
    simpa [prefixWord, tailWord_6583095, baseEnd_6583095] using wordTrace_append hprefix tailTrace_6583095
  have hstable : (prefixWord ++ tailWord_6583095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583095).length < 2 ^ (prefixWord ++ tailWord_6583095).sum := by decide
  have hdescent : baseEnd_6583095 < baseStart_6583095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583125 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_6583125 : Nat := 118140960795 + 6583125 * 2 ^ 59
def prefixEnd_6583125 : Nat := 4983230072969 + 3 ^ 40 * 6583125 * 2
def baseEnd_6583125 : Nat := 1126769111209887075620755

theorem tailTrace_6583125 : CollatzResearch.WordTrace tailWord_6583125 prefixEnd_6583125 1126769111209887075620755 := by
  unfold tailWord_6583125
  simp only [CollatzResearch.WordTrace]
  refine ⟨240106294275469908084358829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160070862850313272056239219 240106294275469908084358829)
  ·
    refine ⟨90039860353301215531634561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240106294275469908084358829 90039860353301215531634561)
    ·
      refine ⟨67529895264975911648725921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90039860353301215531634561 67529895264975911648725921)
      ·
        refine ⟨50647421448731933736544441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67529895264975911648725921 50647421448731933736544441)
        ·
          refine ⟨37985566086548950302408331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50647421448731933736544441 37985566086548950302408331)
          ·
            refine ⟨56978349129823425453612497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37985566086548950302408331 56978349129823425453612497)
            ·
              refine ⟨42733761847367569090209373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56978349129823425453612497 42733761847367569090209373)
              ·
                refine ⟨16025160692762838408828515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42733761847367569090209373 16025160692762838408828515)
                ·
                  refine ⟨24037741039144257613242773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16025160692762838408828515 24037741039144257613242773)
                  ·
                    refine ⟨1126769111209887075620755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24037741039144257613242773 1126769111209887075620755)
                    ·
                      rfl

theorem cell23_6583125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_6583125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583125 prefixEnd_6583125 := by exact prefixLift 6583125
  have htrace : WordTrace (prefixWord ++ tailWord_6583125) baseStart_6583125 baseEnd_6583125 := by
    simpa [prefixWord, tailWord_6583125, baseEnd_6583125] using wordTrace_append hprefix tailTrace_6583125
  have hstable : (prefixWord ++ tailWord_6583125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583125).length < 2 ^ (prefixWord ++ tailWord_6583125).sum := by decide
  have hdescent : baseEnd_6583125 < baseStart_6583125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583152 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_6583152 : Nat := 118140960795 + 6583152 * 2 ^ 59
def prefixEnd_6583152 : Nat := 4983230072969 + 3 ^ 40 * 6583152 * 2
def baseEnd_6583152 : Nat := 3380321197607332621224641

theorem tailTrace_6583152 : CollatzResearch.WordTrace tailWord_6583152 prefixEnd_6583152 3380321197607332621224641 := by
  unfold tailWord_6583152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120053639523186045847795855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160071519364248061130394473 120053639523186045847795855)
  ·
    refine ⟨180080459284779068771693783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120053639523186045847795855 180080459284779068771693783)
    ·
      refine ⟨270120688927168603157540675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180080459284779068771693783 270120688927168603157540675)
      ·
        refine ⟨405181033390752904736311013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270120688927168603157540675 405181033390752904736311013)
        ·
          refine ⟨75971443760766169638058315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405181033390752904736311013 75971443760766169638058315)
          ·
            refine ⟨113957165641149254457087473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75971443760766169638058315 113957165641149254457087473)
            ·
              refine ⟨85467874230861940842815605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113957165641149254457087473 85467874230861940842815605)
              ·
                refine ⟨8012613209143306954013963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85467874230861940842815605 8012613209143306954013963)
                ·
                  refine ⟨12018919813714960431020945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012613209143306954013963 12018919813714960431020945)
                  ·
                    refine ⟨9014189860286220323265709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12018919813714960431020945 9014189860286220323265709)
                    ·
                      refine ⟨3380321197607332621224641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014189860286220323265709 3380321197607332621224641)
                      ·
                        rfl

theorem cell23_6583152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_6583152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583152 prefixEnd_6583152 := by exact prefixLift 6583152
  have htrace : WordTrace (prefixWord ++ tailWord_6583152) baseStart_6583152 baseEnd_6583152 := by
    simpa [prefixWord, tailWord_6583152, baseEnd_6583152] using wordTrace_append hprefix tailTrace_6583152
  have hstable : (prefixWord ++ tailWord_6583152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583152).length < 2 ^ (prefixWord ++ tailWord_6583152).sum := by decide
  have hdescent : baseEnd_6583152 < baseStart_6583152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583209 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 1, 3, 2]
def baseStart_6583209 : Nat := 118140960795 + 6583209 * 2 ^ 59
def prefixEnd_6583209 : Nat := 4983230072969 + 3 ^ 40 * 6583209 * 2
def baseEnd_6583209 : Nat := 3380350466004638898211879

theorem tailTrace_6583209 : CollatzResearch.WordTrace tailWord_6583209 prefixEnd_6583209 3380350466004638898211879 := by
  unfold tailWord_6583209
  simp only [CollatzResearch.WordTrace]
  refine ⟨240109358007165590430416681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160072905338110393620277787 240109358007165590430416681)
  ·
    refine ⟨180082018505374192822812511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240109358007165590430416681 180082018505374192822812511)
    ·
      refine ⟨270123027758061289234218767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180082018505374192822812511 270123027758061289234218767)
      ·
        refine ⟨405184541637091933851328151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270123027758061289234218767 405184541637091933851328151)
        ·
          refine ⟨607776812455637900776992227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405184541637091933851328151 607776812455637900776992227)
          ·
            refine ⟨911665218683456851165488341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607776812455637900776992227 911665218683456851165488341)
            ·
              refine ⟨21367153562893519949191133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 911665218683456851165488341 21367153562893519949191133)
              ·
                refine ⟨8012682586085069980946675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21367153562893519949191133 8012682586085069980946675)
                ·
                  refine ⟨12019023879127604971420013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8012682586085069980946675 12019023879127604971420013)
                  ·
                    refine ⟨4507133954672851864282505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12019023879127604971420013 4507133954672851864282505)
                    ·
                      refine ⟨3380350466004638898211879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507133954672851864282505 3380350466004638898211879)
                      ·
                        rfl

theorem cell23_6583209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3, 2].length) (baseStart_6583209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583209 prefixEnd_6583209 := by exact prefixLift 6583209
  have htrace : WordTrace (prefixWord ++ tailWord_6583209) baseStart_6583209 baseEnd_6583209 := by
    simpa [prefixWord, tailWord_6583209, baseEnd_6583209] using wordTrace_append hprefix tailTrace_6583209
  have hstable : (prefixWord ++ tailWord_6583209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583209).length < 2 ^ (prefixWord ++ tailWord_6583209).sum := by decide
  have hdescent : baseEnd_6583209 < baseStart_6583209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583239 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_6583239 : Nat := 118140960795 + 6583239 * 2 ^ 59
def prefixEnd_6583239 : Nat := 4983230072969 + 3 ^ 40 * 6583239 * 2
def baseEnd_6583239 : Nat := 3380365870424273780836741

theorem tailTrace_6583239 : CollatzResearch.WordTrace tailWord_6583239 prefixEnd_6583239 3380365870424273780836741 := by
  unfold tailWord_6583239
  simp only [CollatzResearch.WordTrace]
  refine ⟨240110452197056905554008771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160073634798037937036005847 240110452197056905554008771)
  ·
    refine ⟨360165678295585358331013157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240110452197056905554008771 360165678295585358331013157)
    ·
      refine ⟨67531064680422254687064967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360165678295585358331013157 67531064680422254687064967)
      ·
        refine ⟨101296597020633382030597451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67531064680422254687064967 101296597020633382030597451)
        ·
          refine ⟨151944895530950073045896177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101296597020633382030597451 151944895530950073045896177)
          ·
            refine ⟨113958671648212554784422133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151944895530950073045896177 113958671648212554784422133)
            ·
              refine ⟨10683625467019927011039575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113958671648212554784422133 10683625467019927011039575)
              ·
                refine ⟨16025438200529890516559363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683625467019927011039575 16025438200529890516559363)
                ·
                  refine ⟨24038157300794835774839045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16025438200529890516559363 24038157300794835774839045)
                  ·
                    refine ⟨4507154493899031707782321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24038157300794835774839045 4507154493899031707782321)
                    ·
                      refine ⟨3380365870424273780836741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507154493899031707782321 3380365870424273780836741)
                      ·
                        rfl

theorem cell23_6583239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_6583239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583239 prefixEnd_6583239 := by exact prefixLift 6583239
  have htrace : WordTrace (prefixWord ++ tailWord_6583239) baseStart_6583239 baseEnd_6583239 := by
    simpa [prefixWord, tailWord_6583239, baseEnd_6583239] using wordTrace_append hprefix tailTrace_6583239
  have hstable : (prefixWord ++ tailWord_6583239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583239).length < 2 ^ (prefixWord ++ tailWord_6583239).sum := by decide
  have hdescent : baseEnd_6583239 < baseStart_6583239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583272 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6583272 : Nat := 118140960795 + 6583272 * 2 ^ 59
def prefixEnd_6583272 : Nat := 4983230072969 + 3 ^ 40 * 6583272 * 2
def baseEnd_6583272 : Nat := 3380382815285872151724089

theorem tailTrace_6583272 : CollatzResearch.WordTrace tailWord_6583272 prefixEnd_6583272 3380382815285872151724089 := by
  unfold tailWord_6583272
  simp only [CollatzResearch.WordTrace]
  refine ⟨120055827902968676094980035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160074437203958234793306713 120055827902968676094980035)
  ·
    refine ⟨180083741854453014142470053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120055827902968676094980035 180083741854453014142470053)
    ·
      refine ⟨33765701597709940151713135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180083741854453014142470053 33765701597709940151713135)
      ·
        refine ⟨50648552396564910227569703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33765701597709940151713135 50648552396564910227569703)
        ·
          refine ⟨75972828594847365341354555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50648552396564910227569703 75972828594847365341354555)
          ·
            refine ⟨113959242892271048012031833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75972828594847365341354555 113959242892271048012031833)
            ·
              refine ⟨85469432169203286009023875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113959242892271048012031833 85469432169203286009023875)
              ·
                refine ⟨128204148253804929013535813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85469432169203286009023875 128204148253804929013535813)
                ·
                  refine ⟨24038277797588424190037965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128204148253804929013535813 24038277797588424190037965)
                  ·
                    refine ⟨9014354174095659071264237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24038277797588424190037965 9014354174095659071264237)
                    ·
                      refine ⟨3380382815285872151724089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014354174095659071264237 3380382815285872151724089)
                      ·
                        rfl

theorem cell23_6583272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6583272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583272 prefixEnd_6583272 := by exact prefixLift 6583272
  have htrace : WordTrace (prefixWord ++ tailWord_6583272) baseStart_6583272 baseEnd_6583272 := by
    simpa [prefixWord, tailWord_6583272, baseEnd_6583272] using wordTrace_append hprefix tailTrace_6583272
  have hstable : (prefixWord ++ tailWord_6583272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583272).length < 2 ^ (prefixWord ++ tailWord_6583272).sum := by decide
  have hdescent : baseEnd_6583272 < baseStart_6583272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583305 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_6583305 : Nat := 118140960795 + 6583305 * 2 ^ 59
def prefixEnd_6583305 : Nat := 4983230072969 + 3 ^ 40 * 6583305 * 2
def baseEnd_6583305 : Nat := 1126799920049156840870479

theorem tailTrace_6583305 : CollatzResearch.WordTrace tailWord_6583305 prefixEnd_6583305 1126799920049156840870479 := by
  unfold tailWord_6583305
  simp only [CollatzResearch.WordTrace]
  refine ⟨240112859414817798825911369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160075239609878532550607579 240112859414817798825911369)
  ·
    refine ⟨180084644561113349119433527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240112859414817798825911369 180084644561113349119433527)
    ·
      refine ⟨270126966841670023679150291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180084644561113349119433527 270126966841670023679150291)
      ·
        refine ⟨405190450262505035518725437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270126966841670023679150291 405190450262505035518725437)
        ·
          refine ⟨151946418848439388319522039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405190450262505035518725437 151946418848439388319522039)
          ·
            refine ⟨227919628272659082479283059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151946418848439388319522039 227919628272659082479283059)
            ·
              refine ⟨341879442408988623718924589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227919628272659082479283059 341879442408988623718924589)
              ·
                refine ⟨128204790903370733894596721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341879442408988623718924589 128204790903370733894596721)
                ·
                  refine ⟨96153593177528050420947541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128204790903370733894596721 96153593177528050420947541)
                  ·
                    refine ⟨1126799920049156840870479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96153593177528050420947541 1126799920049156840870479)
                    ·
                      rfl

theorem cell23_6583305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_6583305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583305 prefixEnd_6583305 := by exact prefixLift 6583305
  have htrace : WordTrace (prefixWord ++ tailWord_6583305) baseStart_6583305 baseEnd_6583305 := by
    simpa [prefixWord, tailWord_6583305, baseEnd_6583305] using wordTrace_append hprefix tailTrace_6583305
  have hstable : (prefixWord ++ tailWord_6583305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583305).length < 2 ^ (prefixWord ++ tailWord_6583305).sum := by decide
  have hdescent : baseEnd_6583305 < baseStart_6583305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583329 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6583329 : Nat := 118140960795 + 6583329 * 2 ^ 59
def prefixEnd_6583329 : Nat := 4983230072969 + 3 ^ 40 * 6583329 * 2
def baseEnd_6583329 : Nat := 3380412083683178428711327

theorem tailTrace_6583329 : CollatzResearch.WordTrace tailWord_6583329 prefixEnd_6583329 3380412083683178428711327 := by
  unfold tailWord_6583329
  simp only [CollatzResearch.WordTrace]
  refine ⟨240113734766730850924785041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160075823177820567283190027 240113734766730850924785041)
  ·
    refine ⟨180085301075048138193588781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240113734766730850924785041 180085301075048138193588781)
    ·
      refine ⟨67531987903143051822595793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180085301075048138193588781 67531987903143051822595793)
      ·
        refine ⟨50648990927357288866946845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67531987903143051822595793 50648990927357288866946845)
        ·
          refine ⟨18993371597758983325105067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50648990927357288866946845 18993371597758983325105067)
          ·
            refine ⟨28490057396638474987657601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18993371597758983325105067 28490057396638474987657601)
            ·
              refine ⟨21367543047478856240743201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28490057396638474987657601 21367543047478856240743201)
              ·
                refine ⟨16025657285609142180557401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21367543047478856240743201 16025657285609142180557401)
                ·
                  refine ⟨12019242964206856635418051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16025657285609142180557401 12019242964206856635418051)
                  ·
                    refine ⟨18028864446310284953127077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12019242964206856635418051 18028864446310284953127077)
                    ·
                      refine ⟨3380412083683178428711327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18028864446310284953127077 3380412083683178428711327)
                      ·
                        rfl

theorem cell23_6583329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6583329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583329 prefixEnd_6583329 := by exact prefixLift 6583329
  have htrace : WordTrace (prefixWord ++ tailWord_6583329) baseStart_6583329 baseEnd_6583329 := by
    simpa [prefixWord, tailWord_6583329, baseEnd_6583329] using wordTrace_append hprefix tailTrace_6583329
  have hstable : (prefixWord ++ tailWord_6583329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583329).length < 2 ^ (prefixWord ++ tailWord_6583329).sum := by decide
  have hdescent : baseEnd_6583329 < baseStart_6583329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583373 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_6583373 : Nat := 118140960795 + 6583373 * 2 ^ 59
def prefixEnd_6583373 : Nat := 4983230072969 + 3 ^ 40 * 6583373 * 2
def baseEnd_6583373 : Nat := 1126811558943992085520375

theorem tailTrace_6583373 : CollatzResearch.WordTrace tailWord_6583373 prefixEnd_6583373 1126811558943992085520375 := by
  unfold tailWord_6583373
  simp only [CollatzResearch.WordTrace]
  refine ⟨240115339578571446439386773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160076893052380964292924515 240115339578571446439386773)
  ·
    refine ⟨11255406542745536551846255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240115339578571446439386773 11255406542745536551846255)
    ·
      refine ⟨16883109814118304827769383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255406542745536551846255 16883109814118304827769383)
      ·
        refine ⟨25324664721177457241654075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16883109814118304827769383 25324664721177457241654075)
        ·
          refine ⟨37986997081766185862481113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25324664721177457241654075 37986997081766185862481113)
          ·
            refine ⟨28490247811324639396860835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37986997081766185862481113 28490247811324639396860835)
            ·
              refine ⟨42735371716986959095291253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28490247811324639396860835 42735371716986959095291253)
              ·
                refine ⟨4006441098467527415183555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42735371716986959095291253 4006441098467527415183555)
                ·
                  refine ⟨6009661647701291122775333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006441098467527415183555 6009661647701291122775333)
                  ·
                    refine ⟨1126811558943992085520375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009661647701291122775333 1126811558943992085520375)
                    ·
                      rfl

theorem cell23_6583373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_6583373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583373 prefixEnd_6583373 := by exact prefixLift 6583373
  have htrace : WordTrace (prefixWord ++ tailWord_6583373) baseStart_6583373 baseEnd_6583373 := by
    simpa [prefixWord, tailWord_6583373, baseEnd_6583373] using wordTrace_append hprefix tailTrace_6583373
  have hstable : (prefixWord ++ tailWord_6583373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583373).length < 2 ^ (prefixWord ++ tailWord_6583373).sum := by decide
  have hdescent : baseEnd_6583373 < baseStart_6583373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583390 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6583390 : Nat := 118140960795 + 6583390 * 2 ^ 59
def prefixEnd_6583390 : Nat := 4983230072969 + 3 ^ 40 * 6583390 * 2
def baseEnd_6583390 : Nat := 1126814468667700896682849

theorem tailTrace_6583390 : CollatzResearch.WordTrace tailWord_6583390 prefixEnd_6583390 1126814468667700896682849 := by
  unfold tailWord_6583390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014494952438732292844453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160077306413006572228503749 30014494952438732292844453)
  ·
    refine ⟨5627717803582262304908335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30014494952438732292844453 5627717803582262304908335)
    ·
      refine ⟨8441576705373393457362503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627717803582262304908335 8441576705373393457362503)
      ·
        refine ⟨12662365058060090186043755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441576705373393457362503 12662365058060090186043755)
        ·
          refine ⟨18993547587090135279065633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662365058060090186043755 18993547587090135279065633)
          ·
            refine ⟨14245160690317601459299225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18993547587090135279065633 14245160690317601459299225)
            ·
              refine ⟨10683870517738201094474419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14245160690317601459299225 10683870517738201094474419)
              ·
                refine ⟨16025805776607301641711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683870517738201094474419 16025805776607301641711629)
                ·
                  refine ⟨6009677166227738115641861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16025805776607301641711629 6009677166227738115641861)
                  ·
                    refine ⟨1126814468667700896682849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009677166227738115641861 1126814468667700896682849)
                    ·
                      rfl

theorem cell23_6583390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6583390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583390 prefixEnd_6583390 := by exact prefixLift 6583390
  have htrace : WordTrace (prefixWord ++ tailWord_6583390) baseStart_6583390 baseEnd_6583390 := by
    simpa [prefixWord, tailWord_6583390, baseEnd_6583390] using wordTrace_append hprefix tailTrace_6583390
  have hstable : (prefixWord ++ tailWord_6583390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583390).length < 2 ^ (prefixWord ++ tailWord_6583390).sum := by decide
  have hdescent : baseEnd_6583390 < baseStart_6583390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583406 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6583406 : Nat := 118140960795 + 6583406 * 2 ^ 59
def prefixEnd_6583406 : Nat := 4983230072969 + 3 ^ 40 * 6583406 * 2
def baseEnd_6583406 : Nat := 3380451621693574627448473

theorem tailTrace_6583406 : CollatzResearch.WordTrace tailWord_6583406 prefixEnd_6583406 3380451621693574627448473 := by
  unfold tailWord_6583406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014567898431486634417259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160077695458301262050225381 30014567898431486634417259)
  ·
    refine ⟨45021851847647229951625889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30014567898431486634417259 45021851847647229951625889)
    ·
      refine ⟨33766388885735422463719417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45021851847647229951625889 33766388885735422463719417)
      ·
        refine ⟨25324791664301566847789563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33766388885735422463719417 25324791664301566847789563)
        ·
          refine ⟨37987187496452350271684345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25324791664301566847789563 37987187496452350271684345)
          ·
            refine ⟨28490390622339262703763259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37987187496452350271684345 28490390622339262703763259)
            ·
              refine ⟨42735585933508894055644889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28490390622339262703763259 42735585933508894055644889)
              ·
                refine ⟨32051689450131670541733667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42735585933508894055644889 32051689450131670541733667)
                ·
                  refine ⟨48077534175197505812600501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32051689450131670541733667 48077534175197505812600501)
                  ·
                    refine ⟨4507268828924766169931297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48077534175197505812600501 4507268828924766169931297)
                    ·
                      refine ⟨3380451621693574627448473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507268828924766169931297 3380451621693574627448473)
                      ·
                        rfl

theorem cell23_6583406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6583406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583406 prefixEnd_6583406 := by exact prefixLift 6583406
  have htrace : WordTrace (prefixWord ++ tailWord_6583406) baseStart_6583406 baseEnd_6583406 := by
    simpa [prefixWord, tailWord_6583406, baseEnd_6583406] using wordTrace_append hprefix tailTrace_6583406
  have hstable : (prefixWord ++ tailWord_6583406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583406).length < 2 ^ (prefixWord ++ tailWord_6583406).sum := by decide
  have hdescent : baseEnd_6583406 < baseStart_6583406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583436 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_6583436 : Nat := 118140960795 + 6583436 * 2 ^ 59
def prefixEnd_6583436 : Nat := 4983230072969 + 3 ^ 40 * 6583436 * 2
def baseEnd_6583436 : Nat := 3380467026113209510073335

theorem tailTrace_6583436 : CollatzResearch.WordTrace tailWord_6583436 prefixEnd_6583436 3380467026113209510073335 := by
  unfold tailWord_6583436
  simp only [CollatzResearch.WordTrace]
  refine ⟨120058818688671604099465081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160078424918228805465953441 120058818688671604099465081)
  ·
    refine ⟨90044114016503703074598811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120058818688671604099465081 90044114016503703074598811)
    ·
      refine ⟨135066171024755554611898217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90044114016503703074598811 135066171024755554611898217)
      ·
        refine ⟨101299628268566665958923663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135066171024755554611898217 101299628268566665958923663)
        ·
          refine ⟨151949442402849998938385495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101299628268566665958923663 151949442402849998938385495)
          ·
            refine ⟨227924163604274998407578243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151949442402849998938385495 227924163604274998407578243)
            ·
              refine ⟨341886245406412497611367365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227924163604274998407578243 341886245406412497611367365)
              ·
                refine ⟨64103671013702343302131381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341886245406412497611367365 64103671013702343302131381)
                ·
                  refine ⟨6009719157534594684574817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64103671013702343302131381 6009719157534594684574817)
                  ·
                    refine ⟨4507289368150946013431113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6009719157534594684574817 4507289368150946013431113)
                    ·
                      refine ⟨3380467026113209510073335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507289368150946013431113 3380467026113209510073335)
                      ·
                        rfl

theorem cell23_6583436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_6583436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583436 prefixEnd_6583436 := by exact prefixLift 6583436
  have htrace : WordTrace (prefixWord ++ tailWord_6583436) baseStart_6583436 baseEnd_6583436 := by
    simpa [prefixWord, tailWord_6583436, baseEnd_6583436] using wordTrace_append hprefix tailTrace_6583436
  have hstable : (prefixWord ++ tailWord_6583436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583436).length < 2 ^ (prefixWord ++ tailWord_6583436).sum := by decide
  have hdescent : baseEnd_6583436 < baseStart_6583436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583463 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6583463 : Nat := 118140960795 + 6583463 * 2 ^ 59
def prefixEnd_6583463 : Nat := 4983230072969 + 3 ^ 40 * 6583463 * 2
def baseEnd_6583463 : Nat := 1126826963363626968145237

theorem tailTrace_6583463 : CollatzResearch.WordTrace tailWord_6583463 prefixEnd_6583463 1126826963363626968145237 := by
  unfold tailWord_6583463
  simp only [CollatzResearch.WordTrace]
  refine ⟨240118622148245391810163043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160079081432163594540108695 240118622148245391810163043)
  ·
    refine ⟨360177933222368087715244565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240118622148245391810163043 360177933222368087715244565)
    ·
      refine ⟨16883340619798504111652089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 360177933222368087715244565 16883340619798504111652089)
      ·
        refine ⟨12662505464848878083739067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16883340619798504111652089 12662505464848878083739067)
        ·
          refine ⟨18993758197273317125608601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662505464848878083739067 18993758197273317125608601)
          ·
            refine ⟨14245318647954987844206451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18993758197273317125608601 14245318647954987844206451)
            ·
              refine ⟨21367977971932481766309677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14245318647954987844206451 21367977971932481766309677)
              ·
                refine ⟨8012991739474680662366129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21367977971932481766309677 8012991739474680662366129)
                ·
                  refine ⟨6009743804606010496774597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8012991739474680662366129 6009743804606010496774597)
                  ·
                    refine ⟨1126826963363626968145237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009743804606010496774597 1126826963363626968145237)
                    ·
                      rfl

theorem cell23_6583463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6583463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583463 prefixEnd_6583463 := by exact prefixLift 6583463
  have htrace : WordTrace (prefixWord ++ tailWord_6583463) baseStart_6583463 baseEnd_6583463 := by
    simpa [prefixWord, tailWord_6583463, baseEnd_6583463] using wordTrace_append hprefix tailTrace_6583463
  have hstable : (prefixWord ++ tailWord_6583463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583463).length < 2 ^ (prefixWord ++ tailWord_6583463).sum := by decide
  have hdescent : baseEnd_6583463 < baseStart_6583463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583466 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6583466 : Nat := 118140960795 + 6583466 * 2 ^ 59
def prefixEnd_6583466 : Nat := 4983230072969 + 3 ^ 40 * 6583466 * 2
def baseEnd_6583466 : Nat := 3380482430532844392698197

theorem tailTrace_6583466 : CollatzResearch.WordTrace tailWord_6583466 prefixEnd_6583466 3380482430532844392698197 := by
  unfold tailWord_6583466
  simp only [CollatzResearch.WordTrace]
  refine ⟨60029682891808630830630563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160079154378156348881681501 60029682891808630830630563)
  ·
    refine ⟨90044524337712946245945845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60029682891808630830630563 90044524337712946245945845)
    ·
      refine ⟨8441674156660588710557423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90044524337712946245945845 8441674156660588710557423)
      ·
        refine ⟨12662511234990883065836135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441674156660588710557423 12662511234990883065836135)
        ·
          refine ⟨18993766852486324598754203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662511234990883065836135 18993766852486324598754203)
          ·
            refine ⟨28490650278729486898131305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18993766852486324598754203 28490650278729486898131305)
            ·
              refine ⟨21367987709047115173598479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28490650278729486898131305 21367987709047115173598479)
              ·
                refine ⟨32051981563570672760397719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21367987709047115173598479 32051981563570672760397719)
                ·
                  refine ⟨48077972345356009140596579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32051981563570672760397719 48077972345356009140596579)
                  ·
                    refine ⟨72116958518034013710894869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48077972345356009140596579 72116958518034013710894869)
                    ·
                      refine ⟨3380482430532844392698197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72116958518034013710894869 3380482430532844392698197)
                      ·
                        rfl

theorem cell23_6583466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6583466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583466 prefixEnd_6583466 := by exact prefixLift 6583466
  have htrace : WordTrace (prefixWord ++ tailWord_6583466) baseStart_6583466 baseEnd_6583466 := by
    simpa [prefixWord, tailWord_6583466, baseEnd_6583466] using wordTrace_append hprefix tailTrace_6583466
  have hstable : (prefixWord ++ tailWord_6583466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583466).length < 2 ^ (prefixWord ++ tailWord_6583466).sum := by decide
  have hdescent : baseEnd_6583466 < baseStart_6583466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583472 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_6583472 : Nat := 118140960795 + 6583472 * 2 ^ 59
def prefixEnd_6583472 : Nat := 4983230072969 + 3 ^ 40 * 6583472 * 2
def baseEnd_6583472 : Nat := 1126828503805590456407723

theorem tailTrace_6583472 : CollatzResearch.WordTrace tailWord_6583472 prefixEnd_6583472 1126828503805590456407723 := by
  unfold tailWord_6583472
  simp only [CollatzResearch.WordTrace]
  refine ⟨120059475202606393173620335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160079300270141857564827113 120059475202606393173620335)
  ·
    refine ⟨180089212803909589760430503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120059475202606393173620335 180089212803909589760430503)
    ·
      refine ⟨270133819205864384640645755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180089212803909589760430503 270133819205864384640645755)
      ·
        refine ⟨405200728808796576960968633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270133819205864384640645755 405200728808796576960968633)
        ·
          refine ⟨303900546606597432720726475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405200728808796576960968633 303900546606597432720726475)
          ·
            refine ⟨455850819909896149081089713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303900546606597432720726475 455850819909896149081089713)
            ·
              refine ⟨341888114932422111810817285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455850819909896149081089713 341888114932422111810817285)
              ·
                refine ⟨64104021549829145964528241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341888114932422111810817285 64104021549829145964528241)
                ·
                  refine ⟨48078016162371859473396181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64104021549829145964528241 48078016162371859473396181)
                  ·
                    refine ⟨1126828503805590456407723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48078016162371859473396181 1126828503805590456407723)
                    ·
                      rfl

theorem cell23_6583472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_6583472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583472 prefixEnd_6583472 := by exact prefixLift 6583472
  have htrace : WordTrace (prefixWord ++ tailWord_6583472) baseStart_6583472 baseEnd_6583472 := by
    simpa [prefixWord, tailWord_6583472, baseEnd_6583472] using wordTrace_append hprefix tailTrace_6583472
  have hstable : (prefixWord ++ tailWord_6583472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583472).length < 2 ^ (prefixWord ++ tailWord_6583472).sum := by decide
  have hdescent : baseEnd_6583472 < baseStart_6583472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583473 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6583473 : Nat := 118140960795 + 6583473 * 2 ^ 59
def prefixEnd_6583473 : Nat := 4983230072969 + 3 ^ 40 * 6583473 * 2
def baseEnd_6583473 : Nat := 3380486024897425865310665

theorem tailTrace_6583473 : CollatzResearch.WordTrace tailWord_6583473 prefixEnd_6583473 3380486024897425865310665 := by
  unfold tailWord_6583473
  simp only [CollatzResearch.WordTrace]
  refine ⟨240118986878209163518027073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160079324585472775678684715 240118986878209163518027073)
  ·
    refine ⟨180089240158656872638520305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240118986878209163518027073 180089240158656872638520305)
    ·
      refine ⟨135066930118992654478890229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180089240158656872638520305 135066930118992654478890229)
      ·
        refine ⟨12662524698655561357395959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135066930118992654478890229 12662524698655561357395959)
        ·
          refine ⟨18993787047983342036093939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662524698655561357395959 18993787047983342036093939)
          ·
            refine ⟨28490680571975013054140909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18993787047983342036093939 28490680571975013054140909)
            ·
              refine ⟨10684005214490629895302841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28490680571975013054140909 10684005214490629895302841)
              ·
                refine ⟨8013003910867972421477131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10684005214490629895302841 8013003910867972421477131)
                ·
                  refine ⟨12019505866301958632215697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013003910867972421477131 12019505866301958632215697)
                  ·
                    refine ⟨9014629399726468974161773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12019505866301958632215697 9014629399726468974161773)
                    ·
                      refine ⟨3380486024897425865310665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014629399726468974161773 3380486024897425865310665)
                      ·
                        rfl

theorem cell23_6583473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6583473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583473 prefixEnd_6583473 := by exact prefixLift 6583473
  have htrace : WordTrace (prefixWord ++ tailWord_6583473) baseStart_6583473 baseEnd_6583473 := by
    simpa [prefixWord, tailWord_6583473, baseEnd_6583473] using wordTrace_append hprefix tailTrace_6583473
  have hstable : (prefixWord ++ tailWord_6583473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583473).length < 2 ^ (prefixWord ++ tailWord_6583473).sum := by decide
  have hdescent : baseEnd_6583473 < baseStart_6583473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583486 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_6583486 : Nat := 118140960795 + 6583486 * 2 ^ 59
def prefixEnd_6583486 : Nat := 4983230072969 + 3 ^ 40 * 6583486 * 2
def baseEnd_6583486 : Nat := 3380492700145934314448105

theorem tailTrace_6583486 : CollatzResearch.WordTrace tailWord_6583486 prefixEnd_6583486 3380492700145934314448105 := by
  unfold tailWord_6583486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014932628395258342281289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160079640684774711158833541 30014932628395258342281289)
  ·
    refine ⟨22511199471296443756710967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30014932628395258342281289 22511199471296443756710967)
    ·
      refine ⟨33766799206944665635066451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22511199471296443756710967 33766799206944665635066451)
      ·
        refine ⟨50650198810416998452599677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33766799206944665635066451 50650198810416998452599677)
        ·
          refine ⟨18993824553906374419724879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50650198810416998452599677 18993824553906374419724879)
          ·
            refine ⟨28490736830859561629587319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18993824553906374419724879 28490736830859561629587319)
            ·
              refine ⟨42736105246289342444380979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28490736830859561629587319 42736105246289342444380979)
              ·
                refine ⟨64104157869434013666571469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42736105246289342444380979 64104157869434013666571469)
                ·
                  refine ⟨24039059201037755124964301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64104157869434013666571469 24039059201037755124964301)
                  ·
                    refine ⟨9014647200389158171861613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24039059201037755124964301 9014647200389158171861613)
                    ·
                      refine ⟨3380492700145934314448105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014647200389158171861613 3380492700145934314448105)
                      ·
                        rfl

theorem cell23_6583486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_6583486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583486 prefixEnd_6583486 := by exact prefixLift 6583486
  have htrace : WordTrace (prefixWord ++ tailWord_6583486) baseStart_6583486 baseEnd_6583486 := by
    simpa [prefixWord, tailWord_6583486, baseEnd_6583486] using wordTrace_append hprefix tailTrace_6583486
  have hstable : (prefixWord ++ tailWord_6583486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583486).length < 2 ^ (prefixWord ++ tailWord_6583486).sum := by decide
  have hdescent : baseEnd_6583486 < baseStart_6583486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583510 : List Nat := [5, 2, 1, 2, 3, 1, 1, 8]
def baseStart_6583510 : Nat := 118140960795 + 6583510 * 2 ^ 59
def prefixEnd_6583510 : Nat := 4983230072969 + 3 ^ 40 * 6583510 * 2
def baseEnd_6583510 : Nat := 125203889765986748909185

theorem tailTrace_6583510 : CollatzResearch.WordTrace tailWord_6583510 prefixEnd_6583510 125203889765986748909185 := by
  unfold tailWord_6583510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007521023692194927320249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160080224252716745891415989 15007521023692194927320249)
  ·
    refine ⟨11255640767769146195490187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15007521023692194927320249 11255640767769146195490187)
    ·
      refine ⟨16883461151653719293235281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255640767769146195490187 16883461151653719293235281)
      ·
        refine ⟨12662595863740289469926461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16883461151653719293235281 12662595863740289469926461)
        ·
          refine ⟨4748473448902608551222423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12662595863740289469926461 4748473448902608551222423)
          ·
            refine ⟨7122710173353912826833635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748473448902608551222423 7122710173353912826833635)
            ·
              refine ⟨10684065260030869240250453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122710173353912826833635 10684065260030869240250453)
              ·
                refine ⟨125203889765986748909185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10684065260030869240250453 125203889765986748909185)
                ·
                  rfl

theorem cell23_6583510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_6583510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583510 prefixEnd_6583510 := by exact prefixLift 6583510
  have htrace : WordTrace (prefixWord ++ tailWord_6583510) baseStart_6583510 baseEnd_6583510 := by
    simpa [prefixWord, tailWord_6583510, baseEnd_6583510] using wordTrace_append hprefix tailTrace_6583510
  have hstable : (prefixWord ++ tailWord_6583510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583510).length < 2 ^ (prefixWord ++ tailWord_6583510).sum := by decide
  have hdescent : baseEnd_6583510 < baseStart_6583510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583554 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_6583554 : Nat := 118140960795 + 6583554 * 2 ^ 59
def prefixEnd_6583554 : Nat := 4983230072969 + 3 ^ 40 * 6583554 * 2
def baseEnd_6583554 : Nat := 3380527616830440048397793

theorem tailTrace_6583554 : CollatzResearch.WordTrace tailWord_6583554 prefixEnd_6583554 3380527616830440048397793 := by
  unfold tailWord_6583554
  simp only [CollatzResearch.WordTrace]
  refine ⟨60030485297728928587931429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160081294127277142901150477 60030485297728928587931429)
  ·
    refine ⟨11255715993324174110237143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60030485297728928587931429 11255715993324174110237143)
    ·
      refine ⟨16883573989986261165355715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255715993324174110237143 16883573989986261165355715)
      ·
        refine ⟨25325360984979391748033573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16883573989986261165355715 25325360984979391748033573)
        ·
          refine ⟨4748505184683635952756295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25325360984979391748033573 4748505184683635952756295)
          ·
            refine ⟨7122757777025453929134443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748505184683635952756295 7122757777025453929134443)
            ·
              refine ⟨10684136665538180893701665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122757777025453929134443 10684136665538180893701665)
              ·
                refine ⟨8013102499153635670276249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10684136665538180893701665 8013102499153635670276249)
                ·
                  refine ⟨6009826874365226752707187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8013102499153635670276249 6009826874365226752707187)
                  ·
                    refine ⟨9014740311547840129060781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6009826874365226752707187 9014740311547840129060781)
                    ·
                      refine ⟨3380527616830440048397793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014740311547840129060781 3380527616830440048397793)
                      ·
                        rfl

theorem cell23_6583554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_6583554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583554 prefixEnd_6583554 := by exact prefixLift 6583554
  have htrace : WordTrace (prefixWord ++ tailWord_6583554) baseStart_6583554 baseEnd_6583554 := by
    simpa [prefixWord, tailWord_6583554, baseEnd_6583554] using wordTrace_append hprefix tailTrace_6583554
  have hstable : (prefixWord ++ tailWord_6583554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583554).length < 2 ^ (prefixWord ++ tailWord_6583554).sum := by decide
  have hdescent : baseEnd_6583554 < baseStart_6583554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583556 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6583556 : Nat := 118140960795 + 6583556 * 2 ^ 59
def prefixEnd_6583556 : Nat := 4983230072969 + 3 ^ 40 * 6583556 * 2
def baseEnd_6583556 : Nat := 3380528643791749040572783

theorem tailTrace_6583556 : CollatzResearch.WordTrace tailWord_6583556 prefixEnd_6583556 3380528643791749040572783 := by
  unfold tailWord_6583556
  simp only [CollatzResearch.WordTrace]
  refine ⟨120061007068454234346649261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160081342757938979128865681 120061007068454234346649261)
  ·
    refine ⟨45022877650670337879993473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120061007068454234346649261 45022877650670337879993473)
    ·
      refine ⟨33767158238002753409995105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45022877650670337879993473 33767158238002753409995105)
      ·
        refine ⟨25325368678502065057496329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33767158238002753409995105 25325368678502065057496329)
        ·
          refine ⟨18994026508876548793122247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25325368678502065057496329 18994026508876548793122247)
          ·
            refine ⟨28491039763314823189683371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18994026508876548793122247 28491039763314823189683371)
            ·
              refine ⟨42736559644972234784525057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28491039763314823189683371 42736559644972234784525057)
              ·
                refine ⟨32052419733729176088393793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42736559644972234784525057 32052419733729176088393793)
                ·
                  refine ⟨24039314800296882066295345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32052419733729176088393793 24039314800296882066295345)
                  ·
                    refine ⟨18029486100222661549721509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24039314800296882066295345 18029486100222661549721509)
                    ·
                      refine ⟨3380528643791749040572783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18029486100222661549721509 3380528643791749040572783)
                      ·
                        rfl

theorem cell23_6583556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6583556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583556 prefixEnd_6583556 := by exact prefixLift 6583556
  have htrace : WordTrace (prefixWord ++ tailWord_6583556) baseStart_6583556 baseEnd_6583556 := by
    simpa [prefixWord, tailWord_6583556, baseEnd_6583556] using wordTrace_append hprefix tailTrace_6583556
  have hstable : (prefixWord ++ tailWord_6583556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583556).length < 2 ^ (prefixWord ++ tailWord_6583556).sum := by decide
  have hdescent : baseEnd_6583556 < baseStart_6583556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583560 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_6583560 : Nat := 118140960795 + 6583560 * 2 ^ 59
def prefixEnd_6583560 : Nat := 4983230072969 + 3 ^ 40 * 6583560 * 2
def baseEnd_6583560 : Nat := 3380530697714367024922765

theorem tailTrace_6583560 : CollatzResearch.WordTrace tailWord_6583560 prefixEnd_6583560 3380530697714367024922765 := by
  unfold tailWord_6583560
  simp only [CollatzResearch.WordTrace]
  refine ⟨120061080014446988688222067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160081440019262651584296089 120061080014446988688222067)
  ·
    refine ⟨180091620021670483032333101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120061080014446988688222067 180091620021670483032333101)
    ·
      refine ⟨67534357508126431137124913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180091620021670483032333101 67534357508126431137124913)
      ·
        refine ⟨50650768131094823352843685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67534357508126431137124913 50650768131094823352843685)
        ·
          refine ⟨9497019024580279378658191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50650768131094823352843685 9497019024580279378658191)
          ·
            refine ⟨14245528536870419067987287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9497019024580279378658191 14245528536870419067987287)
            ·
              refine ⟨21368292805305628601980931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14245528536870419067987287 21368292805305628601980931)
              ·
                refine ⟨32052439207958442902971397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21368292805305628601980931 32052439207958442902971397)
                ·
                  refine ⟨6009832351492208044307137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32052439207958442902971397 6009832351492208044307137)
                  ·
                    refine ⟨4507374263619156033230353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6009832351492208044307137 4507374263619156033230353)
                    ·
                      refine ⟨3380530697714367024922765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507374263619156033230353 3380530697714367024922765)
                      ·
                        rfl

theorem cell23_6583560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_6583560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583560 prefixEnd_6583560 := by exact prefixLift 6583560
  have htrace : WordTrace (prefixWord ++ tailWord_6583560) baseStart_6583560 baseEnd_6583560 := by
    simpa [prefixWord, tailWord_6583560, baseEnd_6583560] using wordTrace_append hprefix tailTrace_6583560
  have hstable : (prefixWord ++ tailWord_6583560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583560).length < 2 ^ (prefixWord ++ tailWord_6583560).sum := by decide
  have hdescent : baseEnd_6583560 < baseStart_6583560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583566 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_6583566 : Nat := 118140960795 + 6583566 * 2 ^ 59
def prefixEnd_6583566 : Nat := 4983230072969 + 3 ^ 40 * 6583566 * 2
def baseEnd_6583566 : Nat := 375614864288699333494193

theorem tailTrace_6583566 : CollatzResearch.WordTrace tailWord_6583566 prefixEnd_6583566 375614864288699333494193 := by
  unfold tailWord_6583566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015297358359030050145319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160081585911248160267441701 30015297358359030050145319)
  ·
    refine ⟨45022946037538545075217979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30015297358359030050145319 45022946037538545075217979)
    ·
      refine ⟨67534419056307817612826969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45022946037538545075217979 67534419056307817612826969)
      ·
        refine ⟨50650814292230863209620227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67534419056307817612826969 50650814292230863209620227)
        ·
          refine ⟨75976221438346294814430341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50650814292230863209620227 75976221438346294814430341)
          ·
            refine ⟨14245541519689930277705689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75976221438346294814430341 14245541519689930277705689)
            ·
              refine ⟨10684156139767447708279267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14245541519689930277705689 10684156139767447708279267)
              ·
                refine ⟨16026234209651171562418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684156139767447708279267 16026234209651171562418901)
                ·
                  refine ⟨375614864288699333494193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16026234209651171562418901 375614864288699333494193)
                  ·
                    rfl

theorem cell23_6583566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_6583566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583566 prefixEnd_6583566 := by exact prefixLift 6583566
  have htrace : WordTrace (prefixWord ++ tailWord_6583566) baseStart_6583566 baseEnd_6583566 := by
    simpa [prefixWord, tailWord_6583566, baseEnd_6583566] using wordTrace_append hprefix tailTrace_6583566
  have hstable : (prefixWord ++ tailWord_6583566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583566).length < 2 ^ (prefixWord ++ tailWord_6583566).sum := by decide
  have hdescent : baseEnd_6583566 < baseStart_6583566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583576 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6583576 : Nat := 118140960795 + 6583576 * 2 ^ 59
def prefixEnd_6583576 : Nat := 4983230072969 + 3 ^ 40 * 6583576 * 2
def baseEnd_6583576 : Nat := 3380538913404838962322691

theorem tailTrace_6583576 : CollatzResearch.WordTrace tailWord_6583576 prefixEnd_6583576 3380538913404838962322691 := by
  unfold tailWord_6583576
  simp only [CollatzResearch.WordTrace]
  refine ⟨120061371798418006054513291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160081829064557341406017721 120061371798418006054513291)
  ·
    refine ⟨180092057697627009081769937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120061371798418006054513291 180092057697627009081769937)
    ·
      refine ⟨135069043273220256811327453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180092057697627009081769937 135069043273220256811327453)
      ·
        refine ⟨50650891227457596304247795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135069043273220256811327453 50650891227457596304247795)
        ·
          refine ⟨75976336841186394456371693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50650891227457596304247795 75976336841186394456371693)
          ·
            refine ⟨28491126315444897921139385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75976336841186394456371693 28491126315444897921139385)
            ·
              refine ⟨21368344736583673440854539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28491126315444897921139385 21368344736583673440854539)
              ·
                refine ⟨32052517104875510161281809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21368344736583673440854539 32052517104875510161281809)
                ·
                  refine ⟨24039387828656632620961357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32052517104875510161281809 24039387828656632620961357)
                  ·
                    refine ⟨9014770435746237232860509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24039387828656632620961357 9014770435746237232860509)
                    ·
                      refine ⟨3380538913404838962322691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014770435746237232860509 3380538913404838962322691)
                      ·
                        rfl

theorem cell23_6583576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6583576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583576 prefixEnd_6583576 := by exact prefixLift 6583576
  have htrace : WordTrace (prefixWord ++ tailWord_6583576) baseStart_6583576 baseEnd_6583576 := by
    simpa [prefixWord, tailWord_6583576, baseEnd_6583576] using wordTrace_append hprefix tailTrace_6583576
  have hstable : (prefixWord ++ tailWord_6583576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583576).length < 2 ^ (prefixWord ++ tailWord_6583576).sum := by decide
  have hdescent : baseEnd_6583576 < baseStart_6583576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583616 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_6583616 : Nat := 118140960795 + 6583616 * 2 ^ 59
def prefixEnd_6583616 : Nat := 4983230072969 + 3 ^ 40 * 6583616 * 2
def baseEnd_6583616 : Nat := 3380559452631018805822507

theorem tailTrace_6583616 : CollatzResearch.WordTrace tailWord_6583616 prefixEnd_6583616 3380559452631018805822507 := by
  unfold tailWord_6583616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120062101258345549470241351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160082801677794065960321801 120062101258345549470241351)
  ·
    refine ⟨180093151887518324205362027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120062101258345549470241351 180093151887518324205362027)
    ·
      refine ⟨270139727831277486308043041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180093151887518324205362027 270139727831277486308043041)
      ·
        refine ⟨202604795873458114731032281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270139727831277486308043041 202604795873458114731032281)
        ·
          refine ⟨151953596905093586048274211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202604795873458114731032281 151953596905093586048274211)
          ·
            refine ⟨227930395357640379072411317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151953596905093586048274211 227930395357640379072411317)
            ·
              refine ⟨21368474564778785538038561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227930395357640379072411317 21368474564778785538038561)
              ·
                refine ⟨16026355923584089153528921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21368474564778785538038561 16026355923584089153528921)
                ·
                  refine ⟨12019766942688066865146691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16026355923584089153528921 12019766942688066865146691)
                  ·
                    refine ⟨18029650414032100297720037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12019766942688066865146691 18029650414032100297720037)
                    ·
                      refine ⟨3380559452631018805822507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18029650414032100297720037 3380559452631018805822507)
                      ·
                        rfl

theorem cell23_6583616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_6583616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583616 prefixEnd_6583616 := by exact prefixLift 6583616
  have htrace : WordTrace (prefixWord ++ tailWord_6583616) baseStart_6583616 baseEnd_6583616 := by
    simpa [prefixWord, tailWord_6583616, baseEnd_6583616] using wordTrace_append hprefix tailTrace_6583616
  have hstable : (prefixWord ++ tailWord_6583616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583616).length < 2 ^ (prefixWord ++ tailWord_6583616).sum := by decide
  have hdescent : baseEnd_6583616 < baseStart_6583616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583653 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_6583653 : Nat := 118140960795 + 6583653 * 2 ^ 59
def prefixEnd_6583653 : Nat := 4983230072969 + 3 ^ 40 * 6583653 * 2
def baseEnd_6583653 : Nat := 3380578451415235161059837

theorem tailTrace_6583653 : CollatzResearch.WordTrace tailWord_6583653 prefixEnd_6583653 3380578451415235161059837 := by
  unfold tailWord_6583653
  simp only [CollatzResearch.WordTrace]
  refine ⟨240125552017557054259579613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160083701345038036173053075 240125552017557054259579613)
  ·
    refine ⟨90047082006583895347342355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240125552017557054259579613 90047082006583895347342355)
    ·
      refine ⟨135070623009875843021013533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90047082006583895347342355 135070623009875843021013533)
      ·
        refine ⟨50651483628703441132880075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135070623009875843021013533 50651483628703441132880075)
        ·
          refine ⟨75977225443055161699320113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50651483628703441132880075 75977225443055161699320113)
          ·
            refine ⟨56982919082291371274490085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75977225443055161699320113 56982919082291371274490085)
            ·
              refine ⟨10684297327929632113966891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56982919082291371274490085 10684297327929632113966891)
              ·
                refine ⟨16026445991894448170950337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684297327929632113966891 16026445991894448170950337)
                ·
                  refine ⟨12019834493920836128212753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16026445991894448170950337 12019834493920836128212753)
                  ·
                    refine ⟨9014875870440627096159565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12019834493920836128212753 9014875870440627096159565)
                    ·
                      refine ⟨3380578451415235161059837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014875870440627096159565 3380578451415235161059837)
                      ·
                        rfl

theorem cell23_6583653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_6583653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583653 prefixEnd_6583653 := by exact prefixLift 6583653
  have htrace : WordTrace (prefixWord ++ tailWord_6583653) baseStart_6583653 baseEnd_6583653 := by
    simpa [prefixWord, tailWord_6583653, baseEnd_6583653] using wordTrace_append hprefix tailTrace_6583653
  have hstable : (prefixWord ++ tailWord_6583653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583653).length < 2 ^ (prefixWord ++ tailWord_6583653).sum := by decide
  have hdescent : baseEnd_6583653 < baseStart_6583653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583679 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_6583679 : Nat := 118140960795 + 6583679 * 2 ^ 59
def prefixEnd_6583679 : Nat := 4983230072969 + 3 ^ 40 * 6583679 * 2
def baseEnd_6583679 : Nat := 3380591801912252059334717

theorem tailTrace_6583679 : CollatzResearch.WordTrace tailWord_6583679 prefixEnd_6583679 3380591801912252059334717 := by
  unfold tailWord_6583679
  simp only [CollatzResearch.WordTrace]
  refine ⟨240126500315462860700026091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160084333543641907133350727 240126500315462860700026091)
  ·
    refine ⟨360189750473194291050039137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240126500315462860700026091 360189750473194291050039137)
    ·
      refine ⟨270142312854895718287529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360189750473194291050039137 270142312854895718287529353)
      ·
        refine ⟨202606734641171788715647015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270142312854895718287529353 202606734641171788715647015)
        ·
          refine ⟨303910101961757683073470523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202606734641171788715647015 303910101961757683073470523)
          ·
            refine ⟨455865152942636524610205785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303910101961757683073470523 455865152942636524610205785)
            ·
              refine ⟨341898864706977393457654339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455865152942636524610205785 341898864706977393457654339)
              ·
                refine ⟨512848297060466090186481509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341898864706977393457654339 512848297060466090186481509)
                ·
                  refine ⟨96159055698837391909965283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512848297060466090186481509 96159055698837391909965283)
                  ·
                    refine ⟨144238583548256087864947925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96159055698837391909965283 144238583548256087864947925)
                    ·
                      refine ⟨3380591801912252059334717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144238583548256087864947925 3380591801912252059334717)
                      ·
                        rfl

theorem cell23_6583679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_6583679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583679 prefixEnd_6583679 := by exact prefixLift 6583679
  have htrace : WordTrace (prefixWord ++ tailWord_6583679) baseStart_6583679 baseEnd_6583679 := by
    simpa [prefixWord, tailWord_6583679, baseEnd_6583679] using wordTrace_append hprefix tailTrace_6583679
  have hstable : (prefixWord ++ tailWord_6583679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583679).length < 2 ^ (prefixWord ++ tailWord_6583679).sum := by decide
  have hdescent : baseEnd_6583679 < baseStart_6583679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583700 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6583700 : Nat := 118140960795 + 6583700 * 2 ^ 59
def prefixEnd_6583700 : Nat := 4983230072969 + 3 ^ 40 * 6583700 * 2
def baseEnd_6583700 : Nat := 3380602585005996477172121

theorem tailTrace_6583700 : CollatzResearch.WordTrace tailWord_6583700 prefixEnd_6583700 3380602585005996477172121 := by
  unfold tailWord_6583700
  simp only [CollatzResearch.WordTrace]
  refine ⟨120063633124193390643270277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160084844165591187524360369 120063633124193390643270277)
  ·
    refine ⟨22511931210786260745613177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120063633124193390643270277 22511931210786260745613177)
    ·
      refine ⟨16883948408089695559209883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22511931210786260745613177 16883948408089695559209883)
      ·
        refine ⟨25325922612134543338814825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16883948408089695559209883 25325922612134543338814825)
        ·
          refine ⟨18994441959100907504111119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25325922612134543338814825 18994441959100907504111119)
          ·
            refine ⟨28491662938651361256166679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18994441959100907504111119 28491662938651361256166679)
            ·
              refine ⟨42737494407977041884250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28491662938651361256166679 42737494407977041884250019)
              ·
                refine ⟨64106241611965562826375029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42737494407977041884250019 64106241611965562826375029)
                ·
                  refine ⟨6009960151121771514972659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64106241611965562826375029 6009960151121771514972659)
                  ·
                    refine ⟨9014940226682657272458989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6009960151121771514972659 9014940226682657272458989)
                    ·
                      refine ⟨3380602585005996477172121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9014940226682657272458989 3380602585005996477172121)
                      ·
                        rfl

theorem cell23_6583700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6583700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583700 prefixEnd_6583700 := by exact prefixLift 6583700
  have htrace : WordTrace (prefixWord ++ tailWord_6583700) baseStart_6583700 baseEnd_6583700 := by
    simpa [prefixWord, tailWord_6583700, baseEnd_6583700] using wordTrace_append hprefix tailTrace_6583700
  have hstable : (prefixWord ++ tailWord_6583700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583700).length < 2 ^ (prefixWord ++ tailWord_6583700).sum := by decide
  have hdescent : baseEnd_6583700 < baseStart_6583700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583736 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6583736 : Nat := 118140960795 + 6583736 * 2 ^ 59
def prefixEnd_6583736 : Nat := 4983230072969 + 3 ^ 40 * 6583736 * 2
def baseEnd_6583736 : Nat := 3380621070309558336321955

theorem tailTrace_6583736 : CollatzResearch.WordTrace tailWord_6583736 prefixEnd_6583736 3380621070309558336321955 := by
  unfold tailWord_6583736
  simp only [CollatzResearch.WordTrace]
  refine ⟨120064289638128179717425531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160085719517504239623234041 120064289638128179717425531)
  ·
    refine ⟨180096434457192269576138297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120064289638128179717425531 180096434457192269576138297)
    ·
      refine ⟨135072325842894202182103723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180096434457192269576138297 135072325842894202182103723)
      ·
        refine ⟨202608488764341303273155585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135072325842894202182103723 202608488764341303273155585)
        ·
          refine ⟨151956366573255977454866689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202608488764341303273155585 151956366573255977454866689)
          ·
            refine ⟨113967274929941983091150017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151956366573255977454866689 113967274929941983091150017)
            ·
              refine ⟨85475456197456487318362513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113967274929941983091150017 85475456197456487318362513)
              ·
                refine ⟨64106592148092365488771885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85475456197456487318362513 64106592148092365488771885)
                ·
                  refine ⟨24039972055534637058289457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64106592148092365488771885 24039972055534637058289457)
                  ·
                    refine ⟨18029979041650977793717093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24039972055534637058289457 18029979041650977793717093)
                    ·
                      refine ⟨3380621070309558336321955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18029979041650977793717093 3380621070309558336321955)
                      ·
                        rfl

theorem cell23_6583736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6583736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583736 prefixEnd_6583736 := by exact prefixLift 6583736
  have htrace : WordTrace (prefixWord ++ tailWord_6583736) baseStart_6583736 baseEnd_6583736 := by
    simpa [prefixWord, tailWord_6583736, baseEnd_6583736] using wordTrace_append hprefix tailTrace_6583736
  have hstable : (prefixWord ++ tailWord_6583736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583736).length < 2 ^ (prefixWord ++ tailWord_6583736).sum := by decide
  have hdescent : baseEnd_6583736 < baseStart_6583736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583790 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_6583790 : Nat := 118140960795 + 6583790 * 2 ^ 59
def prefixEnd_6583790 : Nat := 4983230072969 + 3 ^ 40 * 6583790 * 2
def baseEnd_6583790 : Nat := 3380648798264901125046707

theorem tailTrace_6583790 : CollatzResearch.WordTrace tailWord_6583790 prefixEnd_6583790 3380648798264901125046707 := by
  unfold tailWord_6583790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016318602257590832164603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160087032545373817771544549 30016318602257590832164603)
  ·
    refine ⟨45024477903386386248246905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30016318602257590832164603 45024477903386386248246905)
    ·
      refine ⟨33768358427539789686185179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45024477903386386248246905 33768358427539789686185179)
      ·
        refine ⟨50652537641309684529277769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33768358427539789686185179 50652537641309684529277769)
        ·
          refine ⟨37989403230982263396958327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50652537641309684529277769 37989403230982263396958327)
          ·
            refine ⟨56984104846473395095437491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37989403230982263396958327 56984104846473395095437491)
            ·
              refine ⟨85476157269710092643156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56984104846473395095437491 85476157269710092643156237)
              ·
                refine ⟨32053558976141284741183589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85476157269710092643156237 32053558976141284741183589)
                ·
                  refine ⟨6010042308026490888971923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32053558976141284741183589 6010042308026490888971923)
                  ·
                    refine ⟨9015063462039736333457885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6010042308026490888971923 9015063462039736333457885)
                    ·
                      refine ⟨3380648798264901125046707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015063462039736333457885 3380648798264901125046707)
                      ·
                        rfl

theorem cell23_6583790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_6583790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583790 prefixEnd_6583790 := by exact prefixLift 6583790
  have htrace : WordTrace (prefixWord ++ tailWord_6583790) baseStart_6583790 baseEnd_6583790 := by
    simpa [prefixWord, tailWord_6583790, baseEnd_6583790] using wordTrace_append hprefix tailTrace_6583790
  have hstable : (prefixWord ++ tailWord_6583790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583790).length < 2 ^ (prefixWord ++ tailWord_6583790).sum := by decide
  have hdescent : baseEnd_6583790 < baseStart_6583790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583856 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_6583856 : Nat := 118140960795 + 6583856 * 2 ^ 59
def prefixEnd_6583856 : Nat := 4983230072969 + 3 ^ 40 * 6583856 * 2
def baseEnd_6583856 : Nat := 3380682687988097866821403

theorem tailTrace_6583856 : CollatzResearch.WordTrace tailWord_6583856 prefixEnd_6583856 3380682687988097866821403 := by
  unfold tailWord_6583856
  simp only [CollatzResearch.WordTrace]
  refine ⟨120066478017910809964609711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160088637357214413286146281 120066478017910809964609711)
  ·
    refine ⟨180099717026866214946914567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120066478017910809964609711 180099717026866214946914567)
    ·
      refine ⟨270149575540299322420371851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180099717026866214946914567 270149575540299322420371851)
      ·
        refine ⟨405224363310448983630557777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270149575540299322420371851 405224363310448983630557777)
        ·
          refine ⟨303918272482836737722918333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405224363310448983630557777 303918272482836737722918333)
          ·
            refine ⟨113969352181063776646094375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303918272482836737722918333 113969352181063776646094375)
            ·
              refine ⟨170954028271595664969141563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113969352181063776646094375 170954028271595664969141563)
              ·
                refine ⟨256431042407393497453712345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170954028271595664969141563 256431042407393497453712345)
                ·
                  refine ⟨192323281805545123090284259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256431042407393497453712345 192323281805545123090284259)
                  ·
                    refine ⟨288484922708317684635426389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192323281805545123090284259 288484922708317684635426389)
                    ·
                      refine ⟨3380682687988097866821403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 288484922708317684635426389 3380682687988097866821403)
                      ·
                        rfl

theorem cell23_6583856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_6583856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583856 prefixEnd_6583856 := by exact prefixLift 6583856
  have htrace : WordTrace (prefixWord ++ tailWord_6583856) baseStart_6583856 baseEnd_6583856 := by
    simpa [prefixWord, tailWord_6583856, baseEnd_6583856] using wordTrace_append hprefix tailTrace_6583856
  have hstable : (prefixWord ++ tailWord_6583856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583856).length < 2 ^ (prefixWord ++ tailWord_6583856).sum := by decide
  have hdescent : baseEnd_6583856 < baseStart_6583856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583863 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_6583863 : Nat := 118140960795 + 6583863 * 2 ^ 59
def prefixEnd_6583863 : Nat := 4983230072969 + 3 ^ 40 * 6583863 * 2
def baseEnd_6583863 : Nat := 3380686282352679339433871

theorem tailTrace_6583863 : CollatzResearch.WordTrace tailWord_6583863 prefixEnd_6583863 3380686282352679339433871 := by
  unfold tailWord_6583863
  simp only [CollatzResearch.WordTrace]
  refine ⟨240133211346796260124724243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160088807564530840083149495 240133211346796260124724243)
  ·
    refine ⟨360199817020194390187086365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240133211346796260124724243 360199817020194390187086365)
    ·
      refine ⟨135074931382572896320157387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360199817020194390187086365 135074931382572896320157387)
      ·
        refine ⟨202612397073859344480236081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135074931382572896320157387 202612397073859344480236081)
        ·
          refine ⟨151959297805394508360177061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202612397073859344480236081 151959297805394508360177061)
          ·
            refine ⟨28492368338511470317533199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151959297805394508360177061 28492368338511470317533199)
            ·
              refine ⟨42738552507767205476299799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28492368338511470317533199 42738552507767205476299799)
              ·
                refine ⟨64107828761650808214449699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42738552507767205476299799 64107828761650808214449699)
                ·
                  refine ⟨96161743142476212321674549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64107828761650808214449699 96161743142476212321674549)
                  ·
                    refine ⟨9015163419607144905156989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96161743142476212321674549 9015163419607144905156989)
                    ·
                      refine ⟨3380686282352679339433871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015163419607144905156989 3380686282352679339433871)
                      ·
                        rfl

theorem cell23_6583863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_6583863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583863 prefixEnd_6583863 := by exact prefixLift 6583863
  have htrace : WordTrace (prefixWord ++ tailWord_6583863) baseStart_6583863 baseEnd_6583863 := by
    simpa [prefixWord, tailWord_6583863, baseEnd_6583863] using wordTrace_append hprefix tailTrace_6583863
  have hstable : (prefixWord ++ tailWord_6583863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583863).length < 2 ^ (prefixWord ++ tailWord_6583863).sum := by decide
  have hdescent : baseEnd_6583863 < baseStart_6583863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583943 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 8]
def baseStart_6583943 : Nat := 118140960795 + 6583943 * 2 ^ 59
def prefixEnd_6583943 : Nat := 4983230072969 + 3 ^ 40 * 6583943 * 2
def baseEnd_6583943 : Nat := 375636373422782114048167

theorem tailTrace_6583943 : CollatzResearch.WordTrace tailWord_6583943 prefixEnd_6583943 375636373422782114048167 := by
  unfold tailWord_6583943
  simp only [CollatzResearch.WordTrace]
  refine ⟨240136129186506433787636483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160090752791004289191757655 240136129186506433787636483)
  ·
    refine ⟨360204193779759650681454725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240136129186506433787636483 360204193779759650681454725)
    ·
      refine ⟨67538286333704934502772761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360204193779759650681454725 67538286333704934502772761)
      ·
        refine ⟨50653714750278700877079571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67538286333704934502772761 50653714750278700877079571)
        ·
          refine ⟨75980572125418051315619357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50653714750278700877079571 75980572125418051315619357)
          ·
            refine ⟨28492714547031769243357259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75980572125418051315619357 28492714547031769243357259)
            ·
              refine ⟨42739071820547653865035889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28492714547031769243357259 42739071820547653865035889)
              ·
                refine ⟨32054303865410740398776917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42739071820547653865035889 32054303865410740398776917)
                ·
                  refine ⟨375636373422782114048167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32054303865410740398776917 375636373422782114048167)
                  ·
                    rfl

theorem cell23_6583943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 8].length) (baseStart_6583943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583943 prefixEnd_6583943 := by exact prefixLift 6583943
  have htrace : WordTrace (prefixWord ++ tailWord_6583943) baseStart_6583943 baseEnd_6583943 := by
    simpa [prefixWord, tailWord_6583943, baseEnd_6583943] using wordTrace_append hprefix tailTrace_6583943
  have hstable : (prefixWord ++ tailWord_6583943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583943).length < 2 ^ (prefixWord ++ tailWord_6583943).sum := by decide
  have hdescent : baseEnd_6583943 < baseStart_6583943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583964 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_6583964 : Nat := 118140960795 + 6583964 * 2 ^ 59
def prefixEnd_6583964 : Nat := 4983230072969 + 3 ^ 40 * 6583964 * 2
def baseEnd_6583964 : Nat := 1126912714632927814756969

theorem tailTrace_6583964 : CollatzResearch.WordTrace tailWord_6583964 prefixEnd_6583964 1126912714632927814756969 := by
  unfold tailWord_6583964
  simp only [CollatzResearch.WordTrace]
  refine ⟨120068447559715177187075473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160091263412953569582767297 120068447559715177187075473)
  ·
    refine ⟨90051335669786382890306605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120068447559715177187075473 90051335669786382890306605)
    ·
      refine ⟨33769250876169893583864977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90051335669786382890306605 33769250876169893583864977)
      ·
        refine ⟨25326938157127420187898733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33769250876169893583864977 25326938157127420187898733)
        ·
          refine ⟨9497601808922782570462025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25326938157127420187898733 9497601808922782570462025)
          ·
            refine ⟨7123201356692086927846519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497601808922782570462025 7123201356692086927846519)
            ·
              refine ⟨10684802035038130391769779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123201356692086927846519 10684802035038130391769779)
              ·
                refine ⟨16027203052557195587654669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684802035038130391769779 16027203052557195587654669)
                ·
                  refine ⟨6010201144708948345370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16027203052557195587654669 6010201144708948345370501)
                  ·
                    refine ⟨1126912714632927814756969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010201144708948345370501 1126912714632927814756969)
                    ·
                      rfl

theorem cell23_6583964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_6583964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6583964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6583964 prefixEnd_6583964 := by exact prefixLift 6583964
  have htrace : WordTrace (prefixWord ++ tailWord_6583964) baseStart_6583964 baseEnd_6583964 := by
    simpa [prefixWord, tailWord_6583964, baseEnd_6583964] using wordTrace_append hprefix tailTrace_6583964
  have hstable : (prefixWord ++ tailWord_6583964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583964).length < 2 ^ (prefixWord ++ tailWord_6583964).sum := by decide
  have hdescent : baseEnd_6583964 < baseStart_6583964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584007 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 1, 5]
def baseStart_6584007 : Nat := 118140960795 + 6584007 * 2 ^ 59
def prefixEnd_6584007 : Nat := 4983230072969 + 3 ^ 40 * 6584007 * 2
def baseEnd_6584007 : Nat := 1126920074522308925344403

theorem tailTrace_6584007 : CollatzResearch.WordTrace tailWord_6584007 prefixEnd_6584007 1126920074522308925344403 := by
  unfold tailWord_6584007
  simp only [CollatzResearch.WordTrace]
  refine ⟨240138463458274572717966275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160092308972183048478644183 240138463458274572717966275)
  ·
    refine ⟨360207695187411859076949413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240138463458274572717966275 360207695187411859076949413)
    ·
      refine ⟨67538942847639723576928015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360207695187411859076949413 67538942847639723576928015)
      ·
        refine ⟨101308414271459585365392023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67538942847639723576928015 101308414271459585365392023)
        ·
          refine ⟨151962621407189378048088035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101308414271459585365392023 151962621407189378048088035)
          ·
            refine ⟨227943932110784067072132053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151962621407189378048088035 227943932110784067072132053)
            ·
              refine ⟨5342435908846501572003095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 227943932110784067072132053 5342435908846501572003095)
              ·
                refine ⟨8013653863269752358004643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342435908846501572003095 8013653863269752358004643)
                ·
                  refine ⟨12020480794904628537006965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013653863269752358004643 12020480794904628537006965)
                  ·
                    refine ⟨1126920074522308925344403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12020480794904628537006965 1126920074522308925344403)
                    ·
                      rfl

theorem cell23_6584007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_6584007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584007 prefixEnd_6584007 := by exact prefixLift 6584007
  have htrace : WordTrace (prefixWord ++ tailWord_6584007) baseStart_6584007 baseEnd_6584007 := by
    simpa [prefixWord, tailWord_6584007, baseEnd_6584007] using wordTrace_append hprefix tailTrace_6584007
  have hstable : (prefixWord ++ tailWord_6584007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584007).length < 2 ^ (prefixWord ++ tailWord_6584007).sum := by decide
  have hdescent : baseEnd_6584007 < baseStart_6584007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584037 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_6584037 : Nat := 118140960795 + 6584037 * 2 ^ 59
def prefixEnd_6584037 : Nat := 4983230072969 + 3 ^ 40 * 6584037 * 2
def baseEnd_6584037 : Nat := 1126925209328853886219357

theorem tailTrace_6584037 : CollatzResearch.WordTrace tailWord_6584037 prefixEnd_6584037 1126925209328853886219357 := by
  unfold tailWord_6584037
  simp only [CollatzResearch.WordTrace]
  refine ⟨240139557648165887841558365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160093038432110591894372243 240139557648165887841558365)
  ·
    refine ⟨90052334118062207940584387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240139557648165887841558365 90052334118062207940584387)
    ·
      refine ⟨135078501177093311910876581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90052334118062207940584387 135078501177093311910876581)
      ·
        refine ⟨25327218970704995983289359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135078501177093311910876581 25327218970704995983289359)
        ·
          refine ⟨37990828456057493974934039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25327218970704995983289359 37990828456057493974934039)
          ·
            refine ⟨56986242684086240962401059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37990828456057493974934039 56986242684086240962401059)
            ·
              refine ⟨85479364026129361443601589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56986242684086240962401059 85479364026129361443601589)
              ·
                refine ⟨8013690377449627635337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85479364026129361443601589 8013690377449627635337649)
                ·
                  refine ⟨6010267783087220726503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8013690377449627635337649 6010267783087220726503237)
                  ·
                    refine ⟨1126925209328853886219357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010267783087220726503237 1126925209328853886219357)
                    ·
                      rfl

theorem cell23_6584037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_6584037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584037 prefixEnd_6584037 := by exact prefixLift 6584037
  have htrace : WordTrace (prefixWord ++ tailWord_6584037) baseStart_6584037 baseEnd_6584037 := by
    simpa [prefixWord, tailWord_6584037, baseEnd_6584037] using wordTrace_append hprefix tailTrace_6584037
  have hstable : (prefixWord ++ tailWord_6584037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584037).length < 2 ^ (prefixWord ++ tailWord_6584037).sum := by decide
  have hdescent : baseEnd_6584037 < baseStart_6584037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584047 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_6584047 : Nat := 118140960795 + 6584047 * 2 ^ 59
def prefixEnd_6584047 : Nat := 4983230072969 + 3 ^ 40 * 6584047 * 2
def baseEnd_6584047 : Nat := 3380780762793106619533025

theorem tailTrace_6584047 : CollatzResearch.WordTrace tailWord_6584047 prefixEnd_6584047 3380780762793106619533025 := by
  unfold tailWord_6584047
  simp only [CollatzResearch.WordTrace]
  refine ⟨240139922378129659549422395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160093281585419773032948263 240139922378129659549422395)
  ·
    refine ⟨360209883567194489324133593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240139922378129659549422395 360209883567194489324133593)
    ·
      refine ⟨270157412675395866993100195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360209883567194489324133593 270157412675395866993100195)
      ·
        refine ⟨405236119013093800489650293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270157412675395866993100195 405236119013093800489650293)
        ·
          refine ⟨37990886157477543795904715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405236119013093800489650293 37990886157477543795904715)
          ·
            refine ⟨56986329236216315693857073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37990886157477543795904715 56986329236216315693857073)
            ·
              refine ⟨42739746927162236770392805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56986329236216315693857073 42739746927162236770392805)
              ·
                refine ⟨8013702548842919394448651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42739746927162236770392805 8013702548842919394448651)
                ·
                  refine ⟨12020553823264379091672977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013702548842919394448651 12020553823264379091672977)
                  ·
                    refine ⟨9015415367448284318754733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12020553823264379091672977 9015415367448284318754733)
                    ·
                      refine ⟨3380780762793106619533025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015415367448284318754733 3380780762793106619533025)
                      ·
                        rfl

theorem cell23_6584047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_6584047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584047 prefixEnd_6584047 := by exact prefixLift 6584047
  have htrace : WordTrace (prefixWord ++ tailWord_6584047) baseStart_6584047 baseEnd_6584047 := by
    simpa [prefixWord, tailWord_6584047, baseEnd_6584047] using wordTrace_append hprefix tailTrace_6584047
  have hstable : (prefixWord ++ tailWord_6584047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584047).length < 2 ^ (prefixWord ++ tailWord_6584047).sum := by decide
  have hdescent : baseEnd_6584047 < baseStart_6584047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584071 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 2, 4]
def baseStart_6584071 : Nat := 118140960795 + 6584071 * 2 ^ 59
def prefixEnd_6584071 : Nat := 4983230072969 + 3 ^ 40 * 6584071 * 2
def baseEnd_6584071 : Nat := 1126931028776271508544305

theorem tailTrace_6584071 : CollatzResearch.WordTrace tailWord_6584071 prefixEnd_6584071 1126931028776271508544305 := by
  unfold tailWord_6584071
  simp only [CollatzResearch.WordTrace]
  refine ⟨240140797730042711648296067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160093865153361807765530711 240140797730042711648296067)
  ·
    refine ⟨360211196595064067472444101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240140797730042711648296067 360211196595064067472444101)
    ·
      refine ⟨67539599361574512651083269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360211196595064067472444101 67539599361574512651083269)
      ·
        refine ⟨12663674880295221122078113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67539599361574512651083269 12663674880295221122078113)
        ·
          refine ⟨9497756160221415841558585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12663674880295221122078113 9497756160221415841558585)
          ·
            refine ⟨7123317120166061881168939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497756160221415841558585 7123317120166061881168939)
            ·
              refine ⟨10684975680249092821753409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123317120166061881168939 10684975680249092821753409)
              ·
                refine ⟨8013731760186819616315057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10684975680249092821753409 8013731760186819616315057)
                ·
                  refine ⟨6010298820140114712236293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8013731760186819616315057 6010298820140114712236293)
                  ·
                    refine ⟨1126931028776271508544305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010298820140114712236293 1126931028776271508544305)
                    ·
                      rfl

theorem cell23_6584071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_6584071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584071 prefixEnd_6584071 := by exact prefixLift 6584071
  have htrace : WordTrace (prefixWord ++ tailWord_6584071) baseStart_6584071 baseEnd_6584071 := by
    simpa [prefixWord, tailWord_6584071, baseEnd_6584071] using wordTrace_append hprefix tailTrace_6584071
  have hstable : (prefixWord ++ tailWord_6584071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584071).length < 2 ^ (prefixWord ++ tailWord_6584071).sum := by decide
  have hdescent : baseEnd_6584071 < baseStart_6584071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584120 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6584120 : Nat := 118140960795 + 6584120 * 2 ^ 59
def prefixEnd_6584120 : Nat := 4983230072969 + 3 ^ 40 * 6584120 * 2
def baseEnd_6584120 : Nat := 3380818246880884833920189

theorem tailTrace_6584120 : CollatzResearch.WordTrace tailWord_6584120 prefixEnd_6584120 3380818246880884833920189 := by
  unfold tailWord_6584120
  simp only [CollatzResearch.WordTrace]
  refine ⟨120071292453432596508414907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160095056604576795344553209 120071292453432596508414907)
  ·
    refine ⟨180106938680148894762622361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120071292453432596508414907 180106938680148894762622361)
    ·
      refine ⟨135080204010111671071966771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180106938680148894762622361 135080204010111671071966771)
      ·
        refine ⟨202620306015167506607950157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135080204010111671071966771 202620306015167506607950157)
        ·
          refine ⟨75982614755687814977981309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202620306015167506607950157 75982614755687814977981309)
          ·
            refine ⟨28493480533382930616742991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75982614755687814977981309 28493480533382930616742991)
            ·
              refine ⟨42740220800074395925114487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28493480533382930616742991 42740220800074395925114487)
              ·
                refine ⟨64110331200111593887671731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42740220800074395925114487 64110331200111593887671731)
                ·
                  refine ⟨96165496800167390831507597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64110331200111593887671731 96165496800167390831507597)
                  ·
                    refine ⟨36062061300062771561815349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96165496800167390831507597 36062061300062771561815349)
                    ·
                      refine ⟨3380818246880884833920189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36062061300062771561815349 3380818246880884833920189)
                      ·
                        rfl

theorem cell23_6584120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6584120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584120 prefixEnd_6584120 := by exact prefixLift 6584120
  have htrace : WordTrace (prefixWord ++ tailWord_6584120) baseStart_6584120 baseEnd_6584120 := by
    simpa [prefixWord, tailWord_6584120, baseEnd_6584120] using wordTrace_append hprefix tailTrace_6584120
  have hstable : (prefixWord ++ tailWord_6584120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584120).length < 2 ^ (prefixWord ++ tailWord_6584120).sum := by decide
  have hdescent : baseEnd_6584120 < baseStart_6584120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584217 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_6584217 : Nat := 118140960795 + 6584217 * 2 ^ 59
def prefixEnd_6584217 : Nat := 4983230072969 + 3 ^ 40 * 6584217 * 2
def baseEnd_6584217 : Nat := 1126956018168123651469081

theorem tailTrace_6584217 : CollatzResearch.WordTrace tailWord_6584217 prefixEnd_6584217 1126956018168123651469081 := by
  unfold tailWord_6584217
  simp only [CollatzResearch.WordTrace]
  refine ⟨240146122787513778583110905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160097415191675852388740603 240146122787513778583110905)
  ·
    refine ⟨180109592090635333937333179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240146122787513778583110905 180109592090635333937333179)
    ·
      refine ⟨270164388135953000905999769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180109592090635333937333179 270164388135953000905999769)
      ·
        refine ⟨202623291101964750679499827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270164388135953000905999769 202623291101964750679499827)
        ·
          refine ⟨303934936652947126019249741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202623291101964750679499827 303934936652947126019249741)
          ·
            refine ⟨113975601244855172257218653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303934936652947126019249741 113975601244855172257218653)
            ·
              refine ⟨42740850466820689596456995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113975601244855172257218653 42740850466820689596456995)
              ·
                refine ⟨64111275700231034394685493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42740850466820689596456995 64111275700231034394685493)
                ·
                  refine ⟨6010432096896659474501765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64111275700231034394685493 6010432096896659474501765)
                  ·
                    refine ⟨1126956018168123651469081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010432096896659474501765 1126956018168123651469081)
                    ·
                      rfl

theorem cell23_6584217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_6584217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584217 prefixEnd_6584217 := by exact prefixLift 6584217
  have htrace : WordTrace (prefixWord ++ tailWord_6584217) baseStart_6584217 baseEnd_6584217 := by
    simpa [prefixWord, tailWord_6584217, baseEnd_6584217] using wordTrace_append hprefix tailTrace_6584217
  have hstable : (prefixWord ++ tailWord_6584217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584217).length < 2 ^ (prefixWord ++ tailWord_6584217).sum := by decide
  have hdescent : baseEnd_6584217 < baseStart_6584217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584240 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_6584240 : Nat := 118140960795 + 6584240 * 2 ^ 59
def prefixEnd_6584240 : Nat := 4983230072969 + 3 ^ 40 * 6584240 * 2
def baseEnd_6584240 : Nat := 3380879864559424364419637

theorem tailTrace_6584240 : CollatzResearch.WordTrace tailWord_6584240 prefixEnd_6584240 3380879864559424364419637 := by
  unfold tailWord_6584240
  simp only [CollatzResearch.WordTrace]
  refine ⟨120073480833215226755599087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160097974444286969007465449 120073480833215226755599087)
  ·
    refine ⟨180110221249822840133398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120073480833215226755599087 180110221249822840133398631)
    ·
      refine ⟨270165331874734260200097947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180110221249822840133398631 270165331874734260200097947)
      ·
        refine ⟨405247997812101390300146921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270165331874734260200097947 405247997812101390300146921)
        ·
          refine ⟨303935998359076042725110191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405247997812101390300146921 303935998359076042725110191)
          ·
            refine ⟨455903997538614064087665287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303935998359076042725110191 455903997538614064087665287)
            ·
              refine ⟨683855996307921096131497931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455903997538614064087665287 683855996307921096131497931)
              ·
                refine ⟨1025783994461881644197246897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683855996307921096131497931 1025783994461881644197246897)
                ·
                  refine ⟨769337995846411233147935173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1025783994461881644197246897 769337995846411233147935173)
                  ·
                    refine ⟨144250874221202106215237845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 769337995846411233147935173 144250874221202106215237845)
                    ·
                      refine ⟨3380879864559424364419637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144250874221202106215237845 3380879864559424364419637)
                      ·
                        rfl

theorem cell23_6584240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_6584240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584240 prefixEnd_6584240 := by exact prefixLift 6584240
  have htrace : WordTrace (prefixWord ++ tailWord_6584240) baseStart_6584240 baseEnd_6584240 := by
    simpa [prefixWord, tailWord_6584240, baseEnd_6584240] using wordTrace_append hprefix tailTrace_6584240
  have hstable : (prefixWord ++ tailWord_6584240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584240).length < 2 ^ (prefixWord ++ tailWord_6584240).sum := by decide
  have hdescent : baseEnd_6584240 < baseStart_6584240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584285 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6584285 : Nat := 118140960795 + 6584285 * 2 ^ 59
def prefixEnd_6584285 : Nat := 4983230072969 + 3 ^ 40 * 6584285 * 2
def baseEnd_6584285 : Nat := 1126967657062958896118977

theorem tailTrace_6584285 : CollatzResearch.WordTrace tailWord_6584285 prefixEnd_6584285 1126967657062958896118977 := by
  unfold tailWord_6584285
  simp only [CollatzResearch.WordTrace]
  refine ⟨240148602951267426196586309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160099068634178284131057539 240148602951267426196586309)
  ·
    refine ⟨45027863053362642411859933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240148602951267426196586309 45027863053362642411859933)
    ·
      refine ⟨16885448645010990904447475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45027863053362642411859933 16885448645010990904447475)
      ·
        refine ⟨25328172967516486356671213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16885448645010990904447475 25328172967516486356671213)
        ·
          refine ⟨9498064862818682383751705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25328172967516486356671213 9498064862818682383751705)
          ·
            refine ⟨7123548647114011787813779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498064862818682383751705 7123548647114011787813779)
            ·
              refine ⟨10685322970671017681720669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123548647114011787813779 10685322970671017681720669)
              ·
                refine ⟨4006996114001631630645251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10685322970671017681720669 4006996114001631630645251)
                ·
                  refine ⟨6010494171002447445967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006996114001631630645251 6010494171002447445967877)
                  ·
                    refine ⟨1126967657062958896118977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010494171002447445967877 1126967657062958896118977)
                    ·
                      rfl

theorem cell23_6584285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6584285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584285 prefixEnd_6584285 := by exact prefixLift 6584285
  have htrace : WordTrace (prefixWord ++ tailWord_6584285) baseStart_6584285 baseEnd_6584285 := by
    simpa [prefixWord, tailWord_6584285, baseEnd_6584285] using wordTrace_append hprefix tailTrace_6584285
  have hstable : (prefixWord ++ tailWord_6584285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584285).length < 2 ^ (prefixWord ++ tailWord_6584285).sum := by decide
  have hdescent : baseEnd_6584285 < baseStart_6584285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584331 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 5, 2, 2]
def baseStart_6584331 : Nat := 118140960795 + 6584331 * 2 ^ 59
def prefixEnd_6584331 : Nat := 4983230072969 + 3 ^ 40 * 6584331 * 2
def baseEnd_6584331 : Nat := 3380926591298983508381719

theorem tailTrace_6584331 : CollatzResearch.WordTrace tailWord_6584331 prefixEnd_6584331 3380926591298983508381719 := by
  unfold tailWord_6584331
  simp only [CollatzResearch.WordTrace]
  refine ⟨240150280709100776052760847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160100187139400517368507231 240150280709100776052760847)
  ·
    refine ⟨360225421063651164079141271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240150280709100776052760847 360225421063651164079141271)
    ·
      refine ⟨540338131595476746118711907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360225421063651164079141271 540338131595476746118711907)
      ·
        refine ⟨810507197393215119178067861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540338131595476746118711907 810507197393215119178067861)
        ·
          refine ⟨37992524877806958711471931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 810507197393215119178067861 37992524877806958711471931)
          ·
            refine ⟨56988787316710438067207897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37992524877806958711471931 56988787316710438067207897)
            ·
              refine ⟨42741590487532828550405923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56988787316710438067207897 42741590487532828550405923)
              ·
                refine ⟨64112385731299242825608885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42741590487532828550405923 64112385731299242825608885)
                ·
                  refine ⟨6010536162309304014900833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64112385731299242825608885 6010536162309304014900833)
                  ·
                    refine ⟨4507902121731978011175625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6010536162309304014900833 4507902121731978011175625)
                    ·
                      refine ⟨3380926591298983508381719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507902121731978011175625 3380926591298983508381719)
                      ·
                        rfl

theorem cell23_6584331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2, 2].length) (baseStart_6584331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584331 prefixEnd_6584331 := by exact prefixLift 6584331
  have htrace : WordTrace (prefixWord ++ tailWord_6584331) baseStart_6584331 baseEnd_6584331 := by
    simpa [prefixWord, tailWord_6584331, baseEnd_6584331] using wordTrace_append hprefix tailTrace_6584331
  have hstable : (prefixWord ++ tailWord_6584331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584331).length < 2 ^ (prefixWord ++ tailWord_6584331).sum := by decide
  have hdescent : baseEnd_6584331 < baseStart_6584331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584344 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6584344 : Nat := 118140960795 + 6584344 * 2 ^ 59
def prefixEnd_6584344 : Nat := 4983230072969 + 3 ^ 40 * 6584344 * 2
def baseEnd_6584344 : Nat := 3380933266547491957519159

theorem tailTrace_6584344 : CollatzResearch.WordTrace tailWord_6584344 prefixEnd_6584344 3380933266547491957519159 := by
  unfold tailWord_6584344
  simp only [CollatzResearch.WordTrace]
  refine ⟨120075377429026839636492043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160100503238702452848656057 120075377429026839636492043)
  ·
    refine ⟨180113066143540259454738065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120075377429026839636492043 180113066143540259454738065)
    ·
      refine ⟨135084799607655194591053549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180113066143540259454738065 135084799607655194591053549)
      ·
        refine ⟨50656799852870697971645081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135084799607655194591053549 50656799852870697971645081)
        ·
          refine ⟨37992599889653023478733811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50656799852870697971645081 37992599889653023478733811)
          ·
            refine ⟨56988899834479535218100717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37992599889653023478733811 56988899834479535218100717)
            ·
              refine ⟨21370837437929825706787769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56988899834479535218100717 21370837437929825706787769)
              ·
                refine ⟨16028128078447369280090827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21370837437929825706787769 16028128078447369280090827)
                ·
                  refine ⟨24042192117671053920136241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028128078447369280090827 24042192117671053920136241)
                  ·
                    refine ⟨18031644088253290440102181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24042192117671053920136241 18031644088253290440102181)
                    ·
                      refine ⟨3380933266547491957519159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18031644088253290440102181 3380933266547491957519159)
                      ·
                        rfl

theorem cell23_6584344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6584344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584344 prefixEnd_6584344 := by exact prefixLift 6584344
  have htrace : WordTrace (prefixWord ++ tailWord_6584344) baseStart_6584344 baseEnd_6584344 := by
    simpa [prefixWord, tailWord_6584344, baseEnd_6584344] using wordTrace_append hprefix tailTrace_6584344
  have hstable : (prefixWord ++ tailWord_6584344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584344).length < 2 ^ (prefixWord ++ tailWord_6584344).sum := by decide
  have hdescent : baseEnd_6584344 < baseStart_6584344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584348 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6584348 : Nat := 118140960795 + 6584348 * 2 ^ 59
def prefixEnd_6584348 : Nat := 4983230072969 + 3 ^ 40 * 6584348 * 2
def baseEnd_6584348 : Nat := 3380935320470109941869141

theorem tailTrace_6584348 : CollatzResearch.WordTrace tailWord_6584348 prefixEnd_6584348 3380935320470109941869141 := by
  unfold tailWord_6584348
  simp only [CollatzResearch.WordTrace]
  refine ⟨120075450375019593978064849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160100600500026125304086465 120075450375019593978064849)
  ·
    refine ⟨90056587781264695483548637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120075450375019593978064849 90056587781264695483548637)
    ·
      refine ⟨33771220417974260806330739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90056587781264695483548637 33771220417974260806330739)
      ·
        refine ⟨50656830626961391209496109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33771220417974260806330739 50656830626961391209496109)
        ·
          refine ⟨18996311485110521703561041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50656830626961391209496109 18996311485110521703561041)
          ·
            refine ⟨14247233613832891277670781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18996311485110521703561041 14247233613832891277670781)
            ·
              refine ⟨5342712605187334229126543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14247233613832891277670781 5342712605187334229126543)
              ·
                refine ⟨8014068907781001343689815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342712605187334229126543 8014068907781001343689815)
                ·
                  refine ⟨12021103361671502015534723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014068907781001343689815 12021103361671502015534723)
                  ·
                    refine ⟨18031655042507253023302085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12021103361671502015534723 18031655042507253023302085)
                    ·
                      refine ⟨3380935320470109941869141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18031655042507253023302085 3380935320470109941869141)
                      ·
                        rfl

theorem cell23_6584348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6584348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584348 prefixEnd_6584348 := by exact prefixLift 6584348
  have htrace : WordTrace (prefixWord ++ tailWord_6584348) baseStart_6584348 baseEnd_6584348 := by
    simpa [prefixWord, tailWord_6584348, baseEnd_6584348] using wordTrace_append hprefix tailTrace_6584348
  have hstable : (prefixWord ++ tailWord_6584348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584348).length < 2 ^ (prefixWord ++ tailWord_6584348).sum := by decide
  have hdescent : baseEnd_6584348 < baseStart_6584348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584359 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6584359 : Nat := 118140960795 + 6584359 * 2 ^ 59
def prefixEnd_6584359 : Nat := 4983230072969 + 3 ^ 40 * 6584359 * 2
def baseEnd_6584359 : Nat := 3380940968757309398831591

theorem tailTrace_6584359 : CollatzResearch.WordTrace tailWord_6584359 prefixEnd_6584359 3380940968757309398831591 := by
  unfold tailWord_6584359
  simp only [CollatzResearch.WordTrace]
  refine ⟨240151301952999336834780131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160100867968666224556520087 240151301952999336834780131)
  ·
    refine ⟨360226952929499005252170197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240151301952999336834780131 360226952929499005252170197)
    ·
      refine ⟨8442819209285132935597739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 360226952929499005252170197 8442819209285132935597739)
      ·
        refine ⟨12664228813927699403396609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442819209285132935597739 12664228813927699403396609)
        ·
          refine ⟨9498171610445774552547457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12664228813927699403396609 9498171610445774552547457)
          ·
            refine ⟨7123628707834330914410593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498171610445774552547457 7123628707834330914410593)
            ·
              refine ⟨5342721530875748185807945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123628707834330914410593 5342721530875748185807945)
              ·
                refine ⟨4007041148156811139355959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5342721530875748185807945 4007041148156811139355959)
                ·
                  refine ⟨6010561722235216709033939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007041148156811139355959 6010561722235216709033939)
                  ·
                    refine ⟨9015842583352825063550909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6010561722235216709033939 9015842583352825063550909)
                    ·
                      refine ⟨3380940968757309398831591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015842583352825063550909 3380940968757309398831591)
                      ·
                        rfl

theorem cell23_6584359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6584359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584359 prefixEnd_6584359 := by exact prefixLift 6584359
  have htrace : WordTrace (prefixWord ++ tailWord_6584359) baseStart_6584359 baseEnd_6584359 := by
    simpa [prefixWord, tailWord_6584359, baseEnd_6584359] using wordTrace_append hprefix tailTrace_6584359
  have hstable : (prefixWord ++ tailWord_6584359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584359).length < 2 ^ (prefixWord ++ tailWord_6584359).sum := by decide
  have hdescent : baseEnd_6584359 < baseStart_6584359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584381 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6584381 : Nat := 118140960795 + 6584381 * 2 ^ 59
def prefixEnd_6584381 : Nat := 4983230072969 + 3 ^ 40 * 6584381 * 2
def baseEnd_6584381 : Nat := 3380952265331708312756489

theorem tailTrace_6584381 : CollatzResearch.WordTrace tailWord_6584381 prefixEnd_6584381 3380952265331708312756489 := by
  unfold tailWord_6584381
  simp only [CollatzResearch.WordTrace]
  refine ⟨240152104358919634592080997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160101402905946423061387331 240152104358919634592080997)
  ·
    refine ⟨45028519567297431486015187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240152104358919634592080997 45028519567297431486015187)
    ·
      refine ⟨67542779350946147229022781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45028519567297431486015187 67542779350946147229022781)
      ·
        refine ⟨25328542256604805210883543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67542779350946147229022781 25328542256604805210883543)
        ·
          refine ⟨37992813384907207816325315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25328542256604805210883543 37992813384907207816325315)
          ·
            refine ⟨56989220077360811724487973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37992813384907207816325315 56989220077360811724487973)
            ·
              refine ⟨10685478764505152198341495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56989220077360811724487973 10685478764505152198341495)
              ·
                refine ⟨16028218146757728297512243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685478764505152198341495 16028218146757728297512243)
                ·
                  refine ⟨24042327220136592446268365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028218146757728297512243 24042327220136592446268365)
                  ·
                    refine ⟨9015872707551222167350637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24042327220136592446268365 9015872707551222167350637)
                    ·
                      refine ⟨3380952265331708312756489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015872707551222167350637 3380952265331708312756489)
                      ·
                        rfl

theorem cell23_6584381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6584381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584381 prefixEnd_6584381 := by exact prefixLift 6584381
  have htrace : WordTrace (prefixWord ++ tailWord_6584381) baseStart_6584381 baseEnd_6584381 := by
    simpa [prefixWord, tailWord_6584381, baseEnd_6584381] using wordTrace_append hprefix tailTrace_6584381
  have hstable : (prefixWord ++ tailWord_6584381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584381).length < 2 ^ (prefixWord ++ tailWord_6584381).sum := by decide
  have hdescent : baseEnd_6584381 < baseStart_6584381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584391 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_6584391 : Nat := 118140960795 + 6584391 * 2 ^ 59
def prefixEnd_6584391 : Nat := 4983230072969 + 3 ^ 40 * 6584391 * 2
def baseEnd_6584391 : Nat := 3380957400138253273631443

theorem tailTrace_6584391 : CollatzResearch.WordTrace tailWord_6584391 prefixEnd_6584391 3380957400138253273631443 := by
  unfold tailWord_6584391
  simp only [CollatzResearch.WordTrace]
  refine ⟨240152469088883406299945027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160101646059255604199963351 240152469088883406299945027)
  ·
    refine ⟨360228703633325109449917541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240152469088883406299945027 360228703633325109449917541)
    ·
      refine ⟨67542881931248458021859539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360228703633325109449917541 67542881931248458021859539)
      ·
        refine ⟨101314322896872687032789309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67542881931248458021859539 101314322896872687032789309)
        ·
          refine ⟨37992871086327257637295991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101314322896872687032789309 37992871086327257637295991)
          ·
            refine ⟨56989306629490886455943987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37992871086327257637295991 56989306629490886455943987)
            ·
              refine ⟨85483959944236329683915981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56989306629490886455943987 85483959944236329683915981)
              ·
                refine ⟨32056484979088623631468493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85483959944236329683915981 32056484979088623631468493)
                ·
                  refine ⟨12021181867158233861800685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32056484979088623631468493 12021181867158233861800685)
                  ·
                    refine ⟨4507943200184337698175257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12021181867158233861800685 4507943200184337698175257)
                    ·
                      refine ⟨3380957400138253273631443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507943200184337698175257 3380957400138253273631443)
                      ·
                        rfl

theorem cell23_6584391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_6584391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584391 prefixEnd_6584391 := by exact prefixLift 6584391
  have htrace : WordTrace (prefixWord ++ tailWord_6584391) baseStart_6584391 baseEnd_6584391 := by
    simpa [prefixWord, tailWord_6584391, baseEnd_6584391] using wordTrace_append hprefix tailTrace_6584391
  have hstable : (prefixWord ++ tailWord_6584391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584391).length < 2 ^ (prefixWord ++ tailWord_6584391).sum := by decide
  have hdescent : baseEnd_6584391 < baseStart_6584391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584402 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_6584402 : Nat := 118140960795 + 6584402 * 2 ^ 59
def prefixEnd_6584402 : Nat := 4983230072969 + 3 ^ 40 * 6584402 * 2
def baseEnd_6584402 : Nat := 3380963048425452730593893

theorem tailTrace_6584402 : CollatzResearch.WordTrace tailWord_6584402 prefixEnd_6584402 3380963048425452730593893 := by
  unfold tailWord_6584402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60038217572960888794648865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160101913527895703452396973 60038217572960888794648865)
  ·
    refine ⟨45028663179720666595986649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60038217572960888794648865 45028663179720666595986649)
    ·
      refine ⟨33771497384790499946989987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45028663179720666595986649 33771497384790499946989987)
      ·
        refine ⟨50657246077185749920484981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33771497384790499946989987 50657246077185749920484981)
        ·
          refine ⟨4749116819736164055045467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50657246077185749920484981 4749116819736164055045467)
          ·
            refine ⟨7123675229604246082568201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749116819736164055045467 7123675229604246082568201)
            ·
              refine ⟨5342756422203184561926151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123675229604246082568201 5342756422203184561926151)
              ·
                refine ⟨8014134633304776842889227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342756422203184561926151 8014134633304776842889227)
                ·
                  refine ⟨12021201949957165264333841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014134633304776842889227 12021201949957165264333841)
                  ·
                    refine ⟨9015901462467873948250381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12021201949957165264333841 9015901462467873948250381)
                    ·
                      refine ⟨3380963048425452730593893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9015901462467873948250381 3380963048425452730593893)
                      ·
                        rfl

theorem cell23_6584402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_6584402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584402 prefixEnd_6584402 := by exact prefixLift 6584402
  have htrace : WordTrace (prefixWord ++ tailWord_6584402) baseStart_6584402 baseEnd_6584402 := by
    simpa [prefixWord, tailWord_6584402, baseEnd_6584402] using wordTrace_append hprefix tailTrace_6584402
  have hstable : (prefixWord ++ tailWord_6584402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584402).length < 2 ^ (prefixWord ++ tailWord_6584402).sum := by decide
  have hdescent : baseEnd_6584402 < baseStart_6584402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584408 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_6584408 : Nat := 118140960795 + 6584408 * 2 ^ 59
def prefixEnd_6584408 : Nat := 4983230072969 + 3 ^ 40 * 6584408 * 2
def baseEnd_6584408 : Nat := 3380966129309379707118865

theorem tailTrace_6584408 : CollatzResearch.WordTrace tailWord_6584408 prefixEnd_6584408 3380966129309379707118865 := by
  unfold tailWord_6584408
  simp only [CollatzResearch.WordTrace]
  refine ⟨120076544564910909101656939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160102059419881212135542585 120076544564910909101656939)
  ·
    refine ⟨180114816847366363652485409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120076544564910909101656939 180114816847366363652485409)
    ·
      refine ⟨135086112635524772739364057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180114816847366363652485409 135086112635524772739364057)
      ·
        refine ⟨101314584476643579554523043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135086112635524772739364057 101314584476643579554523043)
        ·
          refine ⟨151971876714965369331784565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101314584476643579554523043 151971876714965369331784565)
          ·
            refine ⟨14247363442028003374854803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151971876714965369331784565 14247363442028003374854803)
            ·
              refine ⟨21371045163042005062282205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14247363442028003374854803 21371045163042005062282205)
              ·
                refine ⟨8014141936140751898355827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21371045163042005062282205 8014141936140751898355827)
                ·
                  refine ⟨12021212904211127847533741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014141936140751898355827 12021212904211127847533741)
                  ·
                    refine ⟨4507954839079172942825153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12021212904211127847533741 4507954839079172942825153)
                    ·
                      refine ⟨3380966129309379707118865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4507954839079172942825153 3380966129309379707118865)
                      ·
                        rfl

theorem cell23_6584408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_6584408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584408 prefixEnd_6584408 := by exact prefixLift 6584408
  have htrace : WordTrace (prefixWord ++ tailWord_6584408) baseStart_6584408 baseEnd_6584408 := by
    simpa [prefixWord, tailWord_6584408, baseEnd_6584408] using wordTrace_append hprefix tailTrace_6584408
  have hstable : (prefixWord ++ tailWord_6584408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584408).length < 2 ^ (prefixWord ++ tailWord_6584408).sum := by decide
  have hdescent : baseEnd_6584408 < baseStart_6584408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584444 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 7]
def baseStart_6584444 : Nat := 118140960795 + 6584444 * 2 ^ 59
def prefixEnd_6584444 : Nat := 4983230072969 + 3 ^ 40 * 6584444 * 2
def baseEnd_6584444 : Nat := 375664957179215729585411

theorem tailTrace_6584444 : CollatzResearch.WordTrace tailWord_6584444 prefixEnd_6584444 375664957179215729585411 := by
  unfold tailWord_6584444
  simp only [CollatzResearch.WordTrace]
  refine ⟨120077201078845698175812193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160102934771794264234416257 120077201078845698175812193)
  ·
    refine ⟨90057900809134273631859145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120077201078845698175812193 90057900809134273631859145)
    ·
      refine ⟨67543425606850705223894359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90057900809134273631859145 67543425606850705223894359)
      ·
        refine ⟨101315138410276057835841539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67543425606850705223894359 101315138410276057835841539)
        ·
          refine ⟨151972707615414086753762309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101315138410276057835841539 151972707615414086753762309)
          ·
            refine ⟨28494882677890141266330433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151972707615414086753762309 28494882677890141266330433)
            ·
              refine ⟨21371162008417605949747825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28494882677890141266330433 21371162008417605949747825)
              ·
                refine ⟨16028371506313204462310869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21371162008417605949747825 16028371506313204462310869)
                ·
                  refine ⟨375664957179215729585411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16028371506313204462310869 375664957179215729585411)
                  ·
                    rfl

theorem cell23_6584444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_6584444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584444 prefixEnd_6584444 := by exact prefixLift 6584444
  have htrace : WordTrace (prefixWord ++ tailWord_6584444) baseStart_6584444 baseEnd_6584444 := by
    simpa [prefixWord, tailWord_6584444, baseEnd_6584444] using wordTrace_append hprefix tailTrace_6584444
  have hstable : (prefixWord ++ tailWord_6584444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584444).length < 2 ^ (prefixWord ++ tailWord_6584444).sum := by decide
  have hdescent : baseEnd_6584444 < baseStart_6584444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584508 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_6584508 : Nat := 118140960795 + 6584508 * 2 ^ 59
def prefixEnd_6584508 : Nat := 4983230072969 + 3 ^ 40 * 6584508 * 2
def baseEnd_6584508 : Nat := 1127005825791609771956135

theorem tailTrace_6584508 : CollatzResearch.WordTrace tailWord_6584508 prefixEnd_6584508 1127005825791609771956135 := by
  unfold tailWord_6584508
  simp only [CollatzResearch.WordTrace]
  refine ⟨120078368214729767640977089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160104490952973023521302785 120078368214729767640977089)
  ·
    refine ⟨90058776161047325730732817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120078368214729767640977089 90058776161047325730732817)
    ·
      refine ⟨67544082120785494298049613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90058776161047325730732817 67544082120785494298049613)
      ·
        refine ⟨25329030795294560361768605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67544082120785494298049613 25329030795294560361768605)
        ·
          refine ⟨9498386548235460135663227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25329030795294560361768605 9498386548235460135663227)
          ·
            refine ⟨14247579822353190203494841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498386548235460135663227 14247579822353190203494841)
            ·
              refine ⟨10685684866764892652621131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247579822353190203494841 10685684866764892652621131)
              ·
                refine ⟨16028527300147338978931697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685684866764892652621131 16028527300147338978931697)
                ·
                  refine ⟨12021395475110504234198773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16028527300147338978931697 12021395475110504234198773)
                  ·
                    refine ⟨1127005825791609771956135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12021395475110504234198773 1127005825791609771956135)
                    ·
                      rfl

theorem cell23_6584508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_6584508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584508 prefixEnd_6584508 := by exact prefixLift 6584508
  have htrace : WordTrace (prefixWord ++ tailWord_6584508) baseStart_6584508 baseEnd_6584508 := by
    simpa [prefixWord, tailWord_6584508, baseEnd_6584508] using wordTrace_append hprefix tailTrace_6584508
  have hstable : (prefixWord ++ tailWord_6584508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584508).length < 2 ^ (prefixWord ++ tailWord_6584508).sum := by decide
  have hdescent : baseEnd_6584508 < baseStart_6584508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 4, 2]
def baseStart_6584511 : Nat := 118140960795 + 6584511 * 2 ^ 59
def prefixEnd_6584511 : Nat := 4983230072969 + 3 ^ 40 * 6584511 * 2
def baseEnd_6584511 : Nat := 3381019017816792804130891

theorem tailTrace_6584511 : CollatzResearch.WordTrace tailWord_6584511 prefixEnd_6584511 3381019017816792804130891 := by
  unfold tailWord_6584511
  simp only [CollatzResearch.WordTrace]
  refine ⟨240156845848448666794313387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160104563898965777862875591 240156845848448666794313387)
  ·
    refine ⟨360235268772673000191470081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240156845848448666794313387 360235268772673000191470081)
    ·
      refine ⟨270176451579504750143602561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360235268772673000191470081 270176451579504750143602561)
      ·
        refine ⟨202632338684628562607701921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270176451579504750143602561 202632338684628562607701921)
        ·
          refine ⟨151974254013471421955776441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202632338684628562607701921 151974254013471421955776441)
          ·
            refine ⟨113980690510103566466832331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151974254013471421955776441 113980690510103566466832331)
            ·
              refine ⟨170971035765155349700248497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113980690510103566466832331 170971035765155349700248497)
              ·
                refine ⟨128228276823866512275186373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170971035765155349700248497 128228276823866512275186373)
                ·
                  refine ⟨24042801904474971051597445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128228276823866512275186373 24042801904474971051597445)
                  ·
                    refine ⟨4508025357089057072174521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24042801904474971051597445 4508025357089057072174521)
                    ·
                      refine ⟨3381019017816792804130891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508025357089057072174521 3381019017816792804130891)
                      ·
                        rfl

theorem cell23_6584511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_6584511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584511 prefixEnd_6584511 := by exact prefixLift 6584511
  have htrace : WordTrace (prefixWord ++ tailWord_6584511) baseStart_6584511 baseEnd_6584511 := by
    simpa [prefixWord, tailWord_6584511, baseEnd_6584511] using wordTrace_append hprefix tailTrace_6584511
  have hstable : (prefixWord ++ tailWord_6584511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584511).length < 2 ^ (prefixWord ++ tailWord_6584511).sum := by decide
  have hdescent : baseEnd_6584511 < baseStart_6584511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584588 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_6584588 : Nat := 118140960795 + 6584588 * 2 ^ 59
def prefixEnd_6584588 : Nat := 4983230072969 + 3 ^ 40 * 6584588 * 2
def baseEnd_6584588 : Nat := 3381058555827189002868037

theorem tailTrace_6584588 : CollatzResearch.WordTrace tailWord_6584588 prefixEnd_6584588 3381058555827189002868037 := by
  unfold tailWord_6584588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120079827134584854472433209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160106436179446472629910945 120079827134584854472433209)
  ·
    refine ⟨90059870350938640854324907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120079827134584854472433209 90059870350938640854324907)
    ·
      refine ⟨135089805526407961281487361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90059870350938640854324907 135089805526407961281487361)
      ·
        refine ⟨101317354144805970961115521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135089805526407961281487361 101317354144805970961115521)
        ·
          refine ⟨75988015608604478220836641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101317354144805970961115521 75988015608604478220836641)
          ·
            refine ⟨56991011706453358665627481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75988015608604478220836641 56991011706453358665627481)
            ·
              refine ⟨42743258779840018999220611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56991011706453358665627481 42743258779840018999220611)
              ·
                refine ⟨64114888169760028498830917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42743258779840018999220611 64114888169760028498830917)
                ·
                  refine ⟨12021541531830005343530797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64114888169760028498830917 12021541531830005343530797)
                  ·
                    refine ⟨4508078074436252003824049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12021541531830005343530797 4508078074436252003824049)
                    ·
                      refine ⟨3381058555827189002868037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508078074436252003824049 3381058555827189002868037)
                      ·
                        rfl

theorem cell23_6584588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_6584588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584588 prefixEnd_6584588 := by exact prefixLift 6584588
  have htrace : WordTrace (prefixWord ++ tailWord_6584588) baseStart_6584588 baseEnd_6584588 := by
    simpa [prefixWord, tailWord_6584588, baseEnd_6584588] using wordTrace_append hprefix tailTrace_6584588
  have hstable : (prefixWord ++ tailWord_6584588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584588).length < 2 ^ (prefixWord ++ tailWord_6584588).sum := by decide
  have hdescent : baseEnd_6584588 < baseStart_6584588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584631 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_6584631 : Nat := 118140960795 + 6584631 * 2 ^ 59
def prefixEnd_6584631 : Nat := 4983230072969 + 3 ^ 40 * 6584631 * 2
def baseEnd_6584631 : Nat := 3381080635495332334630339

theorem tailTrace_6584631 : CollatzResearch.WordTrace tailWord_6584631 prefixEnd_6584631 3381080635495332334630339 := by
  unfold tailWord_6584631
  simp only [CollatzResearch.WordTrace]
  refine ⟨240161222608013927288681747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160107481738675951525787831 240161222608013927288681747)
  ·
    refine ⟨360241833912020890933022621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240161222608013927288681747 360241833912020890933022621)
    ·
      refine ⟨135090687717007834099883483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360241833912020890933022621 135090687717007834099883483)
      ·
        refine ⟨202636031575511751149825225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135090687717007834099883483 202636031575511751149825225)
        ·
          refine ⟨151977023681633813362368919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202636031575511751149825225 151977023681633813362368919)
          ·
            refine ⟨227965535522450720043553379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151977023681633813362368919 227965535522450720043553379)
            ·
              refine ⟨341948303283676080065330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227965535522450720043553379 341948303283676080065330069)
              ·
                refine ⟨16028826716422316253062347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341948303283676080065330069 16028826716422316253062347)
                ·
                  refine ⟨24043240074633474379593521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028826716422316253062347 24043240074633474379593521)
                  ·
                    refine ⟨18032430055975105784695141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24043240074633474379593521 18032430055975105784695141)
                    ·
                      refine ⟨3381080635495332334630339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18032430055975105784695141 3381080635495332334630339)
                      ·
                        rfl

theorem cell23_6584631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_6584631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584631 prefixEnd_6584631 := by exact prefixLift 6584631
  have htrace : WordTrace (prefixWord ++ tailWord_6584631) baseStart_6584631 baseEnd_6584631 := by
    simpa [prefixWord, tailWord_6584631, baseEnd_6584631] using wordTrace_append hprefix tailTrace_6584631
  have hstable : (prefixWord ++ tailWord_6584631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584631).length < 2 ^ (prefixWord ++ tailWord_6584631).sum := by decide
  have hdescent : baseEnd_6584631 < baseStart_6584631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584638 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6584638 : Nat := 118140960795 + 6584638 * 2 ^ 59
def prefixEnd_6584638 : Nat := 4983230072969 + 3 ^ 40 * 6584638 * 2
def baseEnd_6584638 : Nat := 3381084229859913807242807

theorem tailTrace_6584638 : CollatzResearch.WordTrace tailWord_6584638 prefixEnd_6584638 3381084229859913807242807 := by
  unfold tailWord_6584638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020184739873570935523321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160107651945992378322791045 30020184739873570935523321)
  ·
    refine ⟨22515138554905178201642491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30020184739873570935523321 22515138554905178201642491)
    ·
      refine ⟨33772707832357767302463737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515138554905178201642491 33772707832357767302463737)
      ·
        refine ⟨25329530874268325476847803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33772707832357767302463737 25329530874268325476847803)
        ·
          refine ⟨37994296311402488215271705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25329530874268325476847803 37994296311402488215271705)
          ·
            refine ⟨28495722233551866161453779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37994296311402488215271705 28495722233551866161453779)
            ·
              refine ⟨42743583350327799242180669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28495722233551866161453779 42743583350327799242180669)
              ·
                refine ⟨16028843756372924715817751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42743583350327799242180669 16028843756372924715817751)
                ·
                  refine ⟨24043265634559387073726627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028843756372924715817751 24043265634559387073726627)
                  ·
                    refine ⟨36064898451839080610589941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24043265634559387073726627 36064898451839080610589941)
                    ·
                      refine ⟨3381084229859913807242807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36064898451839080610589941 3381084229859913807242807)
                      ·
                        rfl

theorem cell23_6584638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6584638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584638 prefixEnd_6584638 := by exact prefixLift 6584638
  have htrace : WordTrace (prefixWord ++ tailWord_6584638) baseStart_6584638 baseEnd_6584638 := by
    simpa [prefixWord, tailWord_6584638, baseEnd_6584638] using wordTrace_append hprefix tailTrace_6584638
  have hstable : (prefixWord ++ tailWord_6584638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584638).length < 2 ^ (prefixWord ++ tailWord_6584638).sum := by decide
  have hdescent : baseEnd_6584638 < baseStart_6584638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3]
def baseStart_6584651 : Nat := 118140960795 + 6584651 * 2 ^ 59
def prefixEnd_6584651 : Nat := 4983230072969 + 3 ^ 40 * 6584651 * 2
def baseEnd_6584651 : Nat := 3381090905108422256380247

theorem tailTrace_6584651 : CollatzResearch.WordTrace tailWord_6584651 prefixEnd_6584651 3381090905108422256380247 := by
  unfold tailWord_6584651
  simp only [CollatzResearch.WordTrace]
  refine ⟨240161952067941470704409807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160107968045294313802939871 240161952067941470704409807)
  ·
    refine ⟨360242928101912206056614711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240161952067941470704409807 360242928101912206056614711)
    ·
      refine ⟨540364392152868309084922067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360242928101912206056614711 540364392152868309084922067)
      ·
        refine ⟨810546588229302463627383101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540364392152868309084922067 810546588229302463627383101)
        ·
          refine ⟨303954970585988423860268663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 810546588229302463627383101 303954970585988423860268663)
          ·
            refine ⟨455932455878982635790402995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303954970585988423860268663 455932455878982635790402995)
            ·
              refine ⟨683898683818473953685604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455932455878982635790402995 683898683818473953685604493)
              ·
                refine ⟨256462006431927732632101685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 683898683818473953685604493 256462006431927732632101685)
                ·
                  refine ⟨24043313102993224934259533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256462006431927732632101685 24043313102993224934259533)
                  ·
                    refine ⟨9016242413622459350347325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24043313102993224934259533 9016242413622459350347325)
                    ·
                      refine ⟨3381090905108422256380247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9016242413622459350347325 3381090905108422256380247)
                      ·
                        rfl

theorem cell23_6584651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].length) (baseStart_6584651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584651 prefixEnd_6584651 := by exact prefixLift 6584651
  have htrace : WordTrace (prefixWord ++ tailWord_6584651) baseStart_6584651 baseEnd_6584651 := by
    simpa [prefixWord, tailWord_6584651, baseEnd_6584651] using wordTrace_append hprefix tailTrace_6584651
  have hstable : (prefixWord ++ tailWord_6584651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584651).length < 2 ^ (prefixWord ++ tailWord_6584651).sum := by decide
  have hdescent : baseEnd_6584651 < baseStart_6584651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584672 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_6584672 : Nat := 118140960795 + 6584672 * 2 ^ 59
def prefixEnd_6584672 : Nat := 4983230072969 + 3 ^ 40 * 6584672 * 2
def baseEnd_6584672 : Nat := 3381101688202166674217651

theorem tailTrace_6584672 : CollatzResearch.WordTrace tailWord_6584672 prefixEnd_6584672 3381101688202166674217651 := by
  unfold tailWord_6584672
  simp only [CollatzResearch.WordTrace]
  refine ⟨120081359000432695645462135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160108478667243594193949513 120081359000432695645462135)
  ·
    refine ⟨180122038500649043468193203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120081359000432695645462135 180122038500649043468193203)
    ·
      refine ⟨270183057750973565202289805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180122038500649043468193203 270183057750973565202289805)
      ·
        refine ⟨101318646656615086950858677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270183057750973565202289805 101318646656615086950858677)
        ·
          refine ⟨9498623124057664401643001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101318646656615086950858677 9498623124057664401643001)
          ·
            refine ⟨7123967343043248301232251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498623124057664401643001 7123967343043248301232251)
            ·
              refine ⟨10685951014564872451848377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123967343043248301232251 10685951014564872451848377)
              ·
                refine ⟨8014463260923654338886283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10685951014564872451848377 8014463260923654338886283)
                ·
                  refine ⟨12021694891385481508329425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014463260923654338886283 12021694891385481508329425)
                  ·
                    refine ⟨9016271168539111131247069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12021694891385481508329425 9016271168539111131247069)
                    ·
                      refine ⟨3381101688202166674217651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9016271168539111131247069 3381101688202166674217651)
                      ·
                        rfl

theorem cell23_6584672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_6584672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584672 prefixEnd_6584672 := by exact prefixLift 6584672
  have htrace : WordTrace (prefixWord ++ tailWord_6584672) baseStart_6584672 baseEnd_6584672 := by
    simpa [prefixWord, tailWord_6584672, baseEnd_6584672] using wordTrace_append hprefix tailTrace_6584672
  have hstable : (prefixWord ++ tailWord_6584672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584672).length < 2 ^ (prefixWord ++ tailWord_6584672).sum := by decide
  have hdescent : baseEnd_6584672 < baseStart_6584672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584718 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_6584718 : Nat := 118140960795 + 6584718 * 2 ^ 59
def prefixEnd_6584718 : Nat := 4983230072969 + 3 ^ 40 * 6584718 * 2
def baseEnd_6584718 : Nat := 1127041769437424498080813

theorem tailTrace_6584718 : CollatzResearch.WordTrace tailWord_6584718 prefixEnd_6584718 1127041769437424498080813 := by
  unfold tailWord_6584718
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020549469837342643387351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160109597172465827431399205 30020549469837342643387351)
  ·
    refine ⟨45030824204756013965081027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30020549469837342643387351 45030824204756013965081027)
    ·
      refine ⟨67546236307134020947621541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45030824204756013965081027 67546236307134020947621541)
      ·
        refine ⟨12664919307587628927679039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67546236307134020947621541 12664919307587628927679039)
        ·
          refine ⟨18997378961381443391518559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664919307587628927679039 18997378961381443391518559)
          ·
            refine ⟨28496068442072165087277839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18997378961381443391518559 28496068442072165087277839)
            ·
              refine ⟨42744102663108247630916759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28496068442072165087277839 42744102663108247630916759)
              ·
                refine ⟨64116153994662371446375139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42744102663108247630916759 64116153994662371446375139)
                ·
                  refine ⟨96174230991993557169562709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64116153994662371446375139 96174230991993557169562709)
                  ·
                    refine ⟨1127041769437424498080813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96174230991993557169562709 1127041769437424498080813)
                    ·
                      rfl

theorem cell23_6584718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_6584718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584718 prefixEnd_6584718 := by exact prefixLift 6584718
  have htrace : WordTrace (prefixWord ++ tailWord_6584718) baseStart_6584718 baseEnd_6584718 := by
    simpa [prefixWord, tailWord_6584718, baseEnd_6584718] using wordTrace_append hprefix tailTrace_6584718
  have hstable : (prefixWord ++ tailWord_6584718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584718).length < 2 ^ (prefixWord ++ tailWord_6584718).sum := by decide
  have hdescent : baseEnd_6584718 < baseStart_6584718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584725 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_6584725 : Nat := 118140960795 + 6584725 * 2 ^ 59
def prefixEnd_6584725 : Nat := 4983230072969 + 3 ^ 40 * 6584725 * 2
def baseEnd_6584725 : Nat := 3381128902676854966854907

theorem tailTrace_6584725 : CollatzResearch.WordTrace tailWord_6584725 prefixEnd_6584725 3381128902676854966854907 := by
  unfold tailWord_6584725
  simp only [CollatzResearch.WordTrace]
  refine ⟨240164651069673381342603629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160109767379782254228402419 240164651069673381342603629)
  ·
    refine ⟨90061744151127518003476361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240164651069673381342603629 90061744151127518003476361)
    ·
      refine ⟨67546308113345638502607271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90061744151127518003476361 67546308113345638502607271)
      ·
        refine ⟨101319462170018457753910907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67546308113345638502607271 101319462170018457753910907)
        ·
          refine ⟨151979193255027686630866361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101319462170018457753910907 151979193255027686630866361)
          ·
            refine ⟨113984394941270764973149771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151979193255027686630866361 113984394941270764973149771)
            ·
              refine ⟨170976592411906147459724657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113984394941270764973149771 170976592411906147459724657)
              ·
                refine ⟨128232444308929610594793493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170976592411906147459724657 128232444308929610594793493)
                ·
                  refine ⟨6010895826981075496630945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128232444308929610594793493 6010895826981075496630945)
                  ·
                    refine ⟨4508171870235806622473209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6010895826981075496630945 4508171870235806622473209)
                    ·
                      refine ⟨3381128902676854966854907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508171870235806622473209 3381128902676854966854907)
                      ·
                        rfl

theorem cell23_6584725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_6584725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584725 prefixEnd_6584725 := by exact prefixLift 6584725
  have htrace : WordTrace (prefixWord ++ tailWord_6584725) baseStart_6584725 baseEnd_6584725 := by
    simpa [prefixWord, tailWord_6584725, baseEnd_6584725] using wordTrace_append hprefix tailTrace_6584725
  have hstable : (prefixWord ++ tailWord_6584725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584725).length < 2 ^ (prefixWord ++ tailWord_6584725).sum := by decide
  have hdescent : baseEnd_6584725 < baseStart_6584725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584738 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6584738 : Nat := 118140960795 + 6584738 * 2 ^ 59
def prefixEnd_6584738 : Nat := 4983230072969 + 3 ^ 40 * 6584738 * 2
def baseEnd_6584738 : Nat := 3381135577925363415992347

theorem tailTrace_6584738 : CollatzResearch.WordTrace tailWord_6584738 prefixEnd_6584738 3381135577925363415992347 := by
  unfold tailWord_6584738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041281304656571140706717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160110083479084189708551245 60041281304656571140706717)
  ·
    refine ⟨22515480489246214177765019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60041281304656571140706717 22515480489246214177765019)
    ·
      refine ⟨33773220733869321266647529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515480489246214177765019 33773220733869321266647529)
      ·
        refine ⟨25329915550401990949985647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33773220733869321266647529 25329915550401990949985647)
        ·
          refine ⟨37994873325602986424978471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25329915550401990949985647 37994873325602986424978471)
          ·
            refine ⟨56992309988404479637467707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37994873325602986424978471 56992309988404479637467707)
            ·
              refine ⟨85488464982606719456201561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56992309988404479637467707 85488464982606719456201561)
              ·
                refine ⟨64116348736955039592151171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85488464982606719456201561 64116348736955039592151171)
                ·
                  refine ⟨96174523105432559388226757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64116348736955039592151171 96174523105432559388226757)
                  ·
                    refine ⟨18032723082268604885292517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96174523105432559388226757 18032723082268604885292517)
                    ·
                      refine ⟨3381135577925363415992347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18032723082268604885292517 3381135577925363415992347)
                      ·
                        rfl

theorem cell23_6584738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6584738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584738 prefixEnd_6584738 := by exact prefixLift 6584738
  have htrace : WordTrace (prefixWord ++ tailWord_6584738) baseStart_6584738 baseEnd_6584738 := by
    simpa [prefixWord, tailWord_6584738, baseEnd_6584738] using wordTrace_append hprefix tailTrace_6584738
  have hstable : (prefixWord ++ tailWord_6584738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584738).length < 2 ^ (prefixWord ++ tailWord_6584738).sum := by decide
  have hdescent : baseEnd_6584738 < baseStart_6584738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584759 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_6584759 : Nat := 118140960795 + 6584759 * 2 ^ 59
def prefixEnd_6584759 : Nat := 4983230072969 + 3 ^ 40 * 6584759 * 2
def baseEnd_6584759 : Nat := 3381146361019107833829751

theorem tailTrace_6584759 : CollatzResearch.WordTrace tailWord_6584759 prefixEnd_6584759 3381146361019107833829751 := by
  unfold tailWord_6584759
  simp only [CollatzResearch.WordTrace]
  refine ⟨240165891151550205149341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160110594101033470099560887 240165891151550205149341331)
  ·
    refine ⟨360248836727325307724011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240165891151550205149341331 360248836727325307724011997)
    ·
      refine ⟨135093313772746990396504499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360248836727325307724011997 135093313772746990396504499)
      ·
        refine ⟨202639970659120485594756749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135093313772746990396504499 202639970659120485594756749)
        ·
          refine ⟨75989988997170182098033781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202639970659120485594756749 75989988997170182098033781)
          ·
            refine ⟨7124061468484704571690667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75989988997170182098033781 7124061468484704571690667)
            ·
              refine ⟨10686092202727056857536001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124061468484704571690667 10686092202727056857536001)
              ·
                refine ⟨8014569152045292643152001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686092202727056857536001 8014569152045292643152001)
                ·
                  refine ⟨6010926864033969482364001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8014569152045292643152001 6010926864033969482364001)
                  ·
                    refine ⟨4508195148025477111773001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6010926864033969482364001 4508195148025477111773001)
                    ·
                      refine ⟨3381146361019107833829751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508195148025477111773001 3381146361019107833829751)
                      ·
                        rfl

theorem cell23_6584759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_6584759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584759 prefixEnd_6584759 := by exact prefixLift 6584759
  have htrace : WordTrace (prefixWord ++ tailWord_6584759) baseStart_6584759 baseEnd_6584759 := by
    simpa [prefixWord, tailWord_6584759, baseEnd_6584759] using wordTrace_append hprefix tailTrace_6584759
  have hstable : (prefixWord ++ tailWord_6584759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584759).length < 2 ^ (prefixWord ++ tailWord_6584759).sum := by decide
  have hdescent : baseEnd_6584759 < baseStart_6584759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584765 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 5]
def baseStart_6584765 : Nat := 118140960795 + 6584765 * 2 ^ 59
def prefixEnd_6584765 : Nat := 4983230072969 + 3 ^ 40 * 6584765 * 2
def baseEnd_6584765 : Nat := 375683271322559423372747

theorem tailTrace_6584765 : CollatzResearch.WordTrace tailWord_6584765 prefixEnd_6584765 375683271322559423372747 := by
  unfold tailWord_6584765
  simp only [CollatzResearch.WordTrace]
  refine ⟨240166109989528468174059749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160110739993018978782706499 240166109989528468174059749)
  ·
    refine ⟨45031145623036587782636203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240166109989528468174059749 45031145623036587782636203)
    ·
      refine ⟨67546718434554881673954305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45031145623036587782636203 67546718434554881673954305)
      ·
        refine ⟨50660038825916161255465729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67546718434554881673954305 50660038825916161255465729)
        ·
          refine ⟨37995029119437120941599297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50660038825916161255465729 37995029119437120941599297)
          ·
            refine ⟨28496271839577840706199473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37995029119437120941599297 28496271839577840706199473)
            ·
              refine ⟨21372203879683380529649605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28496271839577840706199473 21372203879683380529649605)
              ·
                refine ⟨4007288227440633849309301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21372203879683380529649605 4007288227440633849309301)
                ·
                  refine ⟨375683271322559423372747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007288227440633849309301 375683271322559423372747)
                  ·
                    rfl

theorem cell23_6584765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_6584765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584765 prefixEnd_6584765 := by exact prefixLift 6584765
  have htrace : WordTrace (prefixWord ++ tailWord_6584765) baseStart_6584765 baseEnd_6584765 := by
    simpa [prefixWord, tailWord_6584765, baseEnd_6584765] using wordTrace_append hprefix tailTrace_6584765
  have hstable : (prefixWord ++ tailWord_6584765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584765).length < 2 ^ (prefixWord ++ tailWord_6584765).sum := by decide
  have hdescent : baseEnd_6584765 < baseStart_6584765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584771 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_6584771 : Nat := 118140960795 + 6584771 * 2 ^ 59
def prefixEnd_6584771 : Nat := 4983230072969 + 3 ^ 40 * 6584771 * 2
def baseEnd_6584771 : Nat := 3381152522786961786879695

theorem tailTrace_6584771 : CollatzResearch.WordTrace tailWord_6584771 prefixEnd_6584771 3381152522786961786879695 := by
  unfold tailWord_6584771
  simp only [CollatzResearch.WordTrace]
  refine ⟨240166328827506731198778167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160110885885004487465852111 240166328827506731198778167)
  ·
    refine ⟨360249493241260096798167251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240166328827506731198778167 360249493241260096798167251)
    ·
      refine ⟨540374239861890145197250877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360249493241260096798167251 540374239861890145197250877)
      ·
        refine ⟨202640339948208804448969079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540374239861890145197250877 202640339948208804448969079)
        ·
          refine ⟨303960509922313206673453619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202640339948208804448969079 303960509922313206673453619)
          ·
            refine ⟨455940764883469810010180429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303960509922313206673453619 455940764883469810010180429)
            ·
              refine ⟨170977786831301178753817661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455940764883469810010180429 170977786831301178753817661)
              ·
                refine ⟨64116670061737942032681623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170977786831301178753817661 64116670061737942032681623)
                ·
                  refine ⟨96175005092606913049022435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64116670061737942032681623 96175005092606913049022435)
                  ·
                    refine ⟨144262507638910369573533653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96175005092606913049022435 144262507638910369573533653)
                    ·
                      refine ⟨3381152522786961786879695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144262507638910369573533653 3381152522786961786879695)
                      ·
                        rfl

theorem cell23_6584771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_6584771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584771 prefixEnd_6584771 := by exact prefixLift 6584771
  have htrace : WordTrace (prefixWord ++ tailWord_6584771) baseStart_6584771 baseEnd_6584771 := by
    simpa [prefixWord, tailWord_6584771, baseEnd_6584771] using wordTrace_append hprefix tailTrace_6584771
  have hstable : (prefixWord ++ tailWord_6584771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584771).length < 2 ^ (prefixWord ++ tailWord_6584771).sum := by decide
  have hdescent : baseEnd_6584771 < baseStart_6584771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584825 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_6584825 : Nat := 118140960795 + 6584825 * 2 ^ 59
def prefixEnd_6584825 : Nat := 4983230072969 + 3 ^ 40 * 6584825 * 2
def baseEnd_6584825 : Nat := 1127060083580768191868149

theorem tailTrace_6584825 : CollatzResearch.WordTrace tailWord_6584825 prefixEnd_6584825 1127060083580768191868149 := by
  unfold tailWord_6584825
  simp only [CollatzResearch.WordTrace]
  refine ⟨240168298369311098421243929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160112198912874065614162619 240168298369311098421243929)
  ·
    refine ⟨180126223776983323815932947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240168298369311098421243929 180126223776983323815932947)
    ·
      refine ⟨270189335665474985723899421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180126223776983323815932947 270189335665474985723899421)
      ·
        refine ⟨101321000874553119646462283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270189335665474985723899421 101321000874553119646462283)
        ·
          refine ⟨151981501311829679469693425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101321000874553119646462283 151981501311829679469693425)
          ·
            refine ⟨113986125983872259602270069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151981501311829679469693425 113986125983872259602270069)
            ·
              refine ⟨10686199310988024337712819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113986125983872259602270069 10686199310988024337712819)
              ·
                refine ⟨16029298966482036506569229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686199310988024337712819 16029298966482036506569229)
                ·
                  refine ⟨6010987112430763689963461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16029298966482036506569229 6010987112430763689963461)
                  ·
                    refine ⟨1127060083580768191868149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010987112430763689963461 1127060083580768191868149)
                    ·
                      rfl

theorem cell23_6584825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_6584825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584825 prefixEnd_6584825 := by exact prefixLift 6584825
  have htrace : WordTrace (prefixWord ++ tailWord_6584825) baseStart_6584825 baseEnd_6584825 := by
    simpa [prefixWord, tailWord_6584825, baseEnd_6584825] using wordTrace_append hprefix tailTrace_6584825
  have hstable : (prefixWord ++ tailWord_6584825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584825).length < 2 ^ (prefixWord ++ tailWord_6584825).sum := by decide
  have hdescent : baseEnd_6584825 < baseStart_6584825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584872 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 6]
def baseStart_6584872 : Nat := 118140960795 + 6584872 * 2 ^ 59
def prefixEnd_6584872 : Nat := 4983230072969 + 3 ^ 40 * 6584872 * 2
def baseEnd_6584872 : Nat := 375689376037007321301859

theorem tailTrace_6584872 : CollatzResearch.WordTrace tailWord_6584872 prefixEnd_6584872 375689376037007321301859 := by
  unfold tailWord_6584872
  simp only [CollatzResearch.WordTrace]
  refine ⟨120085006300070412724102435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160113341733427216965469913 120085006300070412724102435)
  ·
    refine ⟨180127509450105619086153653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120085006300070412724102435 180127509450105619086153653)
    ·
      refine ⟨16886954010947401789326905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180127509450105619086153653 16886954010947401789326905)
      ·
        refine ⟨12665215508210551341995179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16886954010947401789326905 12665215508210551341995179)
        ·
          refine ⟨18997823262315827012992769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12665215508210551341995179 18997823262315827012992769)
          ·
            refine ⟨14248367446736870259744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18997823262315827012992769 14248367446736870259744577)
            ·
              refine ⟨10686275585052652694808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248367446736870259744577 10686275585052652694808433)
              ·
                refine ⟨8014706688789489521106325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686275585052652694808433 8014706688789489521106325)
                ·
                  refine ⟨375689376037007321301859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8014706688789489521106325 375689376037007321301859)
                  ·
                    rfl

theorem cell23_6584872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_6584872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584872 prefixEnd_6584872 := by exact prefixLift 6584872
  have htrace : WordTrace (prefixWord ++ tailWord_6584872) baseStart_6584872 baseEnd_6584872 := by
    simpa [prefixWord, tailWord_6584872, baseEnd_6584872] using wordTrace_append hprefix tailTrace_6584872
  have hstable : (prefixWord ++ tailWord_6584872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584872).length < 2 ^ (prefixWord ++ tailWord_6584872).sum := by decide
  have hdescent : baseEnd_6584872 < baseStart_6584872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584909 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6584909 : Nat := 118140960795 + 6584909 * 2 ^ 59
def prefixEnd_6584909 : Nat := 4983230072969 + 3 ^ 40 * 6584909 * 2
def baseEnd_6584909 : Nat := 3381223383117282246954061

theorem tailTrace_6584909 : CollatzResearch.WordTrace tailWord_6584909 prefixEnd_6584909 3381223383117282246954061 := by
  unfold tailWord_6584909
  simp only [CollatzResearch.WordTrace]
  refine ⟨240171362101006780767301781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160114241400671187178201187 240171362101006780767301781)
  ·
    refine ⟨11258032598484692848467271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240171362101006780767301781 11258032598484692848467271)
    ·
      refine ⟨16887048897727039272700907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258032598484692848467271 16887048897727039272700907)
      ·
        refine ⟨25330573346590558909051361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16887048897727039272700907 25330573346590558909051361)
        ·
          refine ⟨18997930009942919181788521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25330573346590558909051361 18997930009942919181788521)
          ·
            refine ⟨14248447507457189386341391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18997930009942919181788521 14248447507457189386341391)
            ·
              refine ⟨21372671261185784079512087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14248447507457189386341391 21372671261185784079512087)
              ·
                refine ⟨32059006891778676119268131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21372671261185784079512087 32059006891778676119268131)
                ·
                  refine ⟨48088510337668014178902197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32059006891778676119268131 48088510337668014178902197)
                  ·
                    refine ⟨4508297844156376329272081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48088510337668014178902197 4508297844156376329272081)
                    ·
                      refine ⟨3381223383117282246954061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508297844156376329272081 3381223383117282246954061)
                      ·
                        rfl

theorem cell23_6584909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6584909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584909 prefixEnd_6584909 := by exact prefixLift 6584909
  have htrace : WordTrace (prefixWord ++ tailWord_6584909) baseStart_6584909 baseEnd_6584909 := by
    simpa [prefixWord, tailWord_6584909, baseEnd_6584909] using wordTrace_append hprefix tailTrace_6584909
  have hstable : (prefixWord ++ tailWord_6584909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584909).length < 2 ^ (prefixWord ++ tailWord_6584909).sum := by decide
  have hdescent : baseEnd_6584909 < baseStart_6584909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584916 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_6584916 : Nat := 118140960795 + 6584916 * 2 ^ 59
def prefixEnd_6584916 : Nat := 4983230072969 + 3 ^ 40 * 6584916 * 2
def baseEnd_6584916 : Nat := 3381226977481863719566529

theorem tailTrace_6584916 : CollatzResearch.WordTrace tailWord_6584916 prefixEnd_6584916 3381226977481863719566529 := by
  unfold tailWord_6584916
  simp only [CollatzResearch.WordTrace]
  refine ⟨120085808705990710481403301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160114411607987613975204401 120085808705990710481403301)
  ·
    refine ⟨22516089132373258215263119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120085808705990710481403301 22516089132373258215263119)
    ·
      refine ⟨33774133698559887322894679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22516089132373258215263119 33774133698559887322894679)
      ·
        refine ⟨50661200547839830984342019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33774133698559887322894679 50661200547839830984342019)
        ·
          refine ⟨75991800821759746476513029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50661200547839830984342019 75991800821759746476513029)
          ·
            refine ⟨14248462654079952464346193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75991800821759746476513029 14248462654079952464346193)
            ·
              refine ⟨10686346990559964348259645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248462654079952464346193 10686346990559964348259645)
              ·
                refine ⟨4007380121459986630597367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10686346990559964348259645 4007380121459986630597367)
                ·
                  refine ⟨6011070182189979945896051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007380121459986630597367 6011070182189979945896051)
                  ·
                    refine ⟨9016605273284969918844077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011070182189979945896051 9016605273284969918844077)
                    ·
                      refine ⟨3381226977481863719566529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9016605273284969918844077 3381226977481863719566529)
                      ·
                        rfl

theorem cell23_6584916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_6584916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584916 prefixEnd_6584916 := by exact prefixLift 6584916
  have htrace : WordTrace (prefixWord ++ tailWord_6584916) baseStart_6584916 baseEnd_6584916 := by
    simpa [prefixWord, tailWord_6584916, baseEnd_6584916] using wordTrace_append hprefix tailTrace_6584916
  have hstable : (prefixWord ++ tailWord_6584916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584916).length < 2 ^ (prefixWord ++ tailWord_6584916).sum := by decide
  have hdescent : baseEnd_6584916 < baseStart_6584916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584942 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6584942 : Nat := 118140960795 + 6584942 * 2 ^ 59
def prefixEnd_6584942 : Nat := 4983230072969 + 3 ^ 40 * 6584942 * 2
def baseEnd_6584942 : Nat := 3381240327978880617841409

theorem tailTrace_6584942 : CollatzResearch.WordTrace tailWord_6584942 prefixEnd_6584942 3381240327978880617841409 := by
  unfold tailWord_6584942
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021570713735903425406635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160115043806591484935502053 30021570713735903425406635)
  ·
    refine ⟨45032356070603855138109953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30021570713735903425406635 45032356070603855138109953)
    ·
      refine ⟨33774267052952891353582465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45032356070603855138109953 33774267052952891353582465)
      ·
        refine ⟨25330700289714668515186849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33774267052952891353582465 25330700289714668515186849)
        ·
          refine ⟨18998025217286001386390137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25330700289714668515186849 18998025217286001386390137)
          ·
            refine ⟨14248518912964501039792603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998025217286001386390137 14248518912964501039792603)
            ·
              refine ⟨21372778369446751559688905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14248518912964501039792603 21372778369446751559688905)
              ·
                refine ⟨16029583777085063669766679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21372778369446751559688905 16029583777085063669766679)
                ·
                  refine ⟨24044375665627595504650019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16029583777085063669766679 24044375665627595504650019)
                  ·
                    refine ⟨36066563498441393256975029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24044375665627595504650019 36066563498441393256975029)
                    ·
                      refine ⟨3381240327978880617841409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36066563498441393256975029 3381240327978880617841409)
                      ·
                        rfl

theorem cell23_6584942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6584942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584942 prefixEnd_6584942 := by exact prefixLift 6584942
  have htrace : WordTrace (prefixWord ++ tailWord_6584942) baseStart_6584942 baseEnd_6584942 := by
    simpa [prefixWord, tailWord_6584942, baseEnd_6584942] using wordTrace_append hprefix tailTrace_6584942
  have hstable : (prefixWord ++ tailWord_6584942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584942).length < 2 ^ (prefixWord ++ tailWord_6584942).sum := by decide
  have hdescent : baseEnd_6584942 < baseStart_6584942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584949 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6584949 : Nat := 118140960795 + 6584949 * 2 ^ 59
def prefixEnd_6584949 : Nat := 4983230072969 + 3 ^ 40 * 6584949 * 2
def baseEnd_6584949 : Nat := 1127081307447820696817959

theorem tailTrace_6584949 : CollatzResearch.WordTrace tailWord_6584949 prefixEnd_6584949 1127081307447820696817959 := by
  unfold tailWord_6584949
  simp only [CollatzResearch.WordTrace]
  refine ⟨240172821020861867598757901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160115214013907911732505267 240172821020861867598757901)
  ·
    refine ⟨90064807882823200349534213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240172821020861867598757901 90064807882823200349534213)
    ·
      refine ⟨16887151478029350065537665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90064807882823200349534213 16887151478029350065537665)
      ·
        refine ⟨12665363608522012549153249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16887151478029350065537665 12665363608522012549153249)
        ·
          refine ⟨9499022706391509411864937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12665363608522012549153249 9499022706391509411864937)
          ·
            refine ⟨7124267029793632058898703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499022706391509411864937 7124267029793632058898703)
            ·
              refine ⟨10686400544690448088348055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124267029793632058898703 10686400544690448088348055)
              ·
                refine ⟨16029600817035672132522083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686400544690448088348055 16029600817035672132522083)
                ·
                  refine ⟨24044401225553508198783125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16029600817035672132522083 24044401225553508198783125)
                  ·
                    refine ⟨1127081307447820696817959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24044401225553508198783125 1127081307447820696817959)
                    ·
                      rfl

theorem cell23_6584949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6584949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584949 prefixEnd_6584949 := by exact prefixLift 6584949
  have htrace : WordTrace (prefixWord ++ tailWord_6584949) baseStart_6584949 baseEnd_6584949 := by
    simpa [prefixWord, tailWord_6584949, baseEnd_6584949] using wordTrace_append hprefix tailTrace_6584949
  have hstable : (prefixWord ++ tailWord_6584949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584949).length < 2 ^ (prefixWord ++ tailWord_6584949).sum := by decide
  have hdescent : baseEnd_6584949 < baseStart_6584949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584955 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3]
def baseStart_6584955 : Nat := 118140960795 + 6584955 * 2 ^ 59
def prefixEnd_6584955 : Nat := 4983230072969 + 3 ^ 40 * 6584955 * 2
def baseEnd_6584955 : Nat := 3381247003227389066978849

theorem tailTrace_6584955 : CollatzResearch.WordTrace tailWord_6584955 prefixEnd_6584955 3381247003227389066978849 := by
  unfold tailWord_6584955
  simp only [CollatzResearch.WordTrace]
  refine ⟨240173039858840130623476319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160115359905893420415650879 240173039858840130623476319)
  ·
    refine ⟨360259559788260195935214479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240173039858840130623476319 360259559788260195935214479)
    ·
      refine ⟨540389339682390293902821719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360259559788260195935214479 540389339682390293902821719)
      ·
        refine ⟨810584009523585440854232579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540389339682390293902821719 810584009523585440854232579)
        ·
          refine ⟨1215876014285378161281348869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810584009523585440854232579 1215876014285378161281348869)
          ·
            refine ⟨227976752678508405240252913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1215876014285378161281348869 227976752678508405240252913)
            ·
              refine ⟨170982564508881303930189685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227976752678508405240252913 170982564508881303930189685)
              ·
                refine ⟨16029615422707622243455283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170982564508881303930189685 16029615422707622243455283)
                ·
                  refine ⟨24044423134061433365182925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16029615422707622243455283 24044423134061433365182925)
                  ·
                    refine ⟨9016658675273037511943597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24044423134061433365182925 9016658675273037511943597)
                    ·
                      refine ⟨3381247003227389066978849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9016658675273037511943597 3381247003227389066978849)
                      ·
                        rfl

theorem cell23_6584955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].length) (baseStart_6584955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584955 prefixEnd_6584955 := by exact prefixLift 6584955
  have htrace : WordTrace (prefixWord ++ tailWord_6584955) baseStart_6584955 baseEnd_6584955 := by
    simpa [prefixWord, tailWord_6584955, baseEnd_6584955] using wordTrace_append hprefix tailTrace_6584955
  have hstable : (prefixWord ++ tailWord_6584955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584955).length < 2 ^ (prefixWord ++ tailWord_6584955).sum := by decide
  have hdescent : baseEnd_6584955 < baseStart_6584955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6584990 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6584990 : Nat := 118140960795 + 6584990 * 2 ^ 59
def prefixEnd_6584990 : Nat := 4983230072969 + 3 ^ 40 * 6584990 * 2
def baseEnd_6584990 : Nat := 3381264975050296430041189

theorem tailTrace_6584990 : CollatzResearch.WordTrace tailWord_6584990 prefixEnd_6584990 3381264975050296430041189 := by
  unfold tailWord_6584990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021789551714166450125053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160116210942475554400666949 30021789551714166450125053)
  ·
    refine ⟨11258171081892812418796895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30021789551714166450125053 11258171081892812418796895)
    ·
      refine ⟨16887256622839218628195343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258171081892812418796895 16887256622839218628195343)
      ·
        refine ⟨25330884934258827942293015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16887256622839218628195343 25330884934258827942293015)
        ·
          refine ⟨37996327401388241913439523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25330884934258827942293015 37996327401388241913439523)
          ·
            refine ⟨56994491102082362870159285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37996327401388241913439523 56994491102082362870159285)
            ·
              refine ⟨5343233540820221519077433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56994491102082362870159285 5343233540820221519077433)
              ·
                refine ⟨4007425155615166139308075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343233540820221519077433 4007425155615166139308075)
                ·
                  refine ⟨6011137733422749208962113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007425155615166139308075 6011137733422749208962113)
                  ·
                    refine ⟨4508353300067061906721585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6011137733422749208962113 4508353300067061906721585)
                    ·
                      refine ⟨3381264975050296430041189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508353300067061906721585 3381264975050296430041189)
                      ·
                        rfl

theorem cell23_6584990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6584990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6584990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6584990 prefixEnd_6584990 := by exact prefixLift 6584990
  have htrace : WordTrace (prefixWord ++ tailWord_6584990) baseStart_6584990 baseEnd_6584990 := by
    simpa [prefixWord, tailWord_6584990, baseEnd_6584990] using wordTrace_append hprefix tailTrace_6584990
  have hstable : (prefixWord ++ tailWord_6584990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6584990).length < 2 ^ (prefixWord ++ tailWord_6584990).sum := by decide
  have hdescent : baseEnd_6584990 < baseStart_6584990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6584990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585065 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_6585065 : Nat := 118140960795 + 6585065 * 2 ^ 59
def prefixEnd_6585065 : Nat := 4983230072969 + 3 ^ 40 * 6585065 * 2
def baseEnd_6585065 : Nat := 1127101162033127878867781

theorem tailTrace_6585065 : CollatzResearch.WordTrace tailWord_6585065 prefixEnd_6585065 1127101162033127878867781 := by
  unfold tailWord_6585065
  simp only [CollatzResearch.WordTrace]
  refine ⟨240177051888441619409980649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160118034592294412939987099 240177051888441619409980649)
  ·
    refine ⟨180132788916331214557485487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240177051888441619409980649 180132788916331214557485487)
    ·
      refine ⟨270199183374496821836228231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180132788916331214557485487 270199183374496821836228231)
      ·
        refine ⟨405298775061745232754342347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270199183374496821836228231 405298775061745232754342347)
        ·
          refine ⟨607948162592617849131513521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405298775061745232754342347 607948162592617849131513521)
          ·
            refine ⟨455961121944463386848635141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607948162592617849131513521 455961121944463386848635141)
            ·
              refine ⟨85492710364586885034119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455961121944463386848635141 85492710364586885034119089)
              ·
                refine ⟨64119532773440163775589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85492710364586885034119089 64119532773440163775589317)
                ·
                  refine ⟨12022412395020030707922997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64119532773440163775589317 12022412395020030707922997)
                  ·
                    refine ⟨1127101162033127878867781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12022412395020030707922997 1127101162033127878867781)
                    ·
                      rfl

theorem cell23_6585065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_6585065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585065 prefixEnd_6585065 := by exact prefixLift 6585065
  have htrace : WordTrace (prefixWord ++ tailWord_6585065) baseStart_6585065 baseEnd_6585065 := by
    simpa [prefixWord, tailWord_6585065, baseEnd_6585065] using wordTrace_append hprefix tailTrace_6585065
  have hstable : (prefixWord ++ tailWord_6585065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585065).length < 2 ^ (prefixWord ++ tailWord_6585065).sum := by decide
  have hdescent : baseEnd_6585065 < baseStart_6585065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585072 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2]
def baseStart_6585072 : Nat := 118140960795 + 6585072 * 2 ^ 59
def prefixEnd_6585072 : Nat := 4983230072969 + 3 ^ 40 * 6585072 * 2
def baseEnd_6585072 : Nat := 3381307080463965109215811

theorem tailTrace_6585072 : CollatzResearch.WordTrace tailWord_6585072 prefixEnd_6585072 3381307080463965109215811 := by
  unfold tailWord_6585072
  simp only [CollatzResearch.WordTrace]
  refine ⟨120088653599708129802742735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160118204799610839736990313 120088653599708129802742735)
  ·
    refine ⟨180132980399562194704114103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120088653599708129802742735 180132980399562194704114103)
    ·
      refine ⟨270199470599343292056171155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180132980399562194704114103 270199470599343292056171155)
      ·
        refine ⟨405299205899014938084256733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270199470599343292056171155 405299205899014938084256733)
        ·
          refine ⟨151987202212130601781596275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405299205899014938084256733 151987202212130601781596275)
          ·
            refine ⟨227980803318195902672394413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151987202212130601781596275 227980803318195902672394413)
            ·
              refine ⟨85492801244323463502147905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227980803318195902672394413 85492801244323463502147905)
              ·
                refine ⟨64119600933242597626610929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85492801244323463502147905 64119600933242597626610929)
                ·
                  refine ⟨48089700699931948219958197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64119600933242597626610929 48089700699931948219958197)
                  ·
                    refine ⟨4508409440618620145621081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48089700699931948219958197 4508409440618620145621081)
                    ·
                      refine ⟨3381307080463965109215811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508409440618620145621081 3381307080463965109215811)
                      ·
                        rfl

theorem cell23_6585072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2].length) (baseStart_6585072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585072 prefixEnd_6585072 := by exact prefixLift 6585072
  have htrace : WordTrace (prefixWord ++ tailWord_6585072) baseStart_6585072 baseEnd_6585072 := by
    simpa [prefixWord, tailWord_6585072, baseEnd_6585072] using wordTrace_append hprefix tailTrace_6585072
  have hstable : (prefixWord ++ tailWord_6585072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585072).length < 2 ^ (prefixWord ++ tailWord_6585072).sum := by decide
  have hdescent : baseEnd_6585072 < baseStart_6585072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585082 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_6585082 : Nat := 118140960795 + 6585082 * 2 ^ 59
def prefixEnd_6585082 : Nat := 4983230072969 + 3 ^ 40 * 6585082 * 2
def baseEnd_6585082 : Nat := 1127104071756836690030255

theorem tailTrace_6585082 : CollatzResearch.WordTrace tailWord_6585082 prefixEnd_6585082 1127104071756836690030255 := by
  unfold tailWord_6585082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60044417982345007828337375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160118447952920020875566333 60044417982345007828337375)
  ·
    refine ⟨90066626973517511742506063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60044417982345007828337375 90066626973517511742506063)
    ·
      refine ⟨135099940460276267613759095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90066626973517511742506063 135099940460276267613759095)
      ·
        refine ⟨202649910690414401420638643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135099940460276267613759095 202649910690414401420638643)
        ·
          refine ⟨303974866035621602130957965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202649910690414401420638643 303974866035621602130957965)
          ·
            refine ⟨113990574763358100799109237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303974866035621602130957965 113990574763358100799109237)
            ·
              refine ⟨10686616384064821949916491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113990574763358100799109237 10686616384064821949916491)
              ·
                refine ⟨16029924576097232924874737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686616384064821949916491 16029924576097232924874737)
                ·
                  refine ⟨12022443432072924693656053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16029924576097232924874737 12022443432072924693656053)
                  ·
                    refine ⟨1127104071756836690030255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12022443432072924693656053 1127104071756836690030255)
                    ·
                      rfl

theorem cell23_6585082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_6585082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585082 prefixEnd_6585082 := by exact prefixLift 6585082
  have htrace : WordTrace (prefixWord ++ tailWord_6585082) baseStart_6585082 baseEnd_6585082 := by
    simpa [prefixWord, tailWord_6585082, baseEnd_6585082] using wordTrace_append hprefix tailTrace_6585082
  have hstable : (prefixWord ++ tailWord_6585082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585082).length < 2 ^ (prefixWord ++ tailWord_6585082).sum := by decide
  have hdescent : baseEnd_6585082 < baseStart_6585082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585086 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_6585086 : Nat := 118140960795 + 6585086 * 2 ^ 59
def prefixEnd_6585086 : Nat := 4983230072969 + 3 ^ 40 * 6585086 * 2
def baseEnd_6585086 : Nat := 375701585465903117160083

theorem tailTrace_6585086 : CollatzResearch.WordTrace tailWord_6585086 prefixEnd_6585086 375701585465903117160083 := by
  unfold tailWord_6585086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022227227670692499561889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160118545214243693330996741 30022227227670692499561889)
  ·
    refine ⟨22516670420753019374671417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30022227227670692499561889 22516670420753019374671417)
    ·
      refine ⟨16887502815564764531003563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22516670420753019374671417 16887502815564764531003563)
      ·
        refine ⟨25331254223347146796505345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16887502815564764531003563 25331254223347146796505345)
        ·
          refine ⟨18998440667510360097379009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25331254223347146796505345 18998440667510360097379009)
          ·
            refine ⟨14248830500632770073034257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998440667510360097379009 14248830500632770073034257)
            ·
              refine ⟨10686622875474577554775693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248830500632770073034257 10686622875474577554775693)
              ·
                refine ⟨4007483578302966583040885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10686622875474577554775693 4007483578302966583040885)
                ·
                  refine ⟨375701585465903117160083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007483578302966583040885 375701585465903117160083)
                  ·
                    rfl

theorem cell23_6585086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_6585086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585086 prefixEnd_6585086 := by exact prefixLift 6585086
  have htrace : WordTrace (prefixWord ++ tailWord_6585086) baseStart_6585086 baseEnd_6585086 := by
    simpa [prefixWord, tailWord_6585086, baseEnd_6585086] using wordTrace_append hprefix tailTrace_6585086
  have hstable : (prefixWord ++ tailWord_6585086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585086).length < 2 ^ (prefixWord ++ tailWord_6585086).sum := by decide
  have hdescent : baseEnd_6585086 < baseStart_6585086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585102 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6585102 : Nat := 118140960795 + 6585102 * 2 ^ 59
def prefixEnd_6585102 : Nat := 4983230072969 + 3 ^ 40 * 6585102 * 2
def baseEnd_6585102 : Nat := 3381322484883599991840673

theorem tailTrace_6585102 : CollatzResearch.WordTrace tailWord_6585102 prefixEnd_6585102 3381322484883599991840673 := by
  unfold tailWord_6585102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022300173663446841134695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160118934259538383152718373 30022300173663446841134695)
  ·
    refine ⟨45033450260495170261702043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30022300173663446841134695 45033450260495170261702043)
    ·
      refine ⟨67550175390742755392553065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45033450260495170261702043 67550175390742755392553065)
      ·
        refine ⟨50662631543057066544414799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67550175390742755392553065 50662631543057066544414799)
        ·
          refine ⟨75993947314585599816622199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50662631543057066544414799 75993947314585599816622199)
          ·
            refine ⟨113990920971878399724933299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75993947314585599816622199 113990920971878399724933299)
            ·
              refine ⟨170986381457817599587399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113990920971878399724933299 170986381457817599587399949)
              ·
                refine ⟨64119893046681599845274981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170986381457817599587399949 64119893046681599845274981)
                ·
                  refine ⟨12022479946252799970989059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64119893046681599845274981 12022479946252799970989059)
                  ·
                    refine ⟨18033719919379199956483589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12022479946252799970989059 18033719919379199956483589)
                    ·
                      refine ⟨3381322484883599991840673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18033719919379199956483589 3381322484883599991840673)
                      ·
                        rfl

theorem cell23_6585102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6585102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585102 prefixEnd_6585102 := by exact prefixLift 6585102
  have htrace : WordTrace (prefixWord ++ tailWord_6585102) baseStart_6585102 baseEnd_6585102 := by
    simpa [prefixWord, tailWord_6585102, baseEnd_6585102] using wordTrace_append hprefix tailTrace_6585102
  have hstable : (prefixWord ++ tailWord_6585102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585102).length < 2 ^ (prefixWord ++ tailWord_6585102).sum := by decide
  have hdescent : baseEnd_6585102 < baseStart_6585102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585105 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_6585105 : Nat := 118140960795 + 6585105 * 2 ^ 59
def prefixEnd_6585105 : Nat := 4983230072969 + 3 ^ 40 * 6585105 * 2
def baseEnd_6585105 : Nat := 3381324025325563480103159

theorem tailTrace_6585105 : CollatzResearch.WordTrace tailWord_6585105 prefixEnd_6585105 3381324025325563480103159 := by
  unfold tailWord_6585105
  simp only [CollatzResearch.WordTrace]
  refine ⟨240178510808296706241436769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160119007205531137494291179 240178510808296706241436769)
  ·
    refine ⟨180133883106222529681077577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240178510808296706241436769 180133883106222529681077577)
    ·
      refine ⟨135100412329666897260808183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180133883106222529681077577 135100412329666897260808183)
      ·
        refine ⟨202650618494500345891212275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135100412329666897260808183 202650618494500345891212275)
        ·
          refine ⟨303975927741750518836818413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202650618494500345891212275 303975927741750518836818413)
          ·
            refine ⟨113990972903156444563806905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303975927741750518836818413 113990972903156444563806905)
            ·
              refine ⟨85493229677367333422855179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113990972903156444563806905 85493229677367333422855179)
              ·
                refine ⟨128239844516051000134282769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85493229677367333422855179 128239844516051000134282769)
                ·
                  refine ⟨96179883387038250100712077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128239844516051000134282769 96179883387038250100712077)
                  ·
                    refine ⟨36067456270139343787767029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96179883387038250100712077 36067456270139343787767029)
                    ·
                      refine ⟨3381324025325563480103159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36067456270139343787767029 3381324025325563480103159)
                      ·
                        rfl

theorem cell23_6585105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_6585105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585105 prefixEnd_6585105 := by exact prefixLift 6585105
  have htrace : WordTrace (prefixWord ++ tailWord_6585105) baseStart_6585105 baseEnd_6585105 := by
    simpa [prefixWord, tailWord_6585105, baseEnd_6585105] using wordTrace_append hprefix tailTrace_6585105
  have hstable : (prefixWord ++ tailWord_6585105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585105).length < 2 ^ (prefixWord ++ tailWord_6585105).sum := by decide
  have hdescent : baseEnd_6585105 < baseStart_6585105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585115 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_6585115 : Nat := 118140960795 + 6585115 * 2 ^ 59
def prefixEnd_6585115 : Nat := 4983230072969 + 3 ^ 40 * 6585115 * 2
def baseEnd_6585115 : Nat := 3381329160132108440978113

theorem tailTrace_6585115 : CollatzResearch.WordTrace tailWord_6585115 prefixEnd_6585115 3381329160132108440978113 := by
  unfold tailWord_6585115
  simp only [CollatzResearch.WordTrace]
  refine ⟨240178875538260477949300799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160119250358840318632867199 240178875538260477949300799)
  ·
    refine ⟨360268313307390716923951199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240178875538260477949300799 360268313307390716923951199)
    ·
      refine ⟨540402469961086075385926799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360268313307390716923951199 540402469961086075385926799)
      ·
        refine ⟨810603704941629113078890199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540402469961086075385926799 810603704941629113078890199)
        ·
          refine ⟨1215905557412443669618335299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810603704941629113078890199 1215905557412443669618335299)
          ·
            refine ⟨1823858336118665504427502949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215905557412443669618335299 1823858336118665504427502949)
            ·
              refine ⟨341973438022249782080156803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1823858336118665504427502949 341973438022249782080156803)
              ·
                refine ⟨512960157033374673120235205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341973438022249782080156803 512960157033374673120235205)
                ·
                  refine ⟨96180029443757751210044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512960157033374673120235205 96180029443757751210044101)
                  ·
                    refine ⟨18033755520704578351883269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96180029443757751210044101 18033755520704578351883269)
                    ·
                      refine ⟨3381329160132108440978113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18033755520704578351883269 3381329160132108440978113)
                      ·
                        rfl

theorem cell23_6585115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_6585115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585115 prefixEnd_6585115 := by exact prefixLift 6585115
  have htrace : WordTrace (prefixWord ++ tailWord_6585115) baseStart_6585115 baseEnd_6585115 := by
    simpa [prefixWord, tailWord_6585115, baseEnd_6585115] using wordTrace_append hprefix tailTrace_6585115
  have hstable : (prefixWord ++ tailWord_6585115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585115).length < 2 ^ (prefixWord ++ tailWord_6585115).sum := by decide
  have hdescent : baseEnd_6585115 < baseStart_6585115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585119 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 4, 2]
def baseStart_6585119 : Nat := 118140960795 + 6585119 * 2 ^ 59
def prefixEnd_6585119 : Nat := 4983230072969 + 3 ^ 40 * 6585119 * 2
def baseEnd_6585119 : Nat := 3381331214054726425328095

theorem tailTrace_6585119 : CollatzResearch.WordTrace tailWord_6585119 prefixEnd_6585119 3381331214054726425328095 := by
  unfold tailWord_6585119
  simp only [CollatzResearch.WordTrace]
  refine ⟨240179021430245986632446411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160119347620163991088297607 240179021430245986632446411)
  ·
    refine ⟨360268532145368979948669617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240179021430245986632446411 360268532145368979948669617)
    ·
      refine ⟨270201399109026734961502213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360268532145368979948669617 270201399109026734961502213)
      ·
        refine ⟨50662762332942512805281665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270201399109026734961502213 50662762332942512805281665)
        ·
          refine ⟨37997071749706884603961249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50662762332942512805281665 37997071749706884603961249)
          ·
            refine ⟨28497803812280163452970937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37997071749706884603961249 28497803812280163452970937)
            ·
              refine ⟨21373352859210122589728203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28497803812280163452970937 21373352859210122589728203)
              ·
                refine ⟨32060029288815183884592305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21373352859210122589728203 32060029288815183884592305)
                ·
                  refine ⟨24045021966611387913444229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32060029288815183884592305 24045021966611387913444229)
                  ·
                    refine ⟨4508441618739635233770793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24045021966611387913444229 4508441618739635233770793)
                    ·
                      refine ⟨3381331214054726425328095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508441618739635233770793 3381331214054726425328095)
                      ·
                        rfl

theorem cell23_6585119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_6585119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585119 prefixEnd_6585119 := by exact prefixLift 6585119
  have htrace : WordTrace (prefixWord ++ tailWord_6585119) baseStart_6585119 baseEnd_6585119 := by
    simpa [prefixWord, tailWord_6585119, baseEnd_6585119] using wordTrace_append hprefix tailTrace_6585119
  have hstable : (prefixWord ++ tailWord_6585119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585119).length < 2 ^ (prefixWord ++ tailWord_6585119).sum := by decide
  have hdescent : baseEnd_6585119 < baseStart_6585119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585189 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_6585189 : Nat := 118140960795 + 6585189 * 2 ^ 59
def prefixEnd_6585189 : Nat := 4983230072969 + 3 ^ 40 * 6585189 * 2
def baseEnd_6585189 : Nat := 1127122385900180383817591

theorem tailTrace_6585189 : CollatzResearch.WordTrace tailWord_6585189 prefixEnd_6585189 1127122385900180383817591 := by
  unfold tailWord_6585189
  simp only [CollatzResearch.WordTrace]
  refine ⟨240181574539992388587494621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160121049693328259058329747 240181574539992388587494621)
  ·
    refine ⟨90068090452497145720310483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240181574539992388587494621 90068090452497145720310483)
    ·
      refine ⟨135102135678745718580465725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90068090452497145720310483 135102135678745718580465725)
      ·
        refine ⟨50663300879529644467674647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135102135678745718580465725 50663300879529644467674647)
        ·
          refine ⟨75994951319294466701511971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50663300879529644467674647 75994951319294466701511971)
          ·
            refine ⟨113992426978941700052267957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75994951319294466701511971 113992426978941700052267957)
            ·
              refine ⟨10686790029275784379900121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113992426978941700052267957 10686790029275784379900121)
              ·
                refine ⟨8015092521956838284925091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686790029275784379900121 8015092521956838284925091)
                ·
                  refine ⟨12022638782935257427387637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8015092521956838284925091 12022638782935257427387637)
                  ·
                    refine ⟨1127122385900180383817591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12022638782935257427387637 1127122385900180383817591)
                    ·
                      rfl

theorem cell23_6585189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_6585189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585189 prefixEnd_6585189 := by exact prefixLift 6585189
  have htrace : WordTrace (prefixWord ++ tailWord_6585189) baseStart_6585189 baseEnd_6585189 := by
    simpa [prefixWord, tailWord_6585189, baseEnd_6585189] using wordTrace_append hprefix tailTrace_6585189
  have hstable : (prefixWord ++ tailWord_6585189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585189).length < 2 ^ (prefixWord ++ tailWord_6585189).sum := by decide
  have hdescent : baseEnd_6585189 < baseStart_6585189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585196 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_6585196 : Nat := 118140960795 + 6585196 * 2 ^ 59
def prefixEnd_6585196 : Nat := 4983230072969 + 3 ^ 40 * 6585196 * 2
def baseEnd_6585196 : Nat := 3381370752065122624065241

theorem tailTrace_6585196 : CollatzResearch.WordTrace tailWord_6585196 prefixEnd_6585196 3381370752065122624065241 := by
  unfold tailWord_6585196
  simp only [CollatzResearch.WordTrace]
  refine ⟨120090914925483514391499721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160121219900644685855332961 120090914925483514391499721)
  ·
    refine ⟨90068186194112635793624791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120090914925483514391499721 90068186194112635793624791)
    ·
      refine ⟨135102279291168953690437187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90068186194112635793624791 135102279291168953690437187)
      ·
        refine ⟨202653418936753430535655781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135102279291168953690437187 202653418936753430535655781)
        ·
          refine ⟨37997516050641268225435459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202653418936753430535655781 37997516050641268225435459)
          ·
            refine ⟨56996274075961902338153189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37997516050641268225435459 56996274075961902338153189)
            ·
              refine ⟨10686801389242856688403723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56996274075961902338153189 10686801389242856688403723)
              ·
                refine ⟨16030202083864285032605585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686801389242856688403723 16030202083864285032605585)
                ·
                  refine ⟨12022651562898213774454189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16030202083864285032605585 12022651562898213774454189)
                  ·
                    refine ⟨4508494336086830165420321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12022651562898213774454189 4508494336086830165420321)
                    ·
                      refine ⟨3381370752065122624065241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508494336086830165420321 3381370752065122624065241)
                      ·
                        rfl

theorem cell23_6585196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_6585196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585196 prefixEnd_6585196 := by exact prefixLift 6585196
  have htrace : WordTrace (prefixWord ++ tailWord_6585196) baseStart_6585196 baseEnd_6585196 := by
    simpa [prefixWord, tailWord_6585196, baseEnd_6585196] using wordTrace_append hprefix tailTrace_6585196
  have hstable : (prefixWord ++ tailWord_6585196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585196).length < 2 ^ (prefixWord ++ tailWord_6585196).sum := by decide
  have hdescent : baseEnd_6585196 < baseStart_6585196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585202 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_6585202 : Nat := 118140960795 + 6585202 * 2 ^ 59
def prefixEnd_6585202 : Nat := 4983230072969 + 3 ^ 40 * 6585202 * 2
def baseEnd_6585202 : Nat := 1127124610983016533530071

theorem tailTrace_6585202 : CollatzResearch.WordTrace tailWord_6585202 prefixEnd_6585202 1127124610983016533530071 := by
  unfold tailWord_6585202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60045512172236322951929465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160121365792630194538478573 60045512172236322951929465)
  ·
    refine ⟨45034134129177242213947099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60045512172236322951929465 45034134129177242213947099)
    ·
      refine ⟨67551201193765863320920649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45034134129177242213947099 67551201193765863320920649)
      ·
        refine ⟨50663400895324397490690487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67551201193765863320920649 50663400895324397490690487)
        ·
          refine ⟨75995101342986596236035731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50663400895324397490690487 75995101342986596236035731)
          ·
            refine ⟨113992652014479894354053597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75995101342986596236035731 113992652014479894354053597)
            ·
              refine ⟨42747244505429960382770099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113992652014479894354053597 42747244505429960382770099)
              ·
                refine ⟨64120866758144940574155149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42747244505429960382770099 64120866758144940574155149)
                ·
                  refine ⟨24045325034304352715308181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64120866758144940574155149 24045325034304352715308181)
                  ·
                    refine ⟨1127124610983016533530071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24045325034304352715308181 1127124610983016533530071)
                    ·
                      rfl

theorem cell23_6585202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_6585202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585202 prefixEnd_6585202 := by exact prefixLift 6585202
  have htrace : WordTrace (prefixWord ++ tailWord_6585202) baseStart_6585202 baseEnd_6585202 := by
    simpa [prefixWord, tailWord_6585202, baseEnd_6585202] using wordTrace_append hprefix tailTrace_6585202
  have hstable : (prefixWord ++ tailWord_6585202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585202).length < 2 ^ (prefixWord ++ tailWord_6585202).sum := by decide
  have hdescent : baseEnd_6585202 < baseStart_6585202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585214 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6585214 : Nat := 118140960795 + 6585214 * 2 ^ 59
def prefixEnd_6585214 : Nat := 4983230072969 + 3 ^ 40 * 6585214 * 2
def baseEnd_6585214 : Nat := 1127126664905634517880053

theorem tailTrace_6585214 : CollatzResearch.WordTrace tailWord_6585214 prefixEnd_6585214 1127126664905634517880053 := by
  unfold tailWord_6585214
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022810795612727232144337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160121657576601211904769797 30022810795612727232144337)
  ·
    refine ⟨22517108096709545424108253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30022810795612727232144337 22517108096709545424108253)
    ·
      refine ⟨8443915536266079534040595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22517108096709545424108253 8443915536266079534040595)
      ·
        refine ⟨12665873304399119301060893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443915536266079534040595 12665873304399119301060893)
        ·
          refine ⟨4749702489149669737897835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12665873304399119301060893 4749702489149669737897835)
          ·
            refine ⟨7124553733724504606846753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749702489149669737897835 7124553733724504606846753)
            ·
              refine ⟨5343415300293378455135065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124553733724504606846753 5343415300293378455135065)
              ·
                refine ⟨4007561475220033841351299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343415300293378455135065 4007561475220033841351299)
                ·
                  refine ⟨6011342212830050762026949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007561475220033841351299 6011342212830050762026949)
                  ·
                    refine ⟨1127126664905634517880053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011342212830050762026949 1127126664905634517880053)
                    ·
                      rfl

theorem cell23_6585214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6585214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585214 prefixEnd_6585214 := by exact prefixLift 6585214
  have htrace : WordTrace (prefixWord ++ tailWord_6585214) baseStart_6585214 baseEnd_6585214 := by
    simpa [prefixWord, tailWord_6585214, baseEnd_6585214] using wordTrace_append hprefix tailTrace_6585214
  have hstable : (prefixWord ++ tailWord_6585214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585214).length < 2 ^ (prefixWord ++ tailWord_6585214).sum := by decide
  have hdescent : baseEnd_6585214 < baseStart_6585214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585236 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_6585236 : Nat := 118140960795 + 6585236 * 2 ^ 59
def prefixEnd_6585236 : Nat := 4983230072969 + 3 ^ 40 * 6585236 * 2
def baseEnd_6585236 : Nat := 1127130430430434155855019

theorem tailTrace_6585236 : CollatzResearch.WordTrace tailWord_6585236 prefixEnd_6585236 1127130430430434155855019 := by
  unfold tailWord_6585236
  simp only [CollatzResearch.WordTrace]
  refine ⟨120091644385411057807227781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160122192513881410409637041 120091644385411057807227781)
  ·
    refine ⟨22517183322264573338855209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120091644385411057807227781 22517183322264573338855209)
    ·
      refine ⟨16887887491698430004141407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22517183322264573338855209 16887887491698430004141407)
      ·
        refine ⟨25331831237547645006212111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16887887491698430004141407 25331831237547645006212111)
        ·
          refine ⟨37997746856321467509318167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25331831237547645006212111 37997746856321467509318167)
          ·
            refine ⟨56996620284482201263977251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37997746856321467509318167 56996620284482201263977251)
            ·
              refine ⟨85494930426723301895965877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56996620284482201263977251 85494930426723301895965877)
              ·
                refine ⟨8015149727505309552746801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85494930426723301895965877 8015149727505309552746801)
                ·
                  refine ⟨6011362295628982164560101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8015149727505309552746801 6011362295628982164560101)
                  ·
                    refine ⟨1127130430430434155855019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011362295628982164560101 1127130430430434155855019)
                    ·
                      rfl

theorem cell23_6585236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_6585236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585236 prefixEnd_6585236 := by exact prefixLift 6585236
  have htrace : WordTrace (prefixWord ++ tailWord_6585236) baseStart_6585236 baseEnd_6585236 := by
    simpa [prefixWord, tailWord_6585236, baseEnd_6585236] using wordTrace_append hprefix tailTrace_6585236
  have hstable : (prefixWord ++ tailWord_6585236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585236).length < 2 ^ (prefixWord ++ tailWord_6585236).sum := by decide
  have hdescent : baseEnd_6585236 < baseStart_6585236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585239 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_6585239 : Nat := 118140960795 + 6585239 * 2 ^ 59
def prefixEnd_6585239 : Nat := 4983230072969 + 3 ^ 40 * 6585239 * 2
def baseEnd_6585239 : Nat := 3381392831733265955827543

theorem tailTrace_6585239 : CollatzResearch.WordTrace tailWord_6585239 prefixEnd_6585239 3381392831733265955827543 := by
  unfold tailWord_6585239
  simp only [CollatzResearch.WordTrace]
  refine ⟨240183398189811247126814771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160122265459874164751209847 240183398189811247126814771)
  ·
    refine ⟨360275097284716870690222157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240183398189811247126814771 360275097284716870690222157)
    ·
      refine ⟨135103161481768826508833309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360275097284716870690222157 135103161481768826508833309)
      ·
        refine ⟨50663685555663309940812491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135103161481768826508833309 50663685555663309940812491)
        ·
          refine ⟨75995528333494964911218737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50663685555663309940812491 75995528333494964911218737)
          ·
            refine ⟨56996646250121223683414053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75995528333494964911218737 56996646250121223683414053)
            ·
              refine ⟨10686871171897729440640135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56996646250121223683414053 10686871171897729440640135)
              ·
                refine ⟨16030306757846594160960203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686871171897729440640135 16030306757846594160960203)
                ·
                  refine ⟨24045460136769891241440305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16030306757846594160960203 24045460136769891241440305)
                  ·
                    refine ⟨18034095102577418431080229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24045460136769891241440305 18034095102577418431080229)
                    ·
                      refine ⟨3381392831733265955827543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18034095102577418431080229 3381392831733265955827543)
                      ·
                        rfl

theorem cell23_6585239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_6585239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585239 prefixEnd_6585239 := by exact prefixLift 6585239
  have htrace : WordTrace (prefixWord ++ tailWord_6585239) baseStart_6585239 baseEnd_6585239 := by
    simpa [prefixWord, tailWord_6585239, baseEnd_6585239] using wordTrace_append hprefix tailTrace_6585239
  have hstable : (prefixWord ++ tailWord_6585239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585239).length < 2 ^ (prefixWord ++ tailWord_6585239).sum := by decide
  have hdescent : baseEnd_6585239 < baseStart_6585239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585259 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 3]
def baseStart_6585259 : Nat := 118140960795 + 6585259 * 2 ^ 59
def prefixEnd_6585259 : Nat := 4983230072969 + 3 ^ 40 * 6585259 * 2
def baseEnd_6585259 : Nat := 3381403101346355877577451

theorem tailTrace_6585259 : CollatzResearch.WordTrace tailWord_6585259 prefixEnd_6585259 3381403101346355877577451 := by
  unfold tailWord_6585259
  simp only [CollatzResearch.WordTrace]
  refine ⟨240184127649738790542542831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160122751766492527028361887 240184127649738790542542831)
  ·
    refine ⟨360276191474608185813814247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240184127649738790542542831 360276191474608185813814247)
    ·
      refine ⟨540414287211912278720721371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360276191474608185813814247 540414287211912278720721371)
      ·
        refine ⟨810621430817868418081082057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540414287211912278720721371 810621430817868418081082057)
        ·
          refine ⟨607966073113401313560811543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810621430817868418081082057 607966073113401313560811543)
          ·
            refine ⟨911949109670101970341217315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607966073113401313560811543 911949109670101970341217315)
            ·
              refine ⟨1367923664505152955511825973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911949109670101970341217315 1367923664505152955511825973)
              ·
                refine ⟨128242843547358089579233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367923664505152955511825973 128242843547358089579233685)
                ·
                  refine ⟨6011383291282410449026579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128242843547358089579233685 6011383291282410449026579)
                  ·
                    refine ⟨9017074936923615673539869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011383291282410449026579 9017074936923615673539869)
                    ·
                      refine ⟨3381403101346355877577451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9017074936923615673539869 3381403101346355877577451)
                      ·
                        rfl

theorem cell23_6585259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 3].length) (baseStart_6585259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585259 prefixEnd_6585259 := by exact prefixLift 6585259
  have htrace : WordTrace (prefixWord ++ tailWord_6585259) baseStart_6585259 baseEnd_6585259 := by
    simpa [prefixWord, tailWord_6585259, baseEnd_6585259] using wordTrace_append hprefix tailTrace_6585259
  have hstable : (prefixWord ++ tailWord_6585259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585259).length < 2 ^ (prefixWord ++ tailWord_6585259).sum := by decide
  have hdescent : baseEnd_6585259 < baseStart_6585259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585319 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6585319 : Nat := 118140960795 + 6585319 * 2 ^ 59
def prefixEnd_6585319 : Nat := 4983230072969 + 3 ^ 40 * 6585319 * 2
def baseEnd_6585319 : Nat := 3381433910185625642827175

theorem tailTrace_6585319 : CollatzResearch.WordTrace tailWord_6585319 prefixEnd_6585319 3381433910185625642827175 := by
  unfold tailWord_6585319
  simp only [CollatzResearch.WordTrace]
  refine ⟨240186316029521420789727011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160124210686347613859818007 240186316029521420789727011)
  ·
    refine ⟨360279474044282131184590517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240186316029521420789727011 360279474044282131184590517)
    ·
      refine ⟨33776200691651449798555361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 360279474044282131184590517 33776200691651449798555361)
      ·
        refine ⟨25332150518738587348916521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33776200691651449798555361 25332150518738587348916521)
        ·
          refine ⟨18999112889053940511687391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25332150518738587348916521 18999112889053940511687391)
          ·
            refine ⟨28498669333580910767531087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18999112889053940511687391 28498669333580910767531087)
            ·
              refine ⟨42748004000371366151296631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28498669333580910767531087 42748004000371366151296631)
              ·
                refine ⟨64122006000557049226944947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42748004000371366151296631 64122006000557049226944947)
                ·
                  refine ⟨96183009000835573840417421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64122006000557049226944947 96183009000835573840417421)
                  ·
                    refine ⟨36068628375313340190156533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96183009000835573840417421 36068628375313340190156533)
                    ·
                      refine ⟨3381433910185625642827175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36068628375313340190156533 3381433910185625642827175)
                      ·
                        rfl

theorem cell23_6585319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6585319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585319 prefixEnd_6585319 := by exact prefixLift 6585319
  have htrace : WordTrace (prefixWord ++ tailWord_6585319) baseStart_6585319 baseEnd_6585319 := by
    simpa [prefixWord, tailWord_6585319, baseEnd_6585319] using wordTrace_append hprefix tailTrace_6585319
  have hstable : (prefixWord ++ tailWord_6585319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585319).length < 2 ^ (prefixWord ++ tailWord_6585319).sum := by decide
  have hdescent : baseEnd_6585319 < baseStart_6585319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585349 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_6585349 : Nat := 118140960795 + 6585349 * 2 ^ 59
def prefixEnd_6585349 : Nat := 4983230072969 + 3 ^ 40 * 6585349 * 2
def baseEnd_6585349 : Nat := 3381449314605260525452037

theorem tailTrace_6585349 : CollatzResearch.WordTrace tailWord_6585349 prefixEnd_6585349 3381449314605260525452037 := by
  unfold tailWord_6585349
  simp only [CollatzResearch.WordTrace]
  refine ⟨240187410219412735913319101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160124940146275157275546067 240187410219412735913319101)
  ·
    refine ⟨90070278832279775967494663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240187410219412735913319101 90070278832279775967494663)
    ·
      refine ⟨135105418248419663951241995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90070278832279775967494663 135105418248419663951241995)
      ·
        refine ⟨202658127372629495926862993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135105418248419663951241995 202658127372629495926862993)
        ·
          refine ⟨151993595529472121945147245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202658127372629495926862993 151993595529472121945147245)
          ·
            refine ⟨56997598323552045729430217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151993595529472121945147245 56997598323552045729430217)
            ·
              refine ⟨42748198742664034297072663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56997598323552045729430217 42748198742664034297072663)
              ·
                refine ⟨64122298113996051445608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42748198742664034297072663 64122298113996051445608995)
                ·
                  refine ⟨96183447170994077168413493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64122298113996051445608995 96183447170994077168413493)
                  ·
                    refine ⟨9017198172280694734538765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96183447170994077168413493 9017198172280694734538765)
                    ·
                      refine ⟨3381449314605260525452037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9017198172280694734538765 3381449314605260525452037)
                      ·
                        rfl

theorem cell23_6585349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_6585349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585349 prefixEnd_6585349 := by exact prefixLift 6585349
  have htrace : WordTrace (prefixWord ++ tailWord_6585349) baseStart_6585349 baseEnd_6585349 := by
    simpa [prefixWord, tailWord_6585349, baseEnd_6585349] using wordTrace_append hprefix tailTrace_6585349
  have hstable : (prefixWord ++ tailWord_6585349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585349).length < 2 ^ (prefixWord ++ tailWord_6585349).sum := by decide
  have hdescent : baseEnd_6585349 < baseStart_6585349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585369 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_6585369 : Nat := 118140960795 + 6585369 * 2 ^ 59
def prefixEnd_6585369 : Nat := 4983230072969 + 3 ^ 40 * 6585369 * 2
def baseEnd_6585369 : Nat := 1127153194739450149067315

theorem tailTrace_6585369 : CollatzResearch.WordTrace tailWord_6585369 prefixEnd_6585369 1127153194739450149067315 := by
  unfold tailWord_6585369
  simp only [CollatzResearch.WordTrace]
  refine ⟨240188139679340279329047161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160125426452893519552698107 240188139679340279329047161)
  ·
    refine ⟨180141104759505209496785371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240188139679340279329047161 180141104759505209496785371)
    ·
      refine ⟨270211657139257814245178057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180141104759505209496785371 270211657139257814245178057)
      ·
        refine ⟨202658742854443360683883543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270211657139257814245178057 202658742854443360683883543)
        ·
          refine ⟨303988114281665041025825315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202658742854443360683883543 303988114281665041025825315)
          ·
            refine ⟨455982171422497561538737973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303988114281665041025825315 455982171422497561538737973)
            ·
              refine ⟨42748328570859146394256685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 455982171422497561538737973 42748328570859146394256685)
              ·
                refine ⟨16030623214072179897846257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42748328570859146394256685 16030623214072179897846257)
                ·
                  refine ⟨12022967410554134923384693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16030623214072179897846257 12022967410554134923384693)
                  ·
                    refine ⟨1127153194739450149067315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12022967410554134923384693 1127153194739450149067315)
                    ·
                      rfl

theorem cell23_6585369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_6585369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585369 prefixEnd_6585369 := by exact prefixLift 6585369
  have htrace : WordTrace (prefixWord ++ tailWord_6585369) baseStart_6585369 baseEnd_6585369 := by
    simpa [prefixWord, tailWord_6585369, baseEnd_6585369] using wordTrace_append hprefix tailTrace_6585369
  have hstable : (prefixWord ++ tailWord_6585369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585369).length < 2 ^ (prefixWord ++ tailWord_6585369).sum := by decide
  have hdescent : baseEnd_6585369 < baseStart_6585369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585379 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_6585379 : Nat := 118140960795 + 6585379 * 2 ^ 59
def prefixEnd_6585379 : Nat := 4983230072969 + 3 ^ 40 * 6585379 * 2
def baseEnd_6585379 : Nat := 3381464719024895408076899

theorem tailTrace_6585379 : CollatzResearch.WordTrace tailWord_6585379 prefixEnd_6585379 3381464719024895408076899 := by
  unfold tailWord_6585379
  simp only [CollatzResearch.WordTrace]
  refine ⟨240188504409304051036911191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160125669606202700691274127 240188504409304051036911191)
  ·
    refine ⟨360282756613956076555366787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240188504409304051036911191 360282756613956076555366787)
    ·
      refine ⟨540424134920934114833050181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360282756613956076555366787 540424134920934114833050181)
      ·
        refine ⟨101329525297675146531196909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 540424134920934114833050181 101329525297675146531196909)
        ·
          refine ⟨37998571986628179949198841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101329525297675146531196909 37998571986628179949198841)
          ·
            refine ⟨28498928989971134961899131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37998571986628179949198841 28498928989971134961899131)
            ·
              refine ⟨42748393484956702442848697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28498928989971134961899131 42748393484956702442848697)
              ·
                refine ⟨32061295113717526832136523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42748393484956702442848697 32061295113717526832136523)
                ·
                  refine ⟨48091942670576290248204785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32061295113717526832136523 48091942670576290248204785)
                  ·
                    refine ⟨36068957002932217686153589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48091942670576290248204785 36068957002932217686153589)
                    ·
                      refine ⟨3381464719024895408076899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36068957002932217686153589 3381464719024895408076899)
                      ·
                        rfl

theorem cell23_6585379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_6585379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585379 prefixEnd_6585379 := by exact prefixLift 6585379
  have htrace : WordTrace (prefixWord ++ tailWord_6585379) baseStart_6585379 baseEnd_6585379 := by
    simpa [prefixWord, tailWord_6585379, baseEnd_6585379] using wordTrace_append hprefix tailTrace_6585379
  have hstable : (prefixWord ++ tailWord_6585379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585379).length < 2 ^ (prefixWord ++ tailWord_6585379).sum := by decide
  have hdescent : baseEnd_6585379 < baseStart_6585379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585416 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_6585416 : Nat := 118140960795 + 6585416 * 2 ^ 59
def prefixEnd_6585416 : Nat := 4983230072969 + 3 ^ 40 * 6585416 * 2
def baseEnd_6585416 : Nat := 1127161239269703921104743

theorem tailTrace_6585416 : CollatzResearch.WordTrace tailWord_6585416 prefixEnd_6585416 1127161239269703921104743 := by
  unfold tailWord_6585416
  simp only [CollatzResearch.WordTrace]
  refine ⟨120094926955085003178004051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160126569273446670904005401 120094926955085003178004051)
  ·
    refine ⟨180142390432627504767006077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120094926955085003178004051 180142390432627504767006077)
    ·
      refine ⟨67553396412235314287627279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180142390432627504767006077 67553396412235314287627279)
      ·
        refine ⟨101330094618352971431440919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67553396412235314287627279 101330094618352971431440919)
        ·
          refine ⟨151995141927529457147161379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101330094618352971431440919 151995141927529457147161379)
          ·
            refine ⟨227992712891294185720742069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151995141927529457147161379 227992712891294185720742069)
            ·
              refine ⟨21374316833558829911319569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227992712891294185720742069 21374316833558829911319569)
              ·
                refine ⟨16030737625169122433489677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21374316833558829911319569 16030737625169122433489677)
                ·
                  refine ⟨6011526609438420912558629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16030737625169122433489677 6011526609438420912558629)
                  ·
                    refine ⟨1127161239269703921104743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011526609438420912558629 1127161239269703921104743)
                    ·
                      rfl

theorem cell23_6585416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_6585416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585416 prefixEnd_6585416 := by exact prefixLift 6585416
  have htrace : WordTrace (prefixWord ++ tailWord_6585416) baseStart_6585416 baseEnd_6585416 := by
    simpa [prefixWord, tailWord_6585416, baseEnd_6585416] using wordTrace_append hprefix tailTrace_6585416
  have hstable : (prefixWord ++ tailWord_6585416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585416).length < 2 ^ (prefixWord ++ tailWord_6585416).sum := by decide
  have hdescent : baseEnd_6585416 < baseStart_6585416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585429 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 8]
def baseStart_6585429 : Nat := 118140960795 + 6585429 * 2 ^ 59
def prefixEnd_6585429 : Nat := 4983230072969 + 3 ^ 40 * 6585429 * 2
def baseEnd_6585429 : Nat := 375721154784180023605741

theorem tailTrace_6585429 : CollatzResearch.WordTrace tailWord_6585429 prefixEnd_6585429 375721154784180023605741 := by
  unfold tailWord_6585429
  simp only [CollatzResearch.WordTrace]
  refine ⟨240190328059122909576231341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160126885372748606384154227 240190328059122909576231341)
  ·
    refine ⟨90071373022171091091086753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240190328059122909576231341 90071373022171091091086753)
    ·
      refine ⟨67553529766628318318315065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90071373022171091091086753 67553529766628318318315065)
      ·
        refine ⟨50665147324971238738736299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67553529766628318318315065 50665147324971238738736299)
        ·
          refine ⟨75997720987456858108104449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50665147324971238738736299 75997720987456858108104449)
          ·
            refine ⟨56998290740592643581078337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75997720987456858108104449 56998290740592643581078337)
            ·
              refine ⟨42748718055444482685808753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56998290740592643581078337 42748718055444482685808753)
              ·
                refine ⟨32061538541583362014356565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42748718055444482685808753 32061538541583362014356565)
                ·
                  refine ⟨375721154784180023605741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32061538541583362014356565 375721154784180023605741)
                  ·
                    rfl

theorem cell23_6585429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_6585429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585429 prefixEnd_6585429 := by exact prefixLift 6585429
  have htrace : WordTrace (prefixWord ++ tailWord_6585429) baseStart_6585429 baseEnd_6585429 := by
    simpa [prefixWord, tailWord_6585429, baseEnd_6585429] using wordTrace_append hprefix tailTrace_6585429
  have hstable : (prefixWord ++ tailWord_6585429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585429).length < 2 ^ (prefixWord ++ tailWord_6585429).sum := by decide
  have hdescent : baseEnd_6585429 < baseStart_6585429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585449 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_6585449 : Nat := 118140960795 + 6585449 * 2 ^ 59
def prefixEnd_6585449 : Nat := 4983230072969 + 3 ^ 40 * 6585449 * 2
def baseEnd_6585449 : Nat := 3381500662670710134201577

theorem tailTrace_6585449 : CollatzResearch.WordTrace tailWord_6585449 prefixEnd_6585449 3381500662670710134201577 := by
  unfold tailWord_6585449
  simp only [CollatzResearch.WordTrace]
  refine ⟨240191057519050452991959401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160127371679366968661306267 240191057519050452991959401)
  ·
    refine ⟨180143293139287839743969551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240191057519050452991959401 180143293139287839743969551)
    ·
      refine ⟨270214939708931759615954327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180143293139287839743969551 270214939708931759615954327)
      ·
        refine ⟨405322409563397639423931491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270214939708931759615954327 405322409563397639423931491)
        ·
          refine ⟨607983614345096459135897237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405322409563397639423931491 607983614345096459135897237)
          ·
            refine ⟨28499231922426396521995183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 607983614345096459135897237 28499231922426396521995183)
            ·
              refine ⟨42748847883639594782992775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28499231922426396521995183 42748847883639594782992775)
              ·
                refine ⟨64123271825459392174489163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42748847883639594782992775 64123271825459392174489163)
                ·
                  refine ⟨96184907738189088261733745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64123271825459392174489163 96184907738189088261733745)
                  ·
                    refine ⟨72138680803641816196300309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96184907738189088261733745 72138680803641816196300309)
                    ·
                      refine ⟨3381500662670710134201577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72138680803641816196300309 3381500662670710134201577)
                      ·
                        rfl

theorem cell23_6585449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_6585449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585449 prefixEnd_6585449 := by exact prefixLift 6585449
  have htrace : WordTrace (prefixWord ++ tailWord_6585449) baseStart_6585449 baseEnd_6585449 := by
    simpa [prefixWord, tailWord_6585449, baseEnd_6585449] using wordTrace_append hprefix tailTrace_6585449
  have hstable : (prefixWord ++ tailWord_6585449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585449).length < 2 ^ (prefixWord ++ tailWord_6585449).sum := by decide
  have hdescent : baseEnd_6585449 < baseStart_6585449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585450 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_6585450 : Nat := 118140960795 + 6585450 * 2 ^ 59
def prefixEnd_6585450 : Nat := 4983230072969 + 3 ^ 40 * 6585450 * 2
def baseEnd_6585450 : Nat := 1127167058717121543429691

theorem tailTrace_6585450 : CollatzResearch.WordTrace tailWord_6585450 prefixEnd_6585450 1127167058717121543429691 := by
  unfold tailWord_6585450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60047773498011707540686451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160127395994697886775163869 60047773498011707540686451)
  ·
    refine ⟨90071660247017561311029677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60047773498011707540686451 90071660247017561311029677)
    ·
      refine ⟨33776872592631585491636129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90071660247017561311029677 33776872592631585491636129)
      ·
        refine ⟨25332654444473689118727097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33776872592631585491636129 25332654444473689118727097)
        ·
          refine ⟨18999490833355266839045323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25332654444473689118727097 18999490833355266839045323)
          ·
            refine ⟨28499236250032900258567985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18999490833355266839045323 28499236250032900258567985)
            ·
              refine ⟨21374427187524675193925989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28499236250032900258567985 21374427187524675193925989)
              ·
                refine ⟨4007705097660876598861123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21374427187524675193925989 4007705097660876598861123)
                ·
                  refine ⟨6011557646491314898291685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007705097660876598861123 6011557646491314898291685)
                  ·
                    refine ⟨1127167058717121543429691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011557646491314898291685 1127167058717121543429691)
                    ·
                      rfl

theorem cell23_6585450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_6585450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585450 prefixEnd_6585450 := by exact prefixLift 6585450
  have htrace : WordTrace (prefixWord ++ tailWord_6585450) baseStart_6585450 baseEnd_6585450 := by
    simpa [prefixWord, tailWord_6585450, baseEnd_6585450] using wordTrace_append hprefix tailTrace_6585450
  have hstable : (prefixWord ++ tailWord_6585450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585450).length < 2 ^ (prefixWord ++ tailWord_6585450).sum := by decide
  have hdescent : baseEnd_6585450 < baseStart_6585450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585500 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6585500 : Nat := 118140960795 + 6585500 * 2 ^ 59
def prefixEnd_6585500 : Nat := 4983230072969 + 3 ^ 40 * 6585500 * 2
def baseEnd_6585500 : Nat := 3381526850184089434663843

theorem tailTrace_6585500 : CollatzResearch.WordTrace tailWord_6585500 prefixEnd_6585500 3381526850184089434663843 := by
  unfold tailWord_6585500
  simp only [CollatzResearch.WordTrace]
  refine ⟨120096458820932844351032977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160128611761243792468043969 120096458820932844351032977)
  ·
    refine ⟨90072344115699633263274733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120096458820932844351032977 90072344115699633263274733)
    ·
      refine ⟨33777129043387362473728025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90072344115699633263274733 33777129043387362473728025)
      ·
        refine ⟨25332846782540521855296019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33777129043387362473728025 25332846782540521855296019)
        ·
          refine ⟨37999270173810782782944029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25332846782540521855296019 37999270173810782782944029)
          ·
            refine ⟨14249726315179043543604011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37999270173810782782944029 14249726315179043543604011)
            ·
              refine ⟨21374589472768565315406017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14249726315179043543604011 21374589472768565315406017)
              ·
                refine ⟨16030942104576423986554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21374589472768565315406017 16030942104576423986554513)
                ·
                  refine ⟨12023206578432317989915885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16030942104576423986554513 12023206578432317989915885)
                  ·
                    refine ⟨4508702466912119246218457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12023206578432317989915885 4508702466912119246218457)
                    ·
                      refine ⟨3381526850184089434663843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508702466912119246218457 3381526850184089434663843)
                      ·
                        rfl

theorem cell23_6585500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6585500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585500 prefixEnd_6585500 := by exact prefixLift 6585500
  have htrace : WordTrace (prefixWord ++ tailWord_6585500) baseStart_6585500 baseEnd_6585500 := by
    simpa [prefixWord, tailWord_6585500, baseEnd_6585500] using wordTrace_append hprefix tailTrace_6585500
  have hstable : (prefixWord ++ tailWord_6585500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585500).length < 2 ^ (prefixWord ++ tailWord_6585500).sum := by decide
  have hdescent : baseEnd_6585500 < baseStart_6585500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585513 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 9, 2, 2]
def baseStart_6585513 : Nat := 118140960795 + 6585513 * 2 ^ 59
def prefixEnd_6585513 : Nat := 4983230072969 + 3 ^ 40 * 6585513 * 2
def baseEnd_6585513 : Nat := 3381533525432597883801283

theorem tailTrace_6585513 : CollatzResearch.WordTrace tailWord_6585513 prefixEnd_6585513 3381533525432597883801283 := by
  unfold tailWord_6585513
  simp only [CollatzResearch.WordTrace]
  refine ⟨240193391790818591922289193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160128927860545727948192795 240193391790818591922289193)
  ·
    refine ⟨180145043843113943941716895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240193391790818591922289193 180145043843113943941716895)
    ·
      refine ⟨270217565764670915912575343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180145043843113943941716895 270217565764670915912575343)
      ·
        refine ⟨405326348647006373868863015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270217565764670915912575343 405326348647006373868863015)
        ·
          refine ⟨607989522970509560803294523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405326348647006373868863015 607989522970509560803294523)
          ·
            refine ⟨911984284455764341204941785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607989522970509560803294523 911984284455764341204941785)
            ·
              refine ⟨683988213341823255903706339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911984284455764341204941785 683988213341823255903706339)
              ·
                refine ⟨1025982320012734883855559509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683988213341823255903706339 1025982320012734883855559509)
                ·
                  refine ⟨6011615156324618460091169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1025982320012734883855559509 6011615156324618460091169)
                  ·
                    refine ⟨4508711367243463845068377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6011615156324618460091169 4508711367243463845068377)
                    ·
                      refine ⟨3381533525432597883801283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508711367243463845068377 3381533525432597883801283)
                      ·
                        rfl

theorem cell23_6585513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2, 2].length) (baseStart_6585513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585513 prefixEnd_6585513 := by exact prefixLift 6585513
  have htrace : WordTrace (prefixWord ++ tailWord_6585513) baseStart_6585513 baseEnd_6585513 := by
    simpa [prefixWord, tailWord_6585513, baseEnd_6585513] using wordTrace_append hprefix tailTrace_6585513
  have hstable : (prefixWord ++ tailWord_6585513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585513).length < 2 ^ (prefixWord ++ tailWord_6585513).sum := by decide
  have hdescent : baseEnd_6585513 < baseStart_6585513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585519 : List Nat := [1, 1, 2, 1, 2, 3, 3, 10]
def baseStart_6585519 : Nat := 118140960795 + 6585519 * 2 ^ 59
def prefixEnd_6585519 : Nat := 4983230072969 + 3 ^ 40 * 6585519 * 2
def baseEnd_6585519 : Nat := 125242096530241661493565

theorem tailTrace_6585519 : CollatzResearch.WordTrace tailWord_6585519 prefixEnd_6585519 125242096530241661493565 := by
  unfold tailWord_6585519
  simp only [CollatzResearch.WordTrace]
  refine ⟨240193610628796854947007611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160129073752531236631338407 240193610628796854947007611)
  ·
    refine ⟨360290415943195282420511417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240193610628796854947007611 360290415943195282420511417)
    ·
      refine ⟨270217811957396461815383563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360290415943195282420511417 270217811957396461815383563)
      ·
        refine ⟨405326717936094692723075345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270217811957396461815383563 405326717936094692723075345)
        ·
          refine ⟨303995038452071019542306509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405326717936094692723075345 303995038452071019542306509)
          ·
            refine ⟨113998139419526632328364941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303995038452071019542306509 113998139419526632328364941)
            ·
              refine ⟨42749302282322487123136853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113998139419526632328364941 42749302282322487123136853)
              ·
                refine ⟨125242096530241661493565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42749302282322487123136853 125242096530241661493565)
                ·
                  rfl

theorem cell23_6585519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 10].length) (baseStart_6585519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585519 prefixEnd_6585519 := by exact prefixLift 6585519
  have htrace : WordTrace (prefixWord ++ tailWord_6585519) baseStart_6585519 baseEnd_6585519 := by
    simpa [prefixWord, tailWord_6585519, baseEnd_6585519] using wordTrace_append hprefix tailTrace_6585519
  have hstable : (prefixWord ++ tailWord_6585519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585519).length < 2 ^ (prefixWord ++ tailWord_6585519).sum := by decide
  have hdescent : baseEnd_6585519 < baseStart_6585519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585550 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_6585550 : Nat := 118140960795 + 6585550 * 2 ^ 59
def prefixEnd_6585550 : Nat := 4983230072969 + 3 ^ 40 * 6585550 * 2
def baseEnd_6585550 : Nat := 3381552524216814239038613

theorem tailTrace_6585550 : CollatzResearch.WordTrace tailWord_6585550 prefixEnd_6585550 3381552524216814239038613 := by
  unfold tailWord_6585550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024342661460568405173263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160129827527789698160924069 30024342661460568405173263)
  ·
    refine ⟨45036513992190852607759895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30024342661460568405173263 45036513992190852607759895)
    ·
      refine ⟨67554770988286278911639843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45036513992190852607759895 67554770988286278911639843)
      ·
        refine ⟨101332156482429418367459765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67554770988286278911639843 101332156482429418367459765)
        ·
          refine ⟨9499889670227757971949353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101332156482429418367459765 9499889670227757971949353)
          ·
            refine ⟨7124917252670818478962015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499889670227757971949353 7124917252670818478962015)
            ·
              refine ⟨10687375879006227718443023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124917252670818478962015 10687375879006227718443023)
              ·
                refine ⟨16031063818509341577664535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10687375879006227718443023 16031063818509341577664535)
                ·
                  refine ⟨24046595727764012366496803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16031063818509341577664535 24046595727764012366496803)
                  ·
                    refine ⟨36069893591646018549745205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24046595727764012366496803 36069893591646018549745205)
                    ·
                      refine ⟨3381552524216814239038613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36069893591646018549745205 3381552524216814239038613)
                      ·
                        rfl

theorem cell23_6585550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_6585550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585550 prefixEnd_6585550 := by exact prefixLift 6585550
  have htrace : WordTrace (prefixWord ++ tailWord_6585550) baseStart_6585550 baseEnd_6585550 := by
    simpa [prefixWord, tailWord_6585550, baseEnd_6585550] using wordTrace_append hprefix tailTrace_6585550
  have hstable : (prefixWord ++ tailWord_6585550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585550).length < 2 ^ (prefixWord ++ tailWord_6585550).sum := by decide
  have hdescent : baseEnd_6585550 < baseStart_6585550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585558 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6585558 : Nat := 118140960795 + 6585558 * 2 ^ 59
def prefixEnd_6585558 : Nat := 4983230072969 + 3 ^ 40 * 6585558 * 2
def baseEnd_6585558 : Nat := 3381556632062050207738577

theorem tailTrace_6585558 : CollatzResearch.WordTrace tailWord_6585558 prefixEnd_6585558 3381556632062050207738577 := by
  unfold tailWord_6585558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012189567228472787979833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160130022050437043071784885 15012189567228472787979833)
  ·
    refine ⟨11259142175421354590984875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15012189567228472787979833 11259142175421354590984875)
    ·
      refine ⟨16888713263132031886477313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259142175421354590984875 16888713263132031886477313)
      ·
        refine ⟨12666534947349023914857985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16888713263132031886477313 12666534947349023914857985)
        ·
          refine ⟨9499901210511767936143489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12666534947349023914857985 9499901210511767936143489)
          ·
            refine ⟨7124925907883825952107617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499901210511767936143489 7124925907883825952107617)
            ·
              refine ⟨5343694430912869464080713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124925907883825952107617 5343694430912869464080713)
              ·
                refine ⟨4007770823184652098060535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343694430912869464080713 4007770823184652098060535)
                ·
                  refine ⟨6011656234776978147090803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007770823184652098060535 6011656234776978147090803)
                  ·
                    refine ⟨9017484352165467220636205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011656234776978147090803 9017484352165467220636205)
                    ·
                      refine ⟨3381556632062050207738577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9017484352165467220636205 3381556632062050207738577)
                      ·
                        rfl

theorem cell23_6585558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6585558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585558 prefixEnd_6585558 := by exact prefixLift 6585558
  have htrace : WordTrace (prefixWord ++ tailWord_6585558) baseStart_6585558 baseEnd_6585558 := by
    simpa [prefixWord, tailWord_6585558, baseEnd_6585558] using wordTrace_append hprefix tailTrace_6585558
  have hstable : (prefixWord ++ tailWord_6585558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585558).length < 2 ^ (prefixWord ++ tailWord_6585558).sum := by decide
  have hdescent : baseEnd_6585558 < baseStart_6585558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585580 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_6585580 : Nat := 118140960795 + 6585580 * 2 ^ 59
def prefixEnd_6585580 : Nat := 4983230072969 + 3 ^ 40 * 6585580 * 2
def baseEnd_6585580 : Nat := 3381567928636449121663475

theorem tailTrace_6585580 : CollatzResearch.WordTrace tailWord_6585580 prefixEnd_6585580 3381567928636449121663475 := by
  unfold tailWord_6585580
  simp only [CollatzResearch.WordTrace]
  refine ⟨120097917740787931182489097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160130556987717241576652129 120097917740787931182489097)
  ·
    refine ⟨90073438305590948386866823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120097917740787931182489097 90073438305590948386866823)
    ·
      refine ⟨135110157458386422580300235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90073438305590948386866823 135110157458386422580300235)
      ·
        refine ⟨202665236187579633870450353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135110157458386422580300235 202665236187579633870450353)
        ·
          refine ⟨151998927140684725402837765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202665236187579633870450353 151998927140684725402837765)
          ·
            refine ⟨28499798838878386013032081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151998927140684725402837765 28499798838878386013032081)
            ·
              refine ⟨21374849129158789509774061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28499798838878386013032081 21374849129158789509774061)
              ·
                refine ⟨8015568423434546066165273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21374849129158789509774061 8015568423434546066165273)
                ·
                  refine ⟨6011676317575909549623955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8015568423434546066165273 6011676317575909549623955)
                  ·
                    refine ⟨9017514476363864324435933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011676317575909549623955 9017514476363864324435933)
                    ·
                      refine ⟨3381567928636449121663475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9017514476363864324435933 3381567928636449121663475)
                      ·
                        rfl

theorem cell23_6585580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_6585580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585580 prefixEnd_6585580 := by exact prefixLift 6585580
  have htrace : WordTrace (prefixWord ++ tailWord_6585580) baseStart_6585580 baseEnd_6585580 := by
    simpa [prefixWord, tailWord_6585580, baseEnd_6585580] using wordTrace_append hprefix tailTrace_6585580
  have hstable : (prefixWord ++ tailWord_6585580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585580).length < 2 ^ (prefixWord ++ tailWord_6585580).sum := by decide
  have hdescent : baseEnd_6585580 < baseStart_6585580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585637 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_6585637 : Nat := 118140960795 + 6585637 * 2 ^ 59
def prefixEnd_6585637 : Nat := 4983230072969 + 3 ^ 40 * 6585637 * 2
def baseEnd_6585637 : Nat := 3381597197033755398650713

theorem tailTrace_6585637 : CollatzResearch.WordTrace tailWord_6585637 prefixEnd_6585637 3381597197033755398650713 := by
  unfold tailWord_6585637
  simp only [CollatzResearch.WordTrace]
  refine ⟨240197914442369361099803165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160131942961579574066535443 240197914442369361099803165)
  ·
    refine ⟨90074217915888510412426187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240197914442369361099803165 90074217915888510412426187)
    ·
      refine ⟨135111326873832765618639281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90074217915888510412426187 135111326873832765618639281)
      ·
        refine ⟨101333495155374574213979461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135111326873832765618639281 101333495155374574213979461)
        ·
          refine ⟨19000030341632732665121149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101333495155374574213979461 19000030341632732665121149)
          ·
            refine ⟨7125011378112274749420431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19000030341632732665121149 7125011378112274749420431)
            ·
              refine ⟨10687517067168412124130647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125011378112274749420431 10687517067168412124130647)
              ·
                refine ⟨16031275600752618186195971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10687517067168412124130647 16031275600752618186195971)
                ·
                  refine ⟨24046913401128927279293957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16031275600752618186195971 24046913401128927279293957)
                  ·
                    refine ⟨4508796262711673864867617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24046913401128927279293957 4508796262711673864867617)
                    ·
                      refine ⟨3381597197033755398650713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4508796262711673864867617 3381597197033755398650713)
                      ·
                        rfl

theorem cell23_6585637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_6585637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585637 prefixEnd_6585637 := by exact prefixLift 6585637
  have htrace : WordTrace (prefixWord ++ tailWord_6585637) baseStart_6585637 baseEnd_6585637 := by
    simpa [prefixWord, tailWord_6585637, baseEnd_6585637] using wordTrace_append hprefix tailTrace_6585637
  have hstable : (prefixWord ++ tailWord_6585637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585637).length < 2 ^ (prefixWord ++ tailWord_6585637).sum := by decide
  have hdescent : baseEnd_6585637 < baseStart_6585637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585660 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 5]
def baseStart_6585660 : Nat := 118140960795 + 6585660 * 2 ^ 59
def prefixEnd_6585660 : Nat := 4983230072969 + 3 ^ 40 * 6585660 * 2
def baseEnd_6585660 : Nat := 375734334120978756518123

theorem tailTrace_6585660 : CollatzResearch.WordTrace tailWord_6585660 prefixEnd_6585660 375734334120978756518123 := by
  unfold tailWord_6585660
  simp only [CollatzResearch.WordTrace]
  refine ⟨120099376660643018013945217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160132502214190690685260289 120099376660643018013945217)
  ·
    refine ⟨90074532495482263510458913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120099376660643018013945217 90074532495482263510458913)
    ·
      refine ⟨67555899371611697632844185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90074532495482263510458913 67555899371611697632844185)
      ·
        refine ⟨50666924528708773224633139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67555899371611697632844185 50666924528708773224633139)
        ·
          refine ⟨76000386793063159836949709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50666924528708773224633139 76000386793063159836949709)
          ·
            refine ⟨28500145047398684938856141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76000386793063159836949709 28500145047398684938856141)
            ·
              refine ⟨10687554392774506852071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28500145047398684938856141 10687554392774506852071053)
              ·
                refine ⟨4007832897290440069526645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10687554392774506852071053 4007832897290440069526645)
                ·
                  refine ⟨375734334120978756518123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007832897290440069526645 375734334120978756518123)
                  ·
                    rfl

theorem cell23_6585660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_6585660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585660 prefixEnd_6585660 := by exact prefixLift 6585660
  have htrace : WordTrace (prefixWord ++ tailWord_6585660) baseStart_6585660 baseEnd_6585660 := by
    simpa [prefixWord, tailWord_6585660, baseEnd_6585660] using wordTrace_append hprefix tailTrace_6585660
  have hstable : (prefixWord ++ tailWord_6585660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585660).length < 2 ^ (prefixWord ++ tailWord_6585660).sum := by decide
  have hdescent : baseEnd_6585660 < baseStart_6585660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585713 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_6585713 : Nat := 118140960795 + 6585713 * 2 ^ 59
def prefixEnd_6585713 : Nat := 4983230072969 + 3 ^ 40 * 6585713 * 2
def baseEnd_6585713 : Nat := 3381636221563497101300363

theorem tailTrace_6585713 : CollatzResearch.WordTrace tailWord_6585713 prefixEnd_6585713 3381636221563497101300363 := by
  unfold tailWord_6585713
  simp only [CollatzResearch.WordTrace]
  refine ⟨240200686390094026079569793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160133790926729350719713195 240200686390094026079569793)
  ·
    refine ⟨180150514792570519559677345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240200686390094026079569793 180150514792570519559677345)
    ·
      refine ⟨135112886094427889669758009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180150514792570519559677345 135112886094427889669758009)
      ·
        refine ⟨101334664570820917252318507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135112886094427889669758009 101334664570820917252318507)
        ·
          refine ⟨152001996856231375878477761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101334664570820917252318507 152001996856231375878477761)
          ·
            refine ⟨114001497642173531908858321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152001996856231375878477761 114001497642173531908858321)
            ·
              refine ⟨85501123231630148931643741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114001497642173531908858321 85501123231630148931643741)
              ·
                refine ⟨32062921211861305849366403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85501123231630148931643741 32062921211861305849366403)
                ·
                  refine ⟨48094381817791958774049605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32062921211861305849366403 48094381817791958774049605)
                  ·
                    refine ⟨9017696590835992270134301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48094381817791958774049605 9017696590835992270134301)
                    ·
                      refine ⟨3381636221563497101300363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9017696590835992270134301 3381636221563497101300363)
                      ·
                        rfl

theorem cell23_6585713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_6585713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585713 prefixEnd_6585713 := by exact prefixLift 6585713
  have htrace : WordTrace (prefixWord ++ tailWord_6585713) baseStart_6585713 baseEnd_6585713 := by
    simpa [prefixWord, tailWord_6585713, baseEnd_6585713] using wordTrace_append hprefix tailTrace_6585713
  have hstable : (prefixWord ++ tailWord_6585713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585713).length < 2 ^ (prefixWord ++ tailWord_6585713).sum := by decide
  have hdescent : baseEnd_6585713 < baseStart_6585713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585733 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 6]
def baseStart_6585733 : Nat := 118140960795 + 6585733 * 2 ^ 59
def prefixEnd_6585733 : Nat := 4983230072969 + 3 ^ 40 * 6585733 * 2
def baseEnd_6585733 : Nat := 375738499019620780338919

theorem tailTrace_6585733 : CollatzResearch.WordTrace tailWord_6585733 prefixEnd_6585733 375738499019620780338919 := by
  unfold tailWord_6585733
  simp only [CollatzResearch.WordTrace]
  refine ⟨240201415850021569495297853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160134277233347712996865235 240201415850021569495297853)
  ·
    refine ⟨90075530943758088560736695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240201415850021569495297853 90075530943758088560736695)
    ·
      refine ⟨135113296415637132841105043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90075530943758088560736695 135113296415637132841105043)
      ·
        refine ⟨202669944623455699261657565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135113296415637132841105043 202669944623455699261657565)
        ·
          refine ⟨76001229233795887223121587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202669944623455699261657565 76001229233795887223121587)
          ·
            refine ⟨114001843850693830834682381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76001229233795887223121587 114001843850693830834682381)
            ·
              refine ⟨42750691444010186563005893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114001843850693830834682381 42750691444010186563005893)
              ·
                refine ⟨8015754645751909980563605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42750691444010186563005893 8015754645751909980563605)
                ·
                  refine ⟨375738499019620780338919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8015754645751909980563605 375738499019620780338919)
                  ·
                    rfl

theorem cell23_6585733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_6585733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585733 prefixEnd_6585733 := by exact prefixLift 6585733
  have htrace : WordTrace (prefixWord ++ tailWord_6585733) baseStart_6585733 baseEnd_6585733 := by
    simpa [prefixWord, tailWord_6585733, baseEnd_6585733] using wordTrace_append hprefix tailTrace_6585733
  have hstable : (prefixWord ++ tailWord_6585733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585733).length < 2 ^ (prefixWord ++ tailWord_6585733).sum := by decide
  have hdescent : baseEnd_6585733 < baseStart_6585733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585763 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 3, 5]
def baseStart_6585763 : Nat := 118140960795 + 6585763 * 2 ^ 59
def prefixEnd_6585763 : Nat := 4983230072969 + 3 ^ 40 * 6585763 * 2
def baseEnd_6585763 : Nat := 1127220631865407301891711

theorem tailTrace_6585763 : CollatzResearch.WordTrace tailWord_6585763 prefixEnd_6585763 1127220631865407301891711 := by
  unfold tailWord_6585763
  simp only [CollatzResearch.WordTrace]
  refine ⟨240202510039912884618889943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160135006693275256412593295 240202510039912884618889943)
  ·
    refine ⟨360303765059869326928334915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240202510039912884618889943 360303765059869326928334915)
    ·
      refine ⟨540455647589803990392502373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360303765059869326928334915 540455647589803990392502373)
      ·
        refine ⟨101335433923088248198594195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 540455647589803990392502373 101335433923088248198594195)
        ·
          refine ⟨152003150884632372297891293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101335433923088248198594195 152003150884632372297891293)
          ·
            refine ⟨57001181581737139611709235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152003150884632372297891293 57001181581737139611709235)
            ·
              refine ⟨85501772372605709417563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57001181581737139611709235 85501772372605709417563853)
              ·
                refine ⟨32063164639727141031586445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85501772372605709417563853 32063164639727141031586445)
                ·
                  refine ⟨12023686739897677886844917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32063164639727141031586445 12023686739897677886844917)
                  ·
                    refine ⟨1127220631865407301891711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12023686739897677886844917 1127220631865407301891711)
                    ·
                      rfl

theorem cell23_6585763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].length) (baseStart_6585763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585763 prefixEnd_6585763 := by exact prefixLift 6585763
  have htrace : WordTrace (prefixWord ++ tailWord_6585763) baseStart_6585763 baseEnd_6585763 := by
    simpa [prefixWord, tailWord_6585763, baseEnd_6585763] using wordTrace_append hprefix tailTrace_6585763
  have hstable : (prefixWord ++ tailWord_6585763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585763).length < 2 ^ (prefixWord ++ tailWord_6585763).sum := by decide
  have hdescent : baseEnd_6585763 < baseStart_6585763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
