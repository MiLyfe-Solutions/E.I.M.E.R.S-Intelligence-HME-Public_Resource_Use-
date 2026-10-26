import V185TrunkScan21Chunk111

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1362050 : List Nat := [3, 4, 14]
def baseStart_1362050 : Nat := 118140960795 + 1362050 * 2 ^ 59
def prefixEnd_1362050 : Nat := 4983230072969 + 3 ^ 40 * 1362050 * 2
def baseEnd_1362050 : Nat := 426390078010365009487

theorem tailTrace_1362050 : CollatzResearch.WordTrace tailWord_1362050 prefixEnd_1362050 426390078010365009487 := by
  unfold tailWord_1362050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419511178883236116328901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33118696477021962976877069 12419511178883236116328901)
  ·
    refine ⟨2328658346040606771811669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12419511178883236116328901 2328658346040606771811669)
    ·
      refine ⟨426390078010365009487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2328658346040606771811669 426390078010365009487)
      ·
        rfl

theorem cell21_1362050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 14].length) (baseStart_1362050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362050 prefixEnd_1362050 := by exact prefixLift 1362050
  have htrace : WordTrace (prefixWord ++ tailWord_1362050) baseStart_1362050 baseEnd_1362050 := by
    simpa [prefixWord, tailWord_1362050, baseEnd_1362050] using wordTrace_append hprefix tailTrace_1362050
  have hstable : (prefixWord ++ tailWord_1362050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362050).length < 2 ^ (prefixWord ++ tailWord_1362050).sum := by decide
  have hdescent : baseEnd_1362050 < baseStart_1362050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362053 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_1362053 : Nat := 118140960795 + 1362053 * 2 ^ 59
def prefixEnd_1362053 : Nat := 4983230072969 + 3 ^ 40 * 1362053 * 2
def baseEnd_1362053 : Nat := 310839051510428753366017

theorem tailTrace_1362053 : CollatzResearch.WordTrace tailWord_1362053 prefixEnd_1362053 310839051510428753366017 := by
  unfold tailWord_1362053
  simp only [CollatzResearch.WordTrace]
  refine ⟨49678154134522075977674813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33118769423014717318449875 49678154134522075977674813)
  ·
    refine ⟨18629307800445778491628055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49678154134522075977674813 18629307800445778491628055)
    ·
      refine ⟨27943961700668667737442083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18629307800445778491628055 27943961700668667737442083)
      ·
        refine ⟨41915942551003001606163125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27943961700668667737442083 41915942551003001606163125)
        ·
          refine ⟨3929619614156531400577793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41915942551003001606163125 3929619614156531400577793)
          ·
            refine ⟨2947214710617398550433345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929619614156531400577793 2947214710617398550433345)
            ·
              refine ⟨2210411032963048912825009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947214710617398550433345 2210411032963048912825009)
              ·
                refine ⟨1657808274722286684618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210411032963048912825009 1657808274722286684618757)
                ·
                  refine ⟨310839051510428753366017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657808274722286684618757 310839051510428753366017)
                  ·
                    rfl

theorem cell21_1362053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_1362053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362053 prefixEnd_1362053 := by exact prefixLift 1362053
  have htrace : WordTrace (prefixWord ++ tailWord_1362053) baseStart_1362053 baseEnd_1362053 := by
    simpa [prefixWord, tailWord_1362053, baseEnd_1362053] using wordTrace_append hprefix tailTrace_1362053
  have hstable : (prefixWord ++ tailWord_1362053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362053).length < 2 ^ (prefixWord ++ tailWord_1362053).sum := by decide
  have hdescent : baseEnd_1362053 < baseStart_1362053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362056 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_1362056 : Nat := 118140960795 + 1362056 * 2 ^ 59
def prefixEnd_1362056 : Nat := 4983230072969 + 3 ^ 40 * 1362056 * 2
def baseEnd_1362056 : Nat := 310839736151301414816011

theorem tailTrace_1362056 : CollatzResearch.WordTrace tailWord_1362056 prefixEnd_1362056 310839736151301414816011 := by
  unfold tailWord_1362056
  simp only [CollatzResearch.WordTrace]
  refine ⟨24839131776755603745017011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33118842369007471660022681 24839131776755603745017011)
  ·
    refine ⟨37258697665133405617525517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24839131776755603745017011 37258697665133405617525517)
    ·
      refine ⟨13972011624425027106572069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37258697665133405617525517 13972011624425027106572069)
      ·
        refine ⟨2619752179579692582482263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13972011624425027106572069 2619752179579692582482263)
        ·
          refine ⟨3929628269369538873723395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619752179579692582482263 3929628269369538873723395)
          ·
            refine ⟨5894442404054308310585093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929628269369538873723395 5894442404054308310585093)
            ·
              refine ⟨1105207950760182808234705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5894442404054308310585093 1105207950760182808234705)
              ·
                refine ⟨828905963070137106176029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105207950760182808234705 828905963070137106176029)
                ·
                  refine ⟨310839736151301414816011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828905963070137106176029 310839736151301414816011)
                  ·
                    rfl

theorem cell21_1362056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_1362056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362056 prefixEnd_1362056 := by exact prefixLift 1362056
  have htrace : WordTrace (prefixWord ++ tailWord_1362056) baseStart_1362056 baseEnd_1362056 := by
    simpa [prefixWord, tailWord_1362056, baseEnd_1362056] using wordTrace_append hprefix tailTrace_1362056
  have hstable : (prefixWord ++ tailWord_1362056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362056).length < 2 ^ (prefixWord ++ tailWord_1362056).sum := by decide
  have hdescent : baseEnd_1362056 < baseStart_1362056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362081 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1362081 : Nat := 118140960795 + 1362081 * 2 ^ 59
def prefixEnd_1362081 : Nat := 4983230072969 + 3 ^ 40 * 1362081 * 2
def baseEnd_1362081 : Nat := 310845441491906926899293

theorem tailTrace_1362081 : CollatzResearch.WordTrace tailWord_1362081 prefixEnd_1362081 310845441491906926899293 := by
  unfold tailWord_1362081
  simp only [CollatzResearch.WordTrace]
  refine ⟨49679175378420636759694097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33119450252280424506462731 49679175378420636759694097)
  ·
    refine ⟨37259381533815477569770573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49679175378420636759694097 37259381533815477569770573)
    ·
      refine ⟨13972268075180804088663965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37259381533815477569770573 13972268075180804088663965)
      ·
        refine ⟨5239600528192801533248987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13972268075180804088663965 5239600528192801533248987)
        ·
          refine ⟨7859400792289202299873481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239600528192801533248987 7859400792289202299873481)
          ·
            refine ⟨5894550594216901724905111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859400792289202299873481 5894550594216901724905111)
            ·
              refine ⟨8841825891325352587357667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894550594216901724905111 8841825891325352587357667)
              ·
                refine ⟨13262738836988028881036501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8841825891325352587357667 13262738836988028881036501)
                ·
                  refine ⟨310845441491906926899293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13262738836988028881036501 310845441491906926899293)
                  ·
                    rfl

theorem cell21_1362081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1362081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362081 prefixEnd_1362081 := by exact prefixLift 1362081
  have htrace : WordTrace (prefixWord ++ tailWord_1362081) baseStart_1362081 baseEnd_1362081 := by
    simpa [prefixWord, tailWord_1362081, baseEnd_1362081] using wordTrace_append hprefix tailTrace_1362081
  have hstable : (prefixWord ++ tailWord_1362081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362081).length < 2 ^ (prefixWord ++ tailWord_1362081).sum := by decide
  have hdescent : baseEnd_1362081 < baseStart_1362081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362084 : List Nat := [2, 3, 1, 2, 4, 1, 3, 5]
def baseStart_1362084 : Nat := 118140960795 + 1362084 * 2 ^ 59
def prefixEnd_1362084 : Nat := 4983230072969 + 3 ^ 40 * 1362084 * 2
def baseEnd_1362084 : Nat := 103615375377593196116429

theorem tailTrace_1362084 : CollatzResearch.WordTrace tailWord_1362084 prefixEnd_1362084 103615375377593196116429 := by
  unfold tailWord_1362084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24839642398704884136026653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33119523198273178848035537 24839642398704884136026653)
  ·
    refine ⟨9314865899514331551009995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24839642398704884136026653 9314865899514331551009995)
    ·
      refine ⟨13972298849271497326514993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9314865899514331551009995 13972298849271497326514993)
      ·
        refine ⟨10479224136953622994886245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13972298849271497326514993 10479224136953622994886245)
        ·
          refine ⟨1964854525678804311541171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10479224136953622994886245 1964854525678804311541171)
          ·
            refine ⟨2947281788518206467311757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964854525678804311541171 2947281788518206467311757)
            ·
              refine ⟨1105230670694327425241909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2947281788518206467311757 1105230670694327425241909)
              ·
                refine ⟨103615375377593196116429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105230670694327425241909 103615375377593196116429)
                ·
                  rfl

theorem cell21_1362084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_1362084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362084 prefixEnd_1362084 := by exact prefixLift 1362084
  have htrace : WordTrace (prefixWord ++ tailWord_1362084) baseStart_1362084 baseEnd_1362084 := by
    simpa [prefixWord, tailWord_1362084, baseEnd_1362084] using wordTrace_append hprefix tailTrace_1362084
  have hstable : (prefixWord ++ tailWord_1362084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362084).length < 2 ^ (prefixWord ++ tailWord_1362084).sum := by decide
  have hdescent : baseEnd_1362084 < baseStart_1362084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362095 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_1362095 : Nat := 118140960795 + 1362095 * 2 ^ 59
def prefixEnd_1362095 : Nat := 4983230072969 + 3 ^ 40 * 1362095 * 2
def baseEnd_1362095 : Nat := 310848636482646013665931

theorem tailTrace_1362095 : CollatzResearch.WordTrace tailWord_1362095 prefixEnd_1362095 310848636482646013665931 := by
  unfold tailWord_1362095
  simp only [CollatzResearch.WordTrace]
  refine ⟨49679686000369917150703739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33119790666913278100469159 49679686000369917150703739)
  ·
    refine ⟨74519529000554875726055609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49679686000369917150703739 74519529000554875726055609)
    ·
      refine ⟨55889646750416156794541707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74519529000554875726055609 55889646750416156794541707)
      ·
        refine ⟨83834470125624235191812561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55889646750416156794541707 83834470125624235191812561)
        ·
          refine ⟨62875852594218176393859421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83834470125624235191812561 62875852594218176393859421)
          ·
            refine ⟨23578444722831816147697283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62875852594218176393859421 23578444722831816147697283)
            ·
              refine ⟨35367667084247724221545925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23578444722831816147697283 35367667084247724221545925)
              ·
                refine ⟨6631437578296448291539861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35367667084247724221545925 6631437578296448291539861)
                ·
                  refine ⟨310848636482646013665931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6631437578296448291539861 310848636482646013665931)
                  ·
                    rfl

theorem cell21_1362095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_1362095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362095 prefixEnd_1362095 := by exact prefixLift 1362095
  have htrace : WordTrace (prefixWord ++ tailWord_1362095) baseStart_1362095 baseEnd_1362095 := by
    simpa [prefixWord, tailWord_1362095, baseEnd_1362095] using wordTrace_append hprefix tailTrace_1362095
  have hstable : (prefixWord ++ tailWord_1362095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362095).length < 2 ^ (prefixWord ++ tailWord_1362095).sum := by decide
  have hdescent : baseEnd_1362095 < baseStart_1362095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362112 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_1362112 : Nat := 118140960795 + 1362112 * 2 ^ 59
def prefixEnd_1362112 : Nat := 4983230072969 + 3 ^ 40 * 1362112 * 2
def baseEnd_1362112 : Nat := 310852516114257761882563

theorem tailTrace_1362112 : CollatzResearch.WordTrace tailWord_1362112 prefixEnd_1362112 310852516114257761882563 := by
  unfold tailWord_1362112
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840153020654164527036295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33120204027538886036048393 24840153020654164527036295)
  ·
    refine ⟨37260229530981246790554443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24840153020654164527036295 37260229530981246790554443)
    ·
      refine ⟨55890344296471870185831665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37260229530981246790554443 55890344296471870185831665)
      ·
        refine ⟨41917758222353902639373749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55890344296471870185831665 41917758222353902639373749)
        ·
          refine ⟨3929789833345678372441289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41917758222353902639373749 3929789833345678372441289)
          ·
            refine ⟨2947342375009258779330967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929789833345678372441289 2947342375009258779330967)
            ·
              refine ⟨4421013562513888168996451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947342375009258779330967 4421013562513888168996451)
              ·
                refine ⟨6631520343770832253494677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421013562513888168996451 6631520343770832253494677)
                ·
                  refine ⟨310852516114257761882563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6631520343770832253494677 310852516114257761882563)
                  ·
                    rfl

theorem cell21_1362112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_1362112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362112 prefixEnd_1362112 := by exact prefixLift 1362112
  have htrace : WordTrace (prefixWord ++ tailWord_1362112) baseStart_1362112 baseEnd_1362112 := by
    simpa [prefixWord, tailWord_1362112, baseEnd_1362112] using wordTrace_append hprefix tailTrace_1362112
  have hstable : (prefixWord ++ tailWord_1362112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362112).length < 2 ^ (prefixWord ++ tailWord_1362112).sum := by decide
  have hdescent : baseEnd_1362112 < baseStart_1362112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362188 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1362188 : Nat := 118140960795 + 1362188 * 2 ^ 59
def prefixEnd_1362188 : Nat := 4983230072969 + 3 ^ 40 * 1362188 * 2
def baseEnd_1362188 : Nat := 310869860349698518615741

theorem tailTrace_1362188 : CollatzResearch.WordTrace tailWord_1362188 prefixEnd_1362188 310869860349698518615741 := by
  unfold tailWord_1362188
  simp only [CollatzResearch.WordTrace]
  refine ⟨24841538994516497016919609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33122051992688662689226145 24841538994516497016919609)
  ·
    refine ⟨18631154245887372762689707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24841538994516497016919609 18631154245887372762689707)
    ·
      refine ⟨27946731368831059144034561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18631154245887372762689707 27946731368831059144034561)
      ·
        refine ⟨20960048526623294358025921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27946731368831059144034561 20960048526623294358025921)
        ·
          refine ⟨15720036394967470768519441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20960048526623294358025921 15720036394967470768519441)
          ·
            refine ⟨11790027296225603076389581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15720036394967470768519441 11790027296225603076389581)
            ·
              refine ⟨4421260236084601153646093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11790027296225603076389581 4421260236084601153646093)
              ·
                refine ⟨1657972588531725432617285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4421260236084601153646093 1657972588531725432617285)
                ·
                  refine ⟨310869860349698518615741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657972588531725432617285 310869860349698518615741)
                  ·
                    rfl

theorem cell21_1362188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1362188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362188 prefixEnd_1362188 := by exact prefixLift 1362188
  have htrace : WordTrace (prefixWord ++ tailWord_1362188) baseStart_1362188 baseEnd_1362188 := by
    simpa [prefixWord, tailWord_1362188, baseEnd_1362188] using wordTrace_append hprefix tailTrace_1362188
  have hstable : (prefixWord ++ tailWord_1362188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362188).length < 2 ^ (prefixWord ++ tailWord_1362188).sum := by decide
  have hdescent : baseEnd_1362188 < baseStart_1362188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362225 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 3]
def baseStart_1362225 : Nat := 118140960795 + 1362225 * 2 ^ 59
def prefixEnd_1362225 : Nat := 4983230072969 + 3 ^ 40 * 1362225 * 2
def baseEnd_1362225 : Nat := 310878304253794676498999

theorem tailTrace_1362225 : CollatzResearch.WordTrace tailWord_1362225 prefixEnd_1362225 310878304253794676498999 := by
  unfold tailWord_1362225
  simp only [CollatzResearch.WordTrace]
  refine ⟨49684427489898949352936129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33122951659932632901957419 49684427489898949352936129)
  ·
    refine ⟨37263320617424212014702097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49684427489898949352936129 37263320617424212014702097)
    ·
      refine ⟨27947490463068159011026573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37263320617424212014702097 27947490463068159011026573)
      ·
        refine ⟨10480308923650559629134965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27947490463068159011026573 10480308923650559629134965)
        ·
          refine ⟨982528961592239965231403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10480308923650559629134965 982528961592239965231403)
          ·
            refine ⟨1473793442388359947847105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982528961592239965231403 1473793442388359947847105)
            ·
              refine ⟨1105345081791269960885329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473793442388359947847105 1105345081791269960885329)
              ·
                refine ⟨829008811343452470663997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105345081791269960885329 829008811343452470663997)
                ·
                  refine ⟨310878304253794676498999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829008811343452470663997 310878304253794676498999)
                  ·
                    rfl

theorem cell21_1362225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_1362225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362225 prefixEnd_1362225 := by exact prefixLift 1362225
  have htrace : WordTrace (prefixWord ++ tailWord_1362225) baseStart_1362225 baseEnd_1362225 := by
    simpa [prefixWord, tailWord_1362225, baseEnd_1362225] using wordTrace_append hprefix tailTrace_1362225
  have hstable : (prefixWord ++ tailWord_1362225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362225).length < 2 ^ (prefixWord ++ tailWord_1362225).sum := by decide
  have hdescent : baseEnd_1362225 < baseStart_1362225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362270 : List Nat := [4, 4, 2, 1, 1, 1, 8]
def baseStart_1362270 : Nat := 118140960795 + 1362270 * 2 ^ 59
def prefixEnd_1362270 : Nat := 4983230072969 + 3 ^ 40 * 1362270 * 2
def baseEnd_1362270 : Nat := 34543174874098288694323

theorem tailTrace_1362270 : CollatzResearch.WordTrace tailWord_1362270 prefixEnd_1362270 34543174874098288694323 := by
  unfold tailWord_1362270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210758596841990254790533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33124045849823948025549509 6210758596841990254790533)
  ·
    refine ⟨1164517236907873172773225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6210758596841990254790533 1164517236907873172773225)
    ·
      refine ⟨873387927680904879579919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164517236907873172773225 873387927680904879579919)
      ·
        refine ⟨1310081891521357319369879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873387927680904879579919 1310081891521357319369879)
        ·
          refine ⟨1965122837282035979054819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310081891521357319369879 1965122837282035979054819)
          ·
            refine ⟨2947684255923053968582229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965122837282035979054819 2947684255923053968582229)
            ·
              refine ⟨34543174874098288694323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2947684255923053968582229 34543174874098288694323)
              ·
                rfl

theorem cell21_1362270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 8].length) (baseStart_1362270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362270 prefixEnd_1362270 := by exact prefixLift 1362270
  have htrace : WordTrace (prefixWord ++ tailWord_1362270) baseStart_1362270 baseEnd_1362270 := by
    simpa [prefixWord, tailWord_1362270, baseEnd_1362270] using wordTrace_append hprefix tailTrace_1362270
  have hstable : (prefixWord ++ tailWord_1362270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362270).length < 2 ^ (prefixWord ++ tailWord_1362270).sum := by decide
  have hdescent : baseEnd_1362270 < baseStart_1362270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362354 : List Nat := [3, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1362354 : Nat := 118140960795 + 1362354 * 2 ^ 59
def prefixEnd_1362354 : Nat := 4983230072969 + 3 ^ 40 * 1362354 * 2
def baseEnd_1362354 : Nat := 103635914603773039616245

theorem tailTrace_1362354 : CollatzResearch.WordTrace tailWord_1362354 prefixEnd_1362354 103635914603773039616245 := by
  unfold tailWord_1362354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422283126607901096095529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33126088337621069589588077 12422283126607901096095529)
  ·
    refine ⟨9316712344955925822071647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12422283126607901096095529 9316712344955925822071647)
    ·
      refine ⟨13975068517433888733107471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316712344955925822071647 13975068517433888733107471)
      ·
        refine ⟨20962602776150833099661207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13975068517433888733107471 20962602776150833099661207)
        ·
          refine ⟨31443904164226249649491811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20962602776150833099661207 31443904164226249649491811)
          ·
            refine ⟨47165856246339374474237717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31443904164226249649491811 47165856246339374474237717)
            ·
              refine ⟨2210899511547158178479893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47165856246339374474237717 2210899511547158178479893)
              ·
                refine ⟨103635914603773039616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2210899511547158178479893 103635914603773039616245)
                ·
                  rfl

theorem cell21_1362354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1362354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362354 prefixEnd_1362354 := by exact prefixLift 1362354
  have htrace : WordTrace (prefixWord ++ tailWord_1362354) baseStart_1362354 baseEnd_1362354 := by
    simpa [prefixWord, tailWord_1362354, baseEnd_1362354] using wordTrace_append hprefix tailTrace_1362354
  have hstable : (prefixWord ++ tailWord_1362354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362354).length < 2 ^ (prefixWord ++ tailWord_1362354).sum := by decide
  have hdescent : baseEnd_1362354 < baseStart_1362354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362357 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1362357 : Nat := 118140960795 + 1362357 * 2 ^ 59
def prefixEnd_1362357 : Nat := 4983230072969 + 3 ^ 40 * 1362357 * 2
def baseEnd_1362357 : Nat := 310908428452191780298729

theorem tailTrace_1362357 : CollatzResearch.WordTrace tailWord_1362357 prefixEnd_1362357 310908428452191780298729 := by
  unfold tailWord_1362357
  simp only [CollatzResearch.WordTrace]
  refine ⟨49689241925420735896741325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33126161283613823931160883 49689241925420735896741325)
  ·
    refine ⟨18633465722032775961277997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49689241925420735896741325 18633465722032775961277997)
    ·
      refine ⟨6987549645762290985479249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18633465722032775961277997 6987549645762290985479249)
      ·
        refine ⟨5240662234321718239109437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6987549645762290985479249 5240662234321718239109437)
        ·
          refine ⟨1965248337870644339666039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5240662234321718239109437 1965248337870644339666039)
          ·
            refine ⟨2947872506805966509499059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965248337870644339666039 2947872506805966509499059)
            ·
              refine ⟨4421808760208949764248589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947872506805966509499059 4421808760208949764248589)
              ·
                refine ⟨1658178285078356161593221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4421808760208949764248589 1658178285078356161593221)
                ·
                  refine ⟨310908428452191780298729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658178285078356161593221 310908428452191780298729)
                  ·
                    rfl

theorem cell21_1362357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1362357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362357 prefixEnd_1362357 := by exact prefixLift 1362357
  have htrace : WordTrace (prefixWord ++ tailWord_1362357) baseStart_1362357 baseEnd_1362357 := by
    simpa [prefixWord, tailWord_1362357, baseEnd_1362357] using wordTrace_append hprefix tailTrace_1362357
  have hstable : (prefixWord ++ tailWord_1362357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362357).length < 2 ^ (prefixWord ++ tailWord_1362357).sum := by decide
  have hdescent : baseEnd_1362357 < baseStart_1362357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362368 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_1362368 : Nat := 118140960795 + 1362368 * 2 ^ 59
def prefixEnd_1362368 : Nat := 4983230072969 + 3 ^ 40 * 1362368 * 2
def baseEnd_1362368 : Nat := 310910938802058205615373

theorem tailTrace_1362368 : CollatzResearch.WordTrace tailWord_1362368 prefixEnd_1362368 310910938802058205615373 := by
  unfold tailWord_1362368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24844821564190442387695879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33126428752253923183594505 24844821564190442387695879)
  ·
    refine ⟨37267232346285663581543819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24844821564190442387695879 37267232346285663581543819)
    ·
      refine ⟨55900848519428495372315729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37267232346285663581543819 55900848519428495372315729)
      ·
        refine ⟨41925636389571371529236797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55900848519428495372315729 41925636389571371529236797)
        ·
          refine ⟨15722113646089264323463799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41925636389571371529236797 15722113646089264323463799)
          ·
            refine ⟨23583170469133896485195699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15722113646089264323463799 23583170469133896485195699)
            ·
              refine ⟨35374755703700844727793549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23583170469133896485195699 35374755703700844727793549)
              ·
                refine ⟨13265533388887816772922581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35374755703700844727793549 13265533388887816772922581)
                ·
                  refine ⟨310910938802058205615373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13265533388887816772922581 310910938802058205615373)
                  ·
                    rfl

theorem cell21_1362368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_1362368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362368 prefixEnd_1362368 := by exact prefixLift 1362368
  have htrace : WordTrace (prefixWord ++ tailWord_1362368) baseStart_1362368 baseEnd_1362368 := by
    simpa [prefixWord, tailWord_1362368, baseEnd_1362368] using wordTrace_append hprefix tailTrace_1362368
  have hstable : (prefixWord ++ tailWord_1362368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362368).length < 2 ^ (prefixWord ++ tailWord_1362368).sum := by decide
  have hdescent : baseEnd_1362368 < baseStart_1362368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362461 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1362461 : Nat := 118140960795 + 1362461 * 2 ^ 59
def prefixEnd_1362461 : Nat := 4983230072969 + 3 ^ 40 * 1362461 * 2
def baseEnd_1362461 : Nat := 310932162669110710565183

theorem tailTrace_1362461 : CollatzResearch.WordTrace tailWord_1362461 prefixEnd_1362461 310932162669110710565183 := by
  unfold tailWord_1362461
  simp only [CollatzResearch.WordTrace]
  refine ⟨49693035117043961658527237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33128690078029307772351491 49693035117043961658527237)
  ·
    refine ⟨9317444084445742810973857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49693035117043961658527237 9317444084445742810973857)
    ·
      refine ⟨6988083063334307108230393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9317444084445742810973857 6988083063334307108230393)
      ·
        refine ⟨5241062297500730331172795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6988083063334307108230393 5241062297500730331172795)
        ·
          refine ⟨7861593446251095496759193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241062297500730331172795 7861593446251095496759193)
          ·
            refine ⟨5896195084688321622569395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7861593446251095496759193 5896195084688321622569395)
            ·
              refine ⟨8844292627032482433854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896195084688321622569395 8844292627032482433854093)
              ·
                refine ⟨3316609735137180912695285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8844292627032482433854093 3316609735137180912695285)
                ·
                  refine ⟨310932162669110710565183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3316609735137180912695285 310932162669110710565183)
                  ·
                    rfl

theorem cell21_1362461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1362461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362461 prefixEnd_1362461 := by exact prefixLift 1362461
  have htrace : WordTrace (prefixWord ++ tailWord_1362461) baseStart_1362461 baseEnd_1362461 := by
    simpa [prefixWord, tailWord_1362461, baseEnd_1362461] using wordTrace_append hprefix tailTrace_1362461
  have hstable : (prefixWord ++ tailWord_1362461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362461).length < 2 ^ (prefixWord ++ tailWord_1362461).sum := by decide
  have hdescent : baseEnd_1362461 < baseStart_1362461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362475 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_1362475 : Nat := 118140960795 + 1362475 * 2 ^ 59
def prefixEnd_1362475 : Nat := 4983230072969 + 3 ^ 40 * 1362475 * 2
def baseEnd_1362475 : Nat := 310935357659849797331821

theorem tailTrace_1362475 : CollatzResearch.WordTrace tailWord_1362475 prefixEnd_1362475 310935357659849797331821 := by
  unfold tailWord_1362475
  simp only [CollatzResearch.WordTrace]
  refine ⟨49693545738993242049536879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33129030492662161366357919 49693545738993242049536879)
  ·
    refine ⟨74540318608489863074305319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49693545738993242049536879 74540318608489863074305319)
    ·
      refine ⟨111810477912734794611457979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74540318608489863074305319 111810477912734794611457979)
      ·
        refine ⟨167715716869102191917186969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111810477912734794611457979 167715716869102191917186969)
        ·
          refine ⟨125786787651826643937890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167715716869102191917186969 125786787651826643937890227)
          ·
            refine ⟨188680181477739965906835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125786787651826643937890227 188680181477739965906835341)
            ·
              refine ⟨70755068054152487215063253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188680181477739965906835341 70755068054152487215063253)
              ·
                refine ⟨1658321907519198919103045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70755068054152487215063253 1658321907519198919103045)
                ·
                  refine ⟨310935357659849797331821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658321907519198919103045 310935357659849797331821)
                  ·
                    rfl

theorem cell21_1362475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_1362475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362475 prefixEnd_1362475 := by exact prefixLift 1362475
  have htrace : WordTrace (prefixWord ++ tailWord_1362475) baseStart_1362475 baseEnd_1362475 := by
    simpa [prefixWord, tailWord_1362475, baseEnd_1362475] using wordTrace_append hprefix tailTrace_1362475
  have hstable : (prefixWord ++ tailWord_1362475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362475).length < 2 ^ (prefixWord ++ tailWord_1362475).sum := by decide
  have hdescent : baseEnd_1362475 < baseStart_1362475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362506 : List Nat := [3, 1, 2, 1, 1, 6, 7]
def baseStart_1362506 : Nat := 118140960795 + 1362506 * 2 ^ 59
def prefixEnd_1362506 : Nat := 4983230072969 + 3 ^ 40 * 1362506 * 2
def baseEnd_1362506 : Nat := 34549159142466736923899

theorem tailTrace_1362506 : CollatzResearch.WordTrace tailWord_1362506 prefixEnd_1362506 34549159142466736923899 := by
  unfold tailWord_1362506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423669100470233585978843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33129784267920622895943581 12423669100470233585978843)
  ·
    refine ⟨18635503650705350378968265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12423669100470233585978843 18635503650705350378968265)
    ·
      refine ⟨13976627738029012784226199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18635503650705350378968265 13976627738029012784226199)
      ·
        refine ⟨20964941607043519176339299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13976627738029012784226199 20964941607043519176339299)
        ·
          refine ⟨31447412410565278764508949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964941607043519176339299 31447412410565278764508949)
          ·
            refine ⟨1474097456745247442086357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31447412410565278764508949 1474097456745247442086357)
            ·
              refine ⟨34549159142466736923899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1474097456745247442086357 34549159142466736923899)
              ·
                rfl

theorem cell21_1362506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 7].length) (baseStart_1362506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362506 prefixEnd_1362506 := by exact prefixLift 1362506
  have htrace : WordTrace (prefixWord ++ tailWord_1362506) baseStart_1362506 baseEnd_1362506 := by
    simpa [prefixWord, tailWord_1362506, baseEnd_1362506] using wordTrace_append hprefix tailTrace_1362506
  have hstable : (prefixWord ++ tailWord_1362506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362506).length < 2 ^ (prefixWord ++ tailWord_1362506).sum := by decide
  have hdescent : baseEnd_1362506 < baseStart_1362506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362565 : List Nat := [1, 3, 1, 1, 4, 11]
def baseStart_1362565 : Nat := 118140960795 + 1362565 * 2 ^ 59
def prefixEnd_1362565 : Nat := 4983230072969 + 3 ^ 40 * 1362565 * 2
def baseEnd_1362565 : Nat := 11516885069852949660431

theorem tailTrace_1362565 : CollatzResearch.WordTrace tailWord_1362565 prefixEnd_1362565 11516885069852949660431 := by
  unfold tailWord_1362565
  simp only [CollatzResearch.WordTrace]
  refine ⟨49696828308667187420313149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33131218872444791613542099 49696828308667187420313149)
  ·
    refine ⟨18636310615750195282617431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49696828308667187420313149 18636310615750195282617431)
    ·
      refine ⟨27954465923625292923926147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18636310615750195282617431 27954465923625292923926147)
      ·
        refine ⟨41931698885437939385889221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27954465923625292923926147 41931698885437939385889221)
        ·
          refine ⟨7862193541019613634854229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41931698885437939385889221 7862193541019613634854229)
          ·
            refine ⟨11516885069852949660431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7862193541019613634854229 11516885069852949660431)
            ·
              rfl

theorem cell21_1362565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 11].length) (baseStart_1362565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362565 prefixEnd_1362565 := by exact prefixLift 1362565
  have htrace : WordTrace (prefixWord ++ tailWord_1362565) baseStart_1362565 baseEnd_1362565 := by
    simpa [prefixWord, tailWord_1362565, baseEnd_1362565] using wordTrace_append hprefix tailTrace_1362565
  have hstable : (prefixWord ++ tailWord_1362565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362565).length < 2 ^ (prefixWord ++ tailWord_1362565).sum := by decide
  have hdescent : baseEnd_1362565 < baseStart_1362565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362641 : List Nat := [1, 2, 2, 1, 2, 3, 2, 8]
def baseStart_1362641 : Nat := 118140960795 + 1362641 * 2 ^ 59
def prefixEnd_1362641 : Nat := 4983230072969 + 3 ^ 40 * 1362641 * 2
def baseEnd_1362641 : Nat := 103657747040490132521605

theorem tailTrace_1362641 : CollatzResearch.WordTrace tailWord_1362641 prefixEnd_1362641 103657747040490132521605 := by
  unfold tailWord_1362641
  simp only [CollatzResearch.WordTrace]
  refine ⟨49699600256391852400079777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33133066837594568266719851 49699600256391852400079777)
  ·
    refine ⟨37274700192293889300059833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49699600256391852400079777 37274700192293889300059833)
    ·
      refine ⟨27956025144220416975044875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37274700192293889300059833 27956025144220416975044875)
      ·
        refine ⟨41934037716330625462567313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27956025144220416975044875 41934037716330625462567313)
        ·
          refine ⟨31450528287247969096925485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41934037716330625462567313 31450528287247969096925485)
          ·
            refine ⟨11793948107717988411347057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31450528287247969096925485 11793948107717988411347057)
            ·
              refine ⟨8845461080788491308510293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11793948107717988411347057 8845461080788491308510293)
              ·
                refine ⟨103657747040490132521605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8845461080788491308510293 103657747040490132521605)
                ·
                  rfl

theorem cell21_1362641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_1362641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362641 prefixEnd_1362641 := by exact prefixLift 1362641
  have htrace : WordTrace (prefixWord ++ tailWord_1362641) baseStart_1362641 baseEnd_1362641 := by
    simpa [prefixWord, tailWord_1362641, baseEnd_1362641] using wordTrace_append hprefix tailTrace_1362641
  have hstable : (prefixWord ++ tailWord_1362641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362641).length < 2 ^ (prefixWord ++ tailWord_1362641).sum := by decide
  have hdescent : baseEnd_1362641 < baseStart_1362641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362664 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_1362664 : Nat := 118140960795 + 1362664 * 2 ^ 59
def prefixEnd_1362664 : Nat := 4983230072969 + 3 ^ 40 * 1362664 * 2
def baseEnd_1362664 : Nat := 310978490034827468681435

theorem tailTrace_1362664 : CollatzResearch.WordTrace tailWord_1362664 prefixEnd_1362664 310978490034827468681435 := by
  unfold tailWord_1362664
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850219567654263664083523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33133626090205684885444697 24850219567654263664083523)
  ·
    refine ⟨37275329351481395496125285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24850219567654263664083523 37275329351481395496125285)
    ·
      refine ⟨6989124253402761655523491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37275329351481395496125285 6989124253402761655523491)
      ·
        refine ⟨10483686380104142483285237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6989124253402761655523491 10483686380104142483285237)
        ·
          refine ⟨982845598134763357807991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10483686380104142483285237 982845598134763357807991)
          ·
            refine ⟨1474268397202145036711987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982845598134763357807991 1474268397202145036711987)
            ·
              refine ⟨2211402595803217555067981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474268397202145036711987 2211402595803217555067981)
              ·
                refine ⟨829275973426206583150493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2211402595803217555067981 829275973426206583150493)
                ·
                  refine ⟨310978490034827468681435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829275973426206583150493 310978490034827468681435)
                  ·
                    rfl

theorem cell21_1362664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_1362664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362664 prefixEnd_1362664 := by exact prefixLift 1362664
  have htrace : WordTrace (prefixWord ++ tailWord_1362664) baseStart_1362664 baseEnd_1362664 := by
    simpa [prefixWord, tailWord_1362664, baseEnd_1362664] using wordTrace_append hprefix tailTrace_1362664
  have hstable : (prefixWord ++ tailWord_1362664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362664).length < 2 ^ (prefixWord ++ tailWord_1362664).sum := by decide
  have hdescent : baseEnd_1362664 < baseStart_1362664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362703 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_1362703 : Nat := 118140960795 + 1362703 * 2 ^ 59
def prefixEnd_1362703 : Nat := 4983230072969 + 3 ^ 40 * 1362703 * 2
def baseEnd_1362703 : Nat := 310987390366172067531355

theorem tailTrace_1362703 : CollatzResearch.WordTrace tailWord_1362703 prefixEnd_1362703 310987390366172067531355 := by
  unfold tailWord_1362703
  simp only [CollatzResearch.WordTrace]
  refine ⟨49701861582167236988836763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33134574388111491325891175 49701861582167236988836763)
  ·
    refine ⟨74552792373250855483255145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49701861582167236988836763 74552792373250855483255145)
    ·
      refine ⟨55914594279938141612441359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74552792373250855483255145 55914594279938141612441359)
      ·
        refine ⟨83871891419907212418662039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55914594279938141612441359 83871891419907212418662039)
        ·
          refine ⟨125807837129860818627993059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83871891419907212418662039 125807837129860818627993059)
          ·
            refine ⟨188711755694791227941989589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125807837129860818627993059 188711755694791227941989589)
            ·
              refine ⟨4422931774096669404890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188711755694791227941989589 4422931774096669404890381)
              ·
                refine ⟨1658599415286251026833893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4422931774096669404890381 1658599415286251026833893)
                ·
                  refine ⟨310987390366172067531355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658599415286251026833893 310987390366172067531355)
                  ·
                    rfl

theorem cell21_1362703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_1362703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362703 prefixEnd_1362703 := by exact prefixLift 1362703
  have htrace : WordTrace (prefixWord ++ tailWord_1362703) baseStart_1362703 baseEnd_1362703 := by
    simpa [prefixWord, tailWord_1362703, baseEnd_1362703] using wordTrace_append hprefix tailTrace_1362703
  have hstable : (prefixWord ++ tailWord_1362703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362703).length < 2 ^ (prefixWord ++ tailWord_1362703).sum := by decide
  have hdescent : baseEnd_1362703 < baseStart_1362703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362734 : List Nat := [4, 1, 3, 2, 1, 10]
def baseStart_1362734 : Nat := 118140960795 + 1362734 * 2 ^ 59
def prefixEnd_1362734 : Nat := 4983230072969 + 3 ^ 40 * 1362734 * 2
def baseEnd_1362734 : Nat := 11518313518093440833875

theorem tailTrace_1362734 : CollatzResearch.WordTrace tailWord_1362734 prefixEnd_1362734 11518313518093440833875 := by
  unfold tailWord_1362734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212874030631866160401907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33135328163369952855476837 6212874030631866160401907)
  ·
    refine ⟨9319311045947799240602861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212874030631866160401907 9319311045947799240602861)
    ·
      refine ⟨3494741642230424715226073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9319311045947799240602861 3494741642230424715226073)
      ·
        refine ⟨2621056231672818536419555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3494741642230424715226073 2621056231672818536419555)
        ·
          refine ⟨3931584347509227804629333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621056231672818536419555 3931584347509227804629333)
          ·
            refine ⟨11518313518093440833875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3931584347509227804629333 11518313518093440833875)
            ·
              rfl

theorem cell21_1362734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 10].length) (baseStart_1362734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362734 prefixEnd_1362734 := by exact prefixLift 1362734
  have htrace : WordTrace (prefixWord ++ tailWord_1362734) baseStart_1362734 baseEnd_1362734 := by
    simpa [prefixWord, tailWord_1362734, baseEnd_1362734] using wordTrace_append hprefix tailTrace_1362734
  have hstable : (prefixWord ++ tailWord_1362734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362734).length < 2 ^ (prefixWord ++ tailWord_1362734).sum := by decide
  have hdescent : baseEnd_1362734 < baseStart_1362734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362748 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1362748 : Nat := 118140960795 + 1362748 * 2 ^ 59
def prefixEnd_1362748 : Nat := 4983230072969 + 3 ^ 40 * 1362748 * 2
def baseEnd_1362748 : Nat := 310997659979261989281263

theorem tailTrace_1362748 : CollatzResearch.WordTrace tailWord_1362748 prefixEnd_1362748 310997659979261989281263 := by
  unfold tailWord_1362748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851751433502104837112449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33135668578002806449483265 24851751433502104837112449)
  ·
    refine ⟨18638813575126578627834337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24851751433502104837112449 18638813575126578627834337)
    ·
      refine ⟨13979110181344933970875753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18638813575126578627834337 13979110181344933970875753)
      ·
        refine ⟨10484332636008700478156815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13979110181344933970875753 10484332636008700478156815)
        ·
          refine ⟨15726498954013050717235223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10484332636008700478156815 15726498954013050717235223)
          ·
            refine ⟨23589748431019576075852835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15726498954013050717235223 23589748431019576075852835)
            ·
              refine ⟨35384622646529364113779253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23589748431019576075852835 35384622646529364113779253)
              ·
                refine ⟨3317308373112127885666805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35384622646529364113779253 3317308373112127885666805)
                ·
                  refine ⟨310997659979261989281263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3317308373112127885666805 310997659979261989281263)
                  ·
                    rfl

theorem cell21_1362748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1362748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362748 prefixEnd_1362748 := by exact prefixLift 1362748
  have htrace : WordTrace (prefixWord ++ tailWord_1362748) baseStart_1362748 baseEnd_1362748 := by
    simpa [prefixWord, tailWord_1362748, baseEnd_1362748] using wordTrace_append hprefix tailTrace_1362748
  have hstable : (prefixWord ++ tailWord_1362748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362748).length < 2 ^ (prefixWord ++ tailWord_1362748).sum := by decide
  have hdescent : baseEnd_1362748 < baseStart_1362748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362872 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_1362872 : Nat := 118140960795 + 1362872 * 2 ^ 59
def prefixEnd_1362872 : Nat := 4983230072969 + 3 ^ 40 * 1362872 * 2
def baseEnd_1362872 : Nat := 311025958468665329214343

theorem tailTrace_1362872 : CollatzResearch.WordTrace tailWord_1362872 prefixEnd_1362872 311025958468665329214343 := by
  unfold tailWord_1362872
  simp only [CollatzResearch.WordTrace]
  refine ⟨24854012759277489425869435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33138683679036652567825913 24854012759277489425869435)
  ·
    refine ⟨37281019138916234138804153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24854012759277489425869435 37281019138916234138804153)
    ·
      refine ⟨27960764354187175604103115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37281019138916234138804153 27960764354187175604103115)
      ·
        refine ⟨41941146531280763406154673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27960764354187175604103115 41941146531280763406154673)
        ·
          refine ⟨31455859898460572554616005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41941146531280763406154673 31455859898460572554616005)
          ·
            refine ⟨5897973730961357353990501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31455859898460572554616005 5897973730961357353990501)
            ·
              refine ⟨1105870074555254503873219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5897973730961357353990501 1105870074555254503873219)
              ·
                refine ⟨1658805111832881755809829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105870074555254503873219 1658805111832881755809829)
                ·
                  refine ⟨311025958468665329214343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658805111832881755809829 311025958468665329214343)
                  ·
                    rfl

theorem cell21_1362872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_1362872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362872 prefixEnd_1362872 := by exact prefixLift 1362872
  have htrace : WordTrace (prefixWord ++ tailWord_1362872) baseStart_1362872 baseEnd_1362872 := by
    simpa [prefixWord, tailWord_1362872, baseEnd_1362872] using wordTrace_append hprefix tailTrace_1362872
  have hstable : (prefixWord ++ tailWord_1362872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362872).length < 2 ^ (prefixWord ++ tailWord_1362872).sum := by decide
  have hdescent : baseEnd_1362872 < baseStart_1362872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362996 : List Nat := [2, 5, 1, 2, 1, 3, 2, 5]
def baseStart_1362996 : Nat := 118140960795 + 1362996 * 2 ^ 59
def prefixEnd_1362996 : Nat := 4983230072969 + 3 ^ 40 * 1362996 * 2
def baseEnd_1362996 : Nat := 103684752319356223049141

theorem tailTrace_1362996 : CollatzResearch.WordTrace tailWord_1362996 prefixEnd_1362996 103684752319356223049141 := by
  unfold tailWord_1362996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24856274085052874014626421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33141698780070498686168561 24856274085052874014626421)
  ·
    refine ⟨2330275695473706938871227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24856274085052874014626421 2330275695473706938871227)
    ·
      refine ⟨3495413543210560408306841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330275695473706938871227 3495413543210560408306841)
      ·
        refine ⟨2621560157407920306230131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3495413543210560408306841 2621560157407920306230131)
        ·
          refine ⟨3932340236111880459345197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621560157407920306230131 3932340236111880459345197)
          ·
            refine ⟨1474627588541955172254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3932340236111880459345197 1474627588541955172254449)
            ·
              refine ⟨1105970691406466379190837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474627588541955172254449 1105970691406466379190837)
              ·
                refine ⟨103684752319356223049141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105970691406466379190837 103684752319356223049141)
                ·
                  rfl

theorem cell21_1362996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_1362996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1362996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1362996 prefixEnd_1362996 := by exact prefixLift 1362996
  have htrace : WordTrace (prefixWord ++ tailWord_1362996) baseStart_1362996 baseEnd_1362996 := by
    simpa [prefixWord, tailWord_1362996, baseEnd_1362996] using wordTrace_append hprefix tailTrace_1362996
  have hstable : (prefixWord ++ tailWord_1362996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362996).length < 2 ^ (prefixWord ++ tailWord_1362996).sum := by decide
  have hdescent : baseEnd_1362996 < baseStart_1362996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363069 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1363069 : Nat := 118140960795 + 1363069 * 2 ^ 59
def prefixEnd_1363069 : Nat := 4983230072969 + 3 ^ 40 * 1363069 * 2
def baseEnd_1363069 : Nat := 311070916552636764430607

theorem tailTrace_1363069 : CollatzResearch.WordTrace tailWord_1363069 prefixEnd_1363069 311070916552636764430607 := by
  unfold tailWord_1363069
  simp only [CollatzResearch.WordTrace]
  refine ⟨49715210698841281496660261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33143473799227520997773507 49715210698841281496660261)
  ·
    refine ⟨9321602006032740280623799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49715210698841281496660261 9321602006032740280623799)
    ·
      refine ⟨13982403009049110420935699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321602006032740280623799 13982403009049110420935699)
      ·
        refine ⟨20973604513573665631403549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982403009049110420935699 20973604513573665631403549)
        ·
          refine ⟨7865101692590124611776331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20973604513573665631403549 7865101692590124611776331)
          ·
            refine ⟨11797652538885186917664497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865101692590124611776331 11797652538885186917664497)
            ·
              refine ⟨8848239404163890188248373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11797652538885186917664497 8848239404163890188248373)
              ·
                refine ⟨829522444140364705148285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8848239404163890188248373 829522444140364705148285)
                ·
                  refine ⟨311070916552636764430607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829522444140364705148285 311070916552636764430607)
                  ·
                    rfl

theorem cell21_1363069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1363069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363069 prefixEnd_1363069 := by exact prefixLift 1363069
  have htrace : WordTrace (prefixWord ++ tailWord_1363069) baseStart_1363069 baseEnd_1363069 := by
    simpa [prefixWord, tailWord_1363069, baseEnd_1363069] using wordTrace_append hprefix tailTrace_1363069
  have hstable : (prefixWord ++ tailWord_1363069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363069).length < 2 ^ (prefixWord ++ tailWord_1363069).sum := by decide
  have hdescent : baseEnd_1363069 < baseStart_1363069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363086 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1363086 : Nat := 118140960795 + 1363086 * 2 ^ 59
def prefixEnd_1363086 : Nat := 4983230072969 + 3 ^ 40 * 1363086 * 2
def baseEnd_1363086 : Nat := 311074796184248512647239

theorem tailTrace_1363086 : CollatzResearch.WordTrace tailWord_1363086 prefixEnd_1363086 311074796184248512647239 := by
  unfold tailWord_1363086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214478842472461675003639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33143887159853128933352741 6214478842472461675003639)
  ·
    refine ⟨9321718263708692512505459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214478842472461675003639 9321718263708692512505459)
    ·
      refine ⟨13982577395563038768758189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321718263708692512505459 13982577395563038768758189)
      ·
        refine ⟨5243466523336139538284321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13982577395563038768758189 5243466523336139538284321)
        ·
          refine ⟨3932599892502104653713241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5243466523336139538284321 3932599892502104653713241)
          ·
            refine ⟨2949449919376578490284931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932599892502104653713241 2949449919376578490284931)
            ·
              refine ⟨4424174879064867735427397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949449919376578490284931 4424174879064867735427397)
              ·
                refine ⟨829532789824662700392637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4424174879064867735427397 829532789824662700392637)
                ·
                  refine ⟨311074796184248512647239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829532789824662700392637 311074796184248512647239)
                  ·
                    rfl

theorem cell21_1363086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1363086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363086 prefixEnd_1363086 := by exact prefixLift 1363086
  have htrace : WordTrace (prefixWord ++ tailWord_1363086) baseStart_1363086 baseEnd_1363086 := by
    simpa [prefixWord, tailWord_1363086, baseEnd_1363086] using wordTrace_append hprefix tailTrace_1363086
  have hstable : (prefixWord ++ tailWord_1363086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363086).length < 2 ^ (prefixWord ++ tailWord_1363086).sum := by decide
  have hdescent : baseEnd_1363086 < baseStart_1363086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363252 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1363252 : Nat := 118140960795 + 1363252 * 2 ^ 59
def prefixEnd_1363252 : Nat := 4983230072969 + 3 ^ 40 * 1363252 * 2
def baseEnd_1363252 : Nat := 311112679645869112880233

theorem tailTrace_1363252 : CollatzResearch.WordTrace tailWord_1363252 prefixEnd_1363252 311112679645869112880233 := by
  unfold tailWord_1363252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860942628589151875286005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33147923504785535833714673 24860942628589151875286005)
  ·
    refine ⟨2330713371430232988308063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24860942628589151875286005 2330713371430232988308063)
    ·
      refine ⟨3496070057145349482462095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330713371430232988308063 3496070057145349482462095)
      ·
        refine ⟨5244105085718024223693143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496070057145349482462095 5244105085718024223693143)
        ·
          refine ⟨7866157628577036335539715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244105085718024223693143 7866157628577036335539715)
          ·
            refine ⟨11799236442865554503309573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866157628577036335539715 11799236442865554503309573)
            ·
              refine ⟨2212356833037291469370545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11799236442865554503309573 2212356833037291469370545)
              ·
                refine ⟨1659267624777968602027909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212356833037291469370545 1659267624777968602027909)
                ·
                  refine ⟨311112679645869112880233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659267624777968602027909 311112679645869112880233)
                  ·
                    rfl

theorem cell21_1363252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1363252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363252 prefixEnd_1363252 := by exact prefixLift 1363252
  have htrace : WordTrace (prefixWord ++ tailWord_1363252) baseStart_1363252 baseEnd_1363252 := by
    simpa [prefixWord, tailWord_1363252, baseEnd_1363252] using wordTrace_append hprefix tailTrace_1363252
  have hstable : (prefixWord ++ tailWord_1363252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363252).length < 2 ^ (prefixWord ++ tailWord_1363252).sum := by decide
  have hdescent : baseEnd_1363252 < baseStart_1363252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363339 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_1363339 : Nat := 118140960795 + 1363339 * 2 ^ 59
def prefixEnd_1363339 : Nat := 4983230072969 + 3 ^ 40 * 1363339 * 2
def baseEnd_1363339 : Nat := 311132534231176294930055

theorem tailTrace_1363339 : CollatzResearch.WordTrace tailWord_1363339 prefixEnd_1363339 311132534231176294930055 := by
  unfold tailWord_1363339
  simp only [CollatzResearch.WordTrace]
  refine ⟨49725058407863117608989071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33150038938575411739326047 49725058407863117608989071)
  ·
    refine ⟨74587587611794676413483607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49725058407863117608989071 74587587611794676413483607)
    ·
      refine ⟨111881381417692014620225411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74587587611794676413483607 111881381417692014620225411)
      ·
        refine ⟨167822072126538021930338117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111881381417692014620225411 167822072126538021930338117)
        ·
          refine ⟨31466638523725879111938397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167822072126538021930338117 31466638523725879111938397)
          ·
            refine ⟨11799989446397204666976899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31466638523725879111938397 11799989446397204666976899)
            ·
              refine ⟨17699984169595807000465349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799989446397204666976899 17699984169595807000465349)
              ·
                refine ⟨3318747031799213812587253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17699984169595807000465349 3318747031799213812587253)
                ·
                  refine ⟨311132534231176294930055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318747031799213812587253 311132534231176294930055)
                  ·
                    rfl

theorem cell21_1363339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_1363339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363339 prefixEnd_1363339 := by exact prefixLift 1363339
  have htrace : WordTrace (prefixWord ++ tailWord_1363339) baseStart_1363339 baseEnd_1363339 := by
    simpa [prefixWord, tailWord_1363339, baseEnd_1363339] using wordTrace_append hprefix tailTrace_1363339
  have hstable : (prefixWord ++ tailWord_1363339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363339).length < 2 ^ (prefixWord ++ tailWord_1363339).sum := by decide
  have hdescent : baseEnd_1363339 < baseStart_1363339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363342 : List Nat := [4, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1363342 : Nat := 118140960795 + 1363342 * 2 ^ 59
def prefixEnd_1363342 : Nat := 4983230072969 + 3 ^ 40 * 1363342 * 2
def baseEnd_1363342 : Nat := 103711072957349652126683

theorem tailTrace_1363342 : CollatzResearch.WordTrace tailWord_1363342 prefixEnd_1363342 103711072957349652126683 := by
  unfold tailWord_1363342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215645978356531140168535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33150111884568166080898853 6215645978356531140168535)
  ·
    refine ⟨9323468967534796710252803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215645978356531140168535 9323468967534796710252803)
    ·
      refine ⟨13985203451302195065379205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9323468967534796710252803 13985203451302195065379205)
      ·
        refine ⟨2622225647119161574758601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13985203451302195065379205 2622225647119161574758601)
        ·
          refine ⟨1966669235339371181068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2622225647119161574758601 1966669235339371181068951)
          ·
            refine ⟨2950003853009056771603427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966669235339371181068951 2950003853009056771603427)
            ·
              refine ⟨4425005779513585157405141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950003853009056771603427 4425005779513585157405141)
              ·
                refine ⟨103711072957349652126683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4425005779513585157405141 103711072957349652126683)
                ·
                  rfl

theorem cell21_1363342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1363342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363342 prefixEnd_1363342 := by exact prefixLift 1363342
  have htrace : WordTrace (prefixWord ++ tailWord_1363342) baseStart_1363342 baseEnd_1363342 := by
    simpa [prefixWord, tailWord_1363342, baseEnd_1363342] using wordTrace_append hprefix tailTrace_1363342
  have hstable : (prefixWord ++ tailWord_1363342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363342).length < 2 ^ (prefixWord ++ tailWord_1363342).sum := by decide
  have hdescent : baseEnd_1363342 < baseStart_1363342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363373 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1363373 : Nat := 118140960795 + 1363373 * 2 ^ 59
def prefixEnd_1363373 : Nat := 4983230072969 + 3 ^ 40 * 1363373 * 2
def baseEnd_1363373 : Nat := 311140293494399791363319

theorem tailTrace_1363373 : CollatzResearch.WordTrace tailWord_1363373 prefixEnd_1363373 311140293494399791363319 := by
  unfold tailWord_1363373
  simp only [CollatzResearch.WordTrace]
  refine ⟨49726298489739941415726773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33150865659826627610484515 49726298489739941415726773)
  ·
    refine ⟨4661840483413119507724385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49726298489739941415726773 4661840483413119507724385)
    ·
      refine ⟨3496380362559839630793289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4661840483413119507724385 3496380362559839630793289)
      ·
        refine ⟨2622285271919879723094967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496380362559839630793289 2622285271919879723094967)
        ·
          refine ⟨3933427907879819584642451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622285271919879723094967 3933427907879819584642451)
          ·
            refine ⟨5900141861819729376963677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933427907879819584642451 5900141861819729376963677)
            ·
              refine ⟨2212553198182398516361379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900141861819729376963677 2212553198182398516361379)
              ·
                refine ⟨3318829797273597774542069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212553198182398516361379 3318829797273597774542069)
                ·
                  refine ⟨311140293494399791363319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3318829797273597774542069 311140293494399791363319)
                  ·
                    rfl

theorem cell21_1363373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1363373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363373 prefixEnd_1363373 := by exact prefixLift 1363373
  have htrace : WordTrace (prefixWord ++ tailWord_1363373) baseStart_1363373 baseEnd_1363373 := by
    simpa [prefixWord, tailWord_1363373, baseEnd_1363373] using wordTrace_append hprefix tailTrace_1363373
  have hstable : (prefixWord ++ tailWord_1363373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363373).length < 2 ^ (prefixWord ++ tailWord_1363373).sum := by decide
  have hdescent : baseEnd_1363373 < baseStart_1363373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363384 : List Nat := [2, 1, 2, 1, 2, 2, 3, 8]
def baseStart_1363384 : Nat := 118140960795 + 1363384 * 2 ^ 59
def prefixEnd_1363384 : Nat := 4983230072969 + 3 ^ 40 * 1363384 * 2
def baseEnd_1363384 : Nat := 103714267948088738893321

theorem tailTrace_1363384 : CollatzResearch.WordTrace tailWord_1363384 prefixEnd_1363384 103714267948088738893321 := by
  unfold tailWord_1363384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24863349846350045147188603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33151133128466726862918137 24863349846350045147188603)
  ·
    refine ⟨37295024769525067720782905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24863349846350045147188603 37295024769525067720782905)
    ·
      refine ⟨27971268577143800790587179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37295024769525067720782905 27971268577143800790587179)
      ·
        refine ⟨41956902865715701185880769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27971268577143800790587179 41956902865715701185880769)
        ·
          refine ⟨31467677149286775889410577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41956902865715701185880769 31467677149286775889410577)
          ·
            refine ⟨23600757861965081917057933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31467677149286775889410577 23600757861965081917057933)
            ·
              refine ⟨8850284198236905718896725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23600757861965081917057933 8850284198236905718896725)
              ·
                refine ⟨103714267948088738893321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8850284198236905718896725 103714267948088738893321)
                ·
                  rfl

theorem cell21_1363384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_1363384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363384 prefixEnd_1363384 := by exact prefixLift 1363384
  have htrace : WordTrace (prefixWord ++ tailWord_1363384) baseStart_1363384 baseEnd_1363384 := by
    simpa [prefixWord, tailWord_1363384, baseEnd_1363384] using wordTrace_append hprefix tailTrace_1363384
  have hstable : (prefixWord ++ tailWord_1363384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363384).length < 2 ^ (prefixWord ++ tailWord_1363384).sum := by decide
  have hdescent : baseEnd_1363384 < baseStart_1363384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363480 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_1363480 : Nat := 118140960795 + 1363480 * 2 ^ 59
def prefixEnd_1363480 : Nat := 4983230072969 + 3 ^ 40 * 1363480 * 2
def baseEnd_1363480 : Nat := 311164712352191383079767

theorem tailTrace_1363480 : CollatzResearch.WordTrace tailWord_1363480 prefixEnd_1363480 311164712352191383079767 := by
  unfold tailWord_1363480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865100550176149344935947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33153467400234865793247929 24865100550176149344935947)
  ·
    refine ⟨37297650825264224017403921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24865100550176149344935947 37297650825264224017403921)
    ·
      refine ⟨27973238118948168013052941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37297650825264224017403921 27973238118948168013052941)
      ·
        refine ⟨10489964294605563004894853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27973238118948168013052941 10489964294605563004894853)
        ·
          refine ⟨1966868305238543063417785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10489964294605563004894853 1966868305238543063417785)
          ·
            refine ⟨1475151228928907297563339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966868305238543063417785 1475151228928907297563339)
            ·
              refine ⟨2212726843393360946345009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475151228928907297563339 2212726843393360946345009)
              ·
                refine ⟨1659545132545020709758757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212726843393360946345009 1659545132545020709758757)
                ·
                  refine ⟨311164712352191383079767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659545132545020709758757 311164712352191383079767)
                  ·
                    rfl

theorem cell21_1363480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_1363480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363480 prefixEnd_1363480 := by exact prefixLift 1363480
  have htrace : WordTrace (prefixWord ++ tailWord_1363480) baseStart_1363480 baseEnd_1363480 := by
    simpa [prefixWord, tailWord_1363480, baseEnd_1363480] using wordTrace_append hprefix tailTrace_1363480
  have hstable : (prefixWord ++ tailWord_1363480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363480).length < 2 ^ (prefixWord ++ tailWord_1363480).sum := by decide
  have hdescent : baseEnd_1363480 < baseStart_1363480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363556 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1363556 : Nat := 118140960795 + 1363556 * 2 ^ 59
def prefixEnd_1363556 : Nat := 4983230072969 + 3 ^ 40 * 1363556 * 2
def baseEnd_1363556 : Nat := 311182056587632139812945

theorem tailTrace_1363556 : CollatzResearch.WordTrace tailWord_1363556 prefixEnd_1363556 311182056587632139812945 := by
  unfold tailWord_1363556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24866486524038481834819261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33155315365384642446425681 24866486524038481834819261)
  ·
    refine ⟨9324932446514430688057223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24866486524038481834819261 9324932446514430688057223)
    ·
      refine ⟨13987398669771646032085835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9324932446514430688057223 13987398669771646032085835)
      ·
        refine ⟨20981098004657469048128753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13987398669771646032085835 20981098004657469048128753)
        ·
          refine ⟨15735823503493101786096565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20981098004657469048128753 15735823503493101786096565)
          ·
            refine ⟨1475233453452478292446553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15735823503493101786096565 1475233453452478292446553)
            ·
              refine ⟨1106425090089358719334915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475233453452478292446553 1106425090089358719334915)
              ·
                refine ⟨1659637635134038079002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106425090089358719334915 1659637635134038079002373)
                ·
                  refine ⟨311182056587632139812945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659637635134038079002373 311182056587632139812945)
                  ·
                    rfl

theorem cell21_1363556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1363556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363556 prefixEnd_1363556 := by exact prefixLift 1363556
  have htrace : WordTrace (prefixWord ++ tailWord_1363556) baseStart_1363556 baseEnd_1363556 := by
    simpa [prefixWord, tailWord_1363556, baseEnd_1363556] using wordTrace_append hprefix tailTrace_1363556
  have hstable : (prefixWord ++ tailWord_1363556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363556).length < 2 ^ (prefixWord ++ tailWord_1363556).sum := by decide
  have hdescent : baseEnd_1363556 < baseStart_1363556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363584 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_1363584 : Nat := 118140960795 + 1363584 * 2 ^ 59
def prefixEnd_1363584 : Nat := 4983230072969 + 3 ^ 40 * 1363584 * 2
def baseEnd_1363584 : Nat := 311188446569110313346221

theorem tailTrace_1363584 : CollatzResearch.WordTrace tailWord_1363584 prefixEnd_1363584 311188446569110313346221 := by
  unfold tailWord_1363584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24866997145987762225828903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33155996194650349634438537 24866997145987762225828903)
  ·
    refine ⟨37300495718981643338743355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24866997145987762225828903 37300495718981643338743355)
    ·
      refine ⟨55950743578472465008115033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37300495718981643338743355 55950743578472465008115033)
      ·
        refine ⟨41963057683854348756086275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55950743578472465008115033 41963057683854348756086275)
        ·
          refine ⟨62944586525781523134129413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41963057683854348756086275 62944586525781523134129413)
          ·
            refine ⟨11802109973584035587649265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62944586525781523134129413 11802109973584035587649265)
            ·
              refine ⟨8851582480188026690736949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11802109973584035587649265 8851582480188026690736949)
              ·
                refine ⟨829835857517627502256589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8851582480188026690736949 829835857517627502256589)
                ·
                  refine ⟨311188446569110313346221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829835857517627502256589 311188446569110313346221)
                  ·
                    rfl

theorem cell21_1363584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_1363584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363584 prefixEnd_1363584 := by exact prefixLift 1363584
  have htrace : WordTrace (prefixWord ++ tailWord_1363584) baseStart_1363584 baseEnd_1363584 := by
    simpa [prefixWord, tailWord_1363584, baseEnd_1363584] using wordTrace_append hprefix tailTrace_1363584
  have hstable : (prefixWord ++ tailWord_1363584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363584).length < 2 ^ (prefixWord ++ tailWord_1363584).sum := by decide
  have hdescent : baseEnd_1363584 < baseStart_1363584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363770 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_1363770 : Nat := 118140960795 + 1363770 * 2 ^ 59
def prefixEnd_1363770 : Nat := 4983230072969 + 3 ^ 40 * 1363770 * 2
def baseEnd_1363770 : Nat := 311230894303215323245841

theorem tailTrace_1363770 : CollatzResearch.WordTrace tailWord_1363770 prefixEnd_1363770 311230894303215323245841 := by
  unfold tailWord_1363770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435194567325419554482191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33160518846201118811952509 12435194567325419554482191)
  ·
    refine ⟨18652791850988129331723287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12435194567325419554482191 18652791850988129331723287)
    ·
      refine ⟨27979187776482193997584931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652791850988129331723287 27979187776482193997584931)
      ·
        refine ⟨41968781664723290996377397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27979187776482193997584931 41968781664723290996377397)
        ·
          refine ⟨3934573281067808530910381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41968781664723290996377397 3934573281067808530910381)
          ·
            refine ⟨1475464980400428199091393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3934573281067808530910381 1475464980400428199091393)
            ·
              refine ⟨1106598735300321149318545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475464980400428199091393 1106598735300321149318545)
              ·
                refine ⟨829949051475240861988909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106598735300321149318545 829949051475240861988909)
                ·
                  refine ⟨311230894303215323245841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829949051475240861988909 311230894303215323245841)
                  ·
                    rfl

theorem cell21_1363770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_1363770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363770 prefixEnd_1363770 := by exact prefixLift 1363770
  have htrace : WordTrace (prefixWord ++ tailWord_1363770) baseStart_1363770 baseEnd_1363770 := by
    simpa [prefixWord, tailWord_1363770, baseEnd_1363770] using wordTrace_append hprefix tailTrace_1363770
  have hstable : (prefixWord ++ tailWord_1363770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363770).length < 2 ^ (prefixWord ++ tailWord_1363770).sum := by decide
  have hdescent : baseEnd_1363770 < baseStart_1363770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363809 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1363809 : Nat := 118140960795 + 1363809 * 2 ^ 59
def prefixEnd_1363809 : Nat := 4983230072969 + 3 ^ 40 * 1363809 * 2
def baseEnd_1363809 : Nat := 311239794634559922095761

theorem tailTrace_1363809 : CollatzResearch.WordTrace tailWord_1363809 prefixEnd_1363809 311239794634559922095761 := by
  unfold tailWord_1363809
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742200716160387878598481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33161467144106925252398987 49742200716160387878598481)
  ·
    refine ⟨37306650537120290908948861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49742200716160387878598481 37306650537120290908948861)
    ·
      refine ⟨13989993951420109090855823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37306650537120290908948861 13989993951420109090855823)
      ·
        refine ⟨20984990927130163636283735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13989993951420109090855823 20984990927130163636283735)
        ·
          refine ⟨31477486390695245454425603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20984990927130163636283735 31477486390695245454425603)
          ·
            refine ⟨47216229586042868181638405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31477486390695245454425603 47216229586042868181638405)
            ·
              refine ⟨8853043047383037784057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47216229586042868181638405 8853043047383037784057201)
              ·
                refine ⟨6639782285537278338042901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8853043047383037784057201 6639782285537278338042901)
                ·
                  refine ⟨311239794634559922095761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6639782285537278338042901 311239794634559922095761)
                  ·
                    rfl

theorem cell21_1363809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1363809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363809 prefixEnd_1363809 := by exact prefixLift 1363809
  have htrace : WordTrace (prefixWord ++ tailWord_1363809) baseStart_1363809 baseEnd_1363809 := by
    simpa [prefixWord, tailWord_1363809, baseEnd_1363809] using wordTrace_append hprefix tailTrace_1363809
  have hstable : (prefixWord ++ tailWord_1363809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363809).length < 2 ^ (prefixWord ++ tailWord_1363809).sum := by decide
  have hdescent : baseEnd_1363809 < baseStart_1363809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363843 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 4]
def baseStart_1363843 : Nat := 118140960795 + 1363843 * 2 ^ 59
def prefixEnd_1363843 : Nat := 4983230072969 + 3 ^ 40 * 1363843 * 2
def baseEnd_1363843 : Nat := 311247553897783418529025

theorem tailTrace_1363843 : CollatzResearch.WordTrace tailWord_1363843 prefixEnd_1363843 311247553897783418529025 := by
  unfold tailWord_1363843
  simp only [CollatzResearch.WordTrace]
  refine ⟨49743440798037211685336183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33162293865358141123557455 49743440798037211685336183)
  ·
    refine ⟨74615161197055817528004275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49743440798037211685336183 74615161197055817528004275)
    ·
      refine ⟨111922741795583726292006413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74615161197055817528004275 111922741795583726292006413)
      ·
        refine ⟨41971028173343897359502405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111922741795583726292006413 41971028173343897359502405)
        ·
          refine ⟨7869567782501980754906701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41971028173343897359502405 7869567782501980754906701)
          ·
            refine ⟨2951087918438242783090013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7869567782501980754906701 2951087918438242783090013)
            ·
              refine ⟨1106657969414341043658755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2951087918438242783090013 1106657969414341043658755)
              ·
                refine ⟨1659986954121511565488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106657969414341043658755 1659986954121511565488133)
                ·
                  refine ⟨311247553897783418529025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659986954121511565488133 311247553897783418529025)
                  ·
                    rfl

theorem cell21_1363843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_1363843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363843 prefixEnd_1363843 := by exact prefixLift 1363843
  have htrace : WordTrace (prefixWord ++ tailWord_1363843) baseStart_1363843 baseEnd_1363843 := by
    simpa [prefixWord, tailWord_1363843, baseEnd_1363843] using wordTrace_append hprefix tailTrace_1363843
  have hstable : (prefixWord ++ tailWord_1363843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363843).length < 2 ^ (prefixWord ++ tailWord_1363843).sum := by decide
  have hdescent : baseEnd_1363843 < baseStart_1363843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363874 : List Nat := [3, 3, 1, 2, 4, 1, 7]
def baseStart_1363874 : Nat := 118140960795 + 1363874 * 2 ^ 59
def prefixEnd_1363874 : Nat := 4983230072969 + 3 ^ 40 * 1363874 * 2
def baseEnd_1363874 : Nat := 34583847613348250390255

theorem tailTrace_1363874 : CollatzResearch.WordTrace tailWord_1363874 prefixEnd_1363874 34583847613348250390255 := by
  unfold tailWord_1363874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436142865231225994928669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33163047640616602653143117 12436142865231225994928669)
  ·
    refine ⟨4663553574461709748098251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12436142865231225994928669 4663553574461709748098251)
    ·
      refine ⟨6995330361692564622147377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663553574461709748098251 6995330361692564622147377)
      ·
        refine ⟨5246497771269423466610533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6995330361692564622147377 5246497771269423466610533)
        ·
          refine ⟨983718332113016899989475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5246497771269423466610533 983718332113016899989475)
          ·
            refine ⟨1475577498169525349984213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983718332113016899989475 1475577498169525349984213)
            ·
              refine ⟨34583847613348250390255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1475577498169525349984213 34583847613348250390255)
              ·
                rfl

theorem cell21_1363874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 7].length) (baseStart_1363874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363874 prefixEnd_1363874 := by exact prefixLift 1363874
  have htrace : WordTrace (prefixWord ++ tailWord_1363874) baseStart_1363874 baseEnd_1363874 := by
    simpa [prefixWord, tailWord_1363874, baseEnd_1363874] using wordTrace_append hprefix tailTrace_1363874
  have hstable : (prefixWord ++ tailWord_1363874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363874).length < 2 ^ (prefixWord ++ tailWord_1363874).sum := by decide
  have hdescent : baseEnd_1363874 < baseStart_1363874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363899 : List Nat := [1, 1, 1, 1, 1, 2, 2, 12]
def baseStart_1363899 : Nat := 118140960795 + 1363899 * 2 ^ 59
def prefixEnd_1363899 : Nat := 4983230072969 + 3 ^ 40 * 1363899 * 2
def baseEnd_1363899 : Nat := 103753444620246588531859

theorem tailTrace_1363899 : CollatzResearch.WordTrace tailWord_1363899 prefixEnd_1363899 103753444620246588531859 := by
  unfold tailWord_1363899
  simp only [CollatzResearch.WordTrace]
  refine ⟨49745483285834333249374751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33163655523889555499583167 49745483285834333249374751)
  ·
    refine ⟨74618224928751499874062127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49745483285834333249374751 74618224928751499874062127)
    ·
      refine ⟨111927337393127249811093191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74618224928751499874062127 111927337393127249811093191)
      ·
        refine ⟨167891006089690874716639787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111927337393127249811093191 167891006089690874716639787)
        ·
          refine ⟨251836509134536312074959681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167891006089690874716639787 251836509134536312074959681)
          ·
            refine ⟨188877381850902234056219761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251836509134536312074959681 188877381850902234056219761)
            ·
              refine ⟨141658036388176675542164821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188877381850902234056219761 141658036388176675542164821)
              ·
                refine ⟨103753444620246588531859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 141658036388176675542164821 103753444620246588531859)
                ·
                  rfl

theorem cell21_1363899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_1363899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363899 prefixEnd_1363899 := by exact prefixLift 1363899
  have htrace : WordTrace (prefixWord ++ tailWord_1363899) baseStart_1363899 baseEnd_1363899 := by
    simpa [prefixWord, tailWord_1363899, baseEnd_1363899] using wordTrace_append hprefix tailTrace_1363899
  have hstable : (prefixWord ++ tailWord_1363899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363899).length < 2 ^ (prefixWord ++ tailWord_1363899).sum := by decide
  have hdescent : baseEnd_1363899 < baseStart_1363899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363916 : List Nat := [2, 2, 1, 4, 1, 2, 2, 7]
def baseStart_1363916 : Nat := 118140960795 + 1363916 * 2 ^ 59
def prefixEnd_1363916 : Nat := 4983230072969 + 3 ^ 40 * 1363916 * 2
def baseEnd_1363916 : Nat := 103754737830783837937403

theorem tailTrace_1363916 : CollatzResearch.WordTrace tailWord_1363916 prefixEnd_1363916 103754737830783837937403 := by
  unfold tailWord_1363916
  simp only [CollatzResearch.WordTrace]
  refine ⟨24873051663386372576371801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33164068884515163435162401 24873051663386372576371801)
  ·
    refine ⟨18654788747539779432278851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24873051663386372576371801 18654788747539779432278851)
    ·
      refine ⟨27982183121309669148418277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18654788747539779432278851 27982183121309669148418277)
      ·
        refine ⟨5246659335245562965328427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27982183121309669148418277 5246659335245562965328427)
        ·
          refine ⟨7869989002868344447992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246659335245562965328427 7869989002868344447992641)
          ·
            refine ⟨5902491752151258335994481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869989002868344447992641 5902491752151258335994481)
            ·
              refine ⟨4426868814113443751995861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902491752151258335994481 4426868814113443751995861)
              ·
                refine ⟨103754737830783837937403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4426868814113443751995861 103754737830783837937403)
                ·
                  rfl

theorem cell21_1363916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_1363916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363916 prefixEnd_1363916 := by exact prefixLift 1363916
  have htrace : WordTrace (prefixWord ++ tailWord_1363916) baseStart_1363916 baseEnd_1363916 := by
    simpa [prefixWord, tailWord_1363916, baseEnd_1363916] using wordTrace_append hprefix tailTrace_1363916
  have hstable : (prefixWord ++ tailWord_1363916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363916).length < 2 ^ (prefixWord ++ tailWord_1363916).sum := by decide
  have hdescent : baseEnd_1363916 < baseStart_1363916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363933 : List Nat := [1, 4, 3, 1, 4, 8]
def baseStart_1363933 : Nat := 118140960795 + 1363933 * 2 ^ 59
def prefixEnd_1363933 : Nat := 4983230072969 + 3 ^ 40 * 1363933 * 2
def baseEnd_1363933 : Nat := 11528447893480120815883

theorem tailTrace_1363933 : CollatzResearch.WordTrace tailWord_1363933 prefixEnd_1363933 11528447893480120815883 := by
  unfold tailWord_1363933
  simp only [CollatzResearch.WordTrace]
  refine ⟨49746723367711157056112453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33164482245140771370741635 49746723367711157056112453)
  ·
    refine ⟨9327510631445841948021085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49746723367711157056112453 9327510631445841948021085)
    ·
      refine ⟨3497816486792190730507907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9327510631445841948021085 3497816486792190730507907)
      ·
        refine ⟨5246724730188286095761861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497816486792190730507907 5246724730188286095761861)
        ·
          refine ⟨983760886910303642955349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5246724730188286095761861 983760886910303642955349)
          ·
            refine ⟨11528447893480120815883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 983760886910303642955349 11528447893480120815883)
            ·
              rfl

theorem cell21_1363933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 8].length) (baseStart_1363933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1363933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1363933 prefixEnd_1363933 := by exact prefixLift 1363933
  have htrace : WordTrace (prefixWord ++ tailWord_1363933) baseStart_1363933 baseEnd_1363933 := by
    simpa [prefixWord, tailWord_1363933, baseEnd_1363933] using wordTrace_append hprefix tailTrace_1363933
  have hstable : (prefixWord ++ tailWord_1363933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363933).length < 2 ^ (prefixWord ++ tailWord_1363933).sum := by decide
  have hdescent : baseEnd_1363933 < baseStart_1363933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364161 : List Nat := [1, 2, 6, 1, 2, 1, 8]
def baseStart_1364161 : Nat := 118140960795 + 1364161 * 2 ^ 59
def prefixEnd_1364161 : Nat := 4983230072969 + 3 ^ 40 * 1364161 * 2
def baseEnd_1364161 : Nat := 34591125092253948025375

theorem tailTrace_1364161 : CollatzResearch.WordTrace tailWord_1364161 prefixEnd_1364161 34591125092253948025375 := by
  unfold tailWord_1364161
  simp only [CollatzResearch.WordTrace]
  refine ⟨49755039210885151995412337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33170026140590101330274891 49755039210885151995412337)
  ·
    refine ⟨37316279408163863996559253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49755039210885151995412337 37316279408163863996559253)
    ·
      refine ⟨1749200597257681124838715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37316279408163863996559253 1749200597257681124838715)
      ·
        refine ⟨2623800895886521687258073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749200597257681124838715 2623800895886521687258073)
        ·
          refine ⟨1967850671914891265443555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2623800895886521687258073 1967850671914891265443555)
          ·
            refine ⟨2951776007872336898165333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967850671914891265443555 2951776007872336898165333)
            ·
              refine ⟨34591125092253948025375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2951776007872336898165333 34591125092253948025375)
              ·
                rfl

theorem cell21_1364161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 8].length) (baseStart_1364161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364161 prefixEnd_1364161 := by exact prefixLift 1364161
  have htrace : WordTrace (prefixWord ++ tailWord_1364161) baseStart_1364161 baseEnd_1364161 := by
    simpa [prefixWord, tailWord_1364161, baseEnd_1364161] using wordTrace_append hprefix tailTrace_1364161
  have hstable : (prefixWord ++ tailWord_1364161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364161).length < 2 ^ (prefixWord ++ tailWord_1364161).sum := by decide
  have hdescent : baseEnd_1364161 < baseStart_1364161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364175 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 3]
def baseStart_1364175 : Nat := 118140960795 + 1364175 * 2 ^ 59
def prefixEnd_1364175 : Nat := 4983230072969 + 3 ^ 40 * 1364175 * 2
def baseEnd_1364175 : Nat := 311323320821024618995013

theorem tailTrace_1364175 : CollatzResearch.WordTrace tailWord_1364175 prefixEnd_1364175 311323320821024618995013 := by
  unfold tailWord_1364175
  simp only [CollatzResearch.WordTrace]
  refine ⟨49755549832834432386421979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33170366555222954924281319 49755549832834432386421979)
  ·
    refine ⟨74633324749251648579632969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49755549832834432386421979 74633324749251648579632969)
    ·
      refine ⟨55974993561938736434724727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74633324749251648579632969 55974993561938736434724727)
      ·
        refine ⟨83962490342908104652087091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55974993561938736434724727 83962490342908104652087091)
        ·
          refine ⟨125943735514362156978130637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83962490342908104652087091 125943735514362156978130637)
          ·
            refine ⟨47228900817885808866798989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125943735514362156978130637 47228900817885808866798989)
            ·
              refine ⟨17710837806707178325049621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47228900817885808866798989 17710837806707178325049621)
              ·
                refine ⟨830195522189398983986701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17710837806707178325049621 830195522189398983986701)
                ·
                  refine ⟨311323320821024618995013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830195522189398983986701 311323320821024618995013)
                  ·
                    rfl

theorem cell21_1364175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].length) (baseStart_1364175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364175 prefixEnd_1364175 := by exact prefixLift 1364175
  have htrace : WordTrace (prefixWord ++ tailWord_1364175) baseStart_1364175 baseEnd_1364175 := by
    simpa [prefixWord, tailWord_1364175, baseEnd_1364175] using wordTrace_append hprefix tailTrace_1364175
  have hstable : (prefixWord ++ tailWord_1364175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364175).length < 2 ^ (prefixWord ++ tailWord_1364175).sum := by decide
  have hdescent : baseEnd_1364175 < baseStart_1364175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364195 : List Nat := [1, 1, 1, 8, 2, 1, 2, 5]
def baseStart_1364195 : Nat := 118140960795 + 1364195 * 2 ^ 59
def prefixEnd_1364195 : Nat := 4983230072969 + 3 ^ 40 * 1364195 * 2
def baseEnd_1364195 : Nat := 103775961697836342887213

theorem tailTrace_1364195 : CollatzResearch.WordTrace tailWord_1364195 prefixEnd_1364195 103775961697836342887213 := by
  unfold tailWord_1364195
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756279292761975802150039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33170852861841317201433359 49756279292761975802150039)
  ·
    refine ⟨74634418939142963703225059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49756279292761975802150039 74634418939142963703225059)
    ·
      refine ⟨111951628408714445554837589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74634418939142963703225059 111951628408714445554837589)
      ·
        refine ⟨1311933145414622408845753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 111951628408714445554837589 1311933145414622408845753)
        ·
          refine ⟨983949859060966806634315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311933145414622408845753 983949859060966806634315)
          ·
            refine ⟨1475924788591450209951473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983949859060966806634315 1475924788591450209951473)
            ·
              refine ⟨1106943591443587657463605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475924788591450209951473 1106943591443587657463605)
              ·
                refine ⟨103775961697836342887213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1106943591443587657463605 103775961697836342887213)
                ·
                  rfl

theorem cell21_1364195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].length) (baseStart_1364195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364195 prefixEnd_1364195 := by exact prefixLift 1364195
  have htrace : WordTrace (prefixWord ++ tailWord_1364195) baseStart_1364195 baseEnd_1364195 := by
    simpa [prefixWord, tailWord_1364195, baseEnd_1364195] using wordTrace_append hprefix tailTrace_1364195
  have hstable : (prefixWord ++ tailWord_1364195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364195).length < 2 ^ (prefixWord ++ tailWord_1364195).sum := by decide
  have hdescent : baseEnd_1364195 < baseStart_1364195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364203 : List Nat := [1, 1, 1, 1, 2, 5, 3, 7]
def baseStart_1364203 : Nat := 118140960795 + 1364203 * 2 ^ 59
def prefixEnd_1364203 : Nat := 4983230072969 + 3 ^ 40 * 1364203 * 2
def baseEnd_1364203 : Nat := 103776570267500930842763

theorem tailTrace_1364203 : CollatzResearch.WordTrace tailWord_1364203 prefixEnd_1364203 103776570267500930842763 := by
  unfold tailWord_1364203
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756571076732993168441263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33171047384488662112294175 49756571076732993168441263)
  ·
    refine ⟨74634856615099489752661895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49756571076732993168441263 74634856615099489752661895)
    ·
      refine ⟨111952284922649234628992843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74634856615099489752661895 111952284922649234628992843)
      ·
        refine ⟨167928427383973851943489265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111952284922649234628992843 167928427383973851943489265)
        ·
          refine ⟨125946320537980388957616949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167928427383973851943489265 125946320537980388957616949)
          ·
            refine ⟨11807467550435661464776589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125946320537980388957616949 11807467550435661464776589)
            ·
              refine ⟨4427800331413373049291221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11807467550435661464776589 4427800331413373049291221)
              ·
                refine ⟨103776570267500930842763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4427800331413373049291221 103776570267500930842763)
                ·
                  rfl

theorem cell21_1364203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_1364203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364203 prefixEnd_1364203 := by exact prefixLift 1364203
  have htrace : WordTrace (prefixWord ++ tailWord_1364203) baseStart_1364203 baseEnd_1364203 := by
    simpa [prefixWord, tailWord_1364203, baseEnd_1364203] using wordTrace_append hprefix tailTrace_1364203
  have hstable : (prefixWord ++ tailWord_1364203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364203).length < 2 ^ (prefixWord ++ tailWord_1364203).sum := by decide
  have hdescent : baseEnd_1364203 < baseStart_1364203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364220 : List Nat := [2, 2, 2, 1, 4, 3, 7]
def baseStart_1364220 : Nat := 118140960795 + 1364220 * 2 ^ 59
def prefixEnd_1364220 : Nat := 4983230072969 + 3 ^ 40 * 1364220 * 2
def baseEnd_1364220 : Nat := 34592621159346060082769

theorem tailTrace_1364220 : CollatzResearch.WordTrace tailWord_1364220 prefixEnd_1364220 34592621159346060082769 := by
  unfold tailWord_1364220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878595558835702535905057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33171460745114270047873409 24878595558835702535905057)
  ·
    refine ⟨18658946669126776901928793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24878595558835702535905057 18658946669126776901928793)
    ·
      refine ⟨13994210001845082676446595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18658946669126776901928793 13994210001845082676446595)
      ·
        refine ⟨20991315002767624014669893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13994210001845082676446595 20991315002767624014669893)
        ·
          refine ⟨3935871563018929502750605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20991315002767624014669893 3935871563018929502750605)
          ·
            refine ⟨1475951836132098563531477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3935871563018929502750605 1475951836132098563531477)
            ·
              refine ⟨34592621159346060082769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1475951836132098563531477 34592621159346060082769)
              ·
                rfl

theorem cell21_1364220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 7].length) (baseStart_1364220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364220 prefixEnd_1364220 := by exact prefixLift 1364220
  have htrace : WordTrace (prefixWord ++ tailWord_1364220) baseStart_1364220 baseEnd_1364220 := by
    simpa [prefixWord, tailWord_1364220, baseEnd_1364220] using wordTrace_append hprefix tailTrace_1364220
  have hstable : (prefixWord ++ tailWord_1364220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364220).length < 2 ^ (prefixWord ++ tailWord_1364220).sum := by decide
  have hdescent : baseEnd_1364220 < baseStart_1364220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364226 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1364226 : Nat := 118140960795 + 1364226 * 2 ^ 59
def prefixEnd_1364226 : Nat := 4983230072969 + 3 ^ 40 * 1364226 * 2
def baseEnd_1364226 : Nat := 311334959715859863644909

theorem tailTrace_1364226 : CollatzResearch.WordTrace tailWord_1364226 prefixEnd_1364226 311334959715859863644909 := by
  unfold tailWord_1364226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439352488912417024132133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33171606637099778731019021 12439352488912417024132133)
  ·
    refine ⟨2332378591671078192024775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12439352488912417024132133 2332378591671078192024775)
    ·
      refine ⟨3498567887506617288037163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332378591671078192024775 3498567887506617288037163)
      ·
        refine ⟨5247851831259925932055745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3498567887506617288037163 5247851831259925932055745)
        ·
          refine ⟨3935888873444944449041809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247851831259925932055745 3935888873444944449041809)
          ·
            refine ⟨2951916655083708336781357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3935888873444944449041809 2951916655083708336781357)
            ·
              refine ⟨1106968745656390626293009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2951916655083708336781357 1106968745656390626293009)
              ·
                refine ⟨830226559242292969719757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106968745656390626293009 830226559242292969719757)
                ·
                  refine ⟨311334959715859863644909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830226559242292969719757 311334959715859863644909)
                  ·
                    rfl

theorem cell21_1364226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1364226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364226 prefixEnd_1364226 := by exact prefixLift 1364226
  have htrace : WordTrace (prefixWord ++ tailWord_1364226) baseStart_1364226 baseEnd_1364226 := by
    simpa [prefixWord, tailWord_1364226, baseEnd_1364226] using wordTrace_append hprefix tailTrace_1364226
  have hstable : (prefixWord ++ tailWord_1364226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364226).length < 2 ^ (prefixWord ++ tailWord_1364226).sum := by decide
  have hdescent : baseEnd_1364226 < baseStart_1364226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364282 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1364282 : Nat := 118140960795 + 1364282 * 2 ^ 59
def prefixEnd_1364282 : Nat := 4983230072969 + 3 ^ 40 * 1364282 * 2
def baseEnd_1364282 : Nat := 311347739678816210711461

theorem tailTrace_1364282 : CollatzResearch.WordTrace tailWord_1364282 prefixEnd_1364282 311347739678816210711461 := by
  unfold tailWord_1364282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439863110861697415141775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33172968295631193107044733 12439863110861697415141775)
  ·
    refine ⟨18659794666292546122712663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12439863110861697415141775 18659794666292546122712663)
    ·
      refine ⟨27989691999438819184068995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18659794666292546122712663 27989691999438819184068995)
      ·
        refine ⟨41984537999158228776103493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27989691999438819184068995 41984537999158228776103493)
        ·
          refine ⟨7872100874842167895519405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41984537999158228776103493 7872100874842167895519405)
          ·
            refine ⟨2952037828065812960819777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7872100874842167895519405 2952037828065812960819777)
            ·
              refine ⟨2214028371049359720614833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952037828065812960819777 2214028371049359720614833)
              ·
                refine ⟨1660521278287019790461125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214028371049359720614833 1660521278287019790461125)
                ·
                  refine ⟨311347739678816210711461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660521278287019790461125 311347739678816210711461)
                  ·
                    rfl

theorem cell21_1364282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1364282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364282 prefixEnd_1364282 := by exact prefixLift 1364282
  have htrace : WordTrace (prefixWord ++ tailWord_1364282) baseStart_1364282 baseEnd_1364282 := by
    simpa [prefixWord, tailWord_1364282, baseEnd_1364282] using wordTrace_append hprefix tailTrace_1364282
  have hstable : (prefixWord ++ tailWord_1364282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364282).length < 2 ^ (prefixWord ++ tailWord_1364282).sum := by decide
  have hdescent : baseEnd_1364282 < baseStart_1364282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364476 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1364476 : Nat := 118140960795 + 1364476 * 2 ^ 59
def prefixEnd_1364476 : Nat := 4983230072969 + 3 ^ 40 * 1364476 * 2
def baseEnd_1364476 : Nat := 311392013121914984477731

theorem tailTrace_1364476 : CollatzResearch.WordTrace tailWord_1364476 prefixEnd_1364476 311392013121914984477731 := by
  unfold tailWord_1364476
  simp only [CollatzResearch.WordTrace]
  refine ⟨24883264102371980396564641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33177685469829307195419521 24883264102371980396564641)
  ·
    refine ⟨18662448076778985297423481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24883264102371980396564641 18662448076778985297423481)
    ·
      refine ⟨13996836057584238973067611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18662448076778985297423481 13996836057584238973067611)
      ·
        refine ⟨20995254086376358459601417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13996836057584238973067611 20995254086376358459601417)
        ·
          refine ⟨15746440564782268844701063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20995254086376358459601417 15746440564782268844701063)
          ·
            refine ⟨23619660847173403267051595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15746440564782268844701063 23619660847173403267051595)
            ·
              refine ⟨35429491270760104900577393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23619660847173403267051595 35429491270760104900577393)
              ·
                refine ⟨26572118453070078675433045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35429491270760104900577393 26572118453070078675433045)
                ·
                  refine ⟨311392013121914984477731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26572118453070078675433045 311392013121914984477731)
                  ·
                    rfl

theorem cell21_1364476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1364476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364476 prefixEnd_1364476 := by exact prefixLift 1364476
  have htrace : WordTrace (prefixWord ++ tailWord_1364476) baseStart_1364476 baseEnd_1364476 := by
    simpa [prefixWord, tailWord_1364476, baseEnd_1364476] using wordTrace_append hprefix tailTrace_1364476
  have hstable : (prefixWord ++ tailWord_1364476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364476).length < 2 ^ (prefixWord ++ tailWord_1364476).sum := by decide
  have hdescent : baseEnd_1364476 < baseStart_1364476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364482 : List Nat := [3, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1364482 : Nat := 118140960795 + 1364482 * 2 ^ 59
def prefixEnd_1364482 : Nat := 4983230072969 + 3 ^ 40 * 1364482 * 2
def baseEnd_1364482 : Nat := 103797794134553435792573

theorem tailTrace_1364482 : CollatzResearch.WordTrace tailWord_1364482 prefixEnd_1364482 103797794134553435792573 := by
  unfold tailWord_1364482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441686760680555954461925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33177831361814815878565133 12441686760680555954461925)
  ·
    refine ⟨2332816267627604241461611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12441686760680555954461925 2332816267627604241461611)
    ·
      refine ⟨3499224401441406362192417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332816267627604241461611 3499224401441406362192417)
      ·
        refine ⟨2624418301081054771644313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3499224401441406362192417 2624418301081054771644313)
        ·
          refine ⟨1968313725810791078733235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624418301081054771644313 1968313725810791078733235)
          ·
            refine ⟨2952470588716186618099853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968313725810791078733235 2952470588716186618099853)
            ·
              refine ⟨1107176470768569981787445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952470588716186618099853 1107176470768569981787445)
              ·
                refine ⟨103797794134553435792573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107176470768569981787445 103797794134553435792573)
                ·
                  rfl

theorem cell21_1364482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1364482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364482 prefixEnd_1364482 := by exact prefixLift 1364482
  have htrace : WordTrace (prefixWord ++ tailWord_1364482) baseStart_1364482 baseEnd_1364482 := by
    simpa [prefixWord, tailWord_1364482, baseEnd_1364482] using wordTrace_append hprefix tailTrace_1364482
  have hstable : (prefixWord ++ tailWord_1364482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364482).length < 2 ^ (prefixWord ++ tailWord_1364482).sum := by decide
  have hdescent : baseEnd_1364482 < baseStart_1364482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364538 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1364538 : Nat := 118140960795 + 1364538 * 2 ^ 59
def prefixEnd_1364538 : Nat := 4983230072969 + 3 ^ 40 * 1364538 * 2
def baseEnd_1364538 : Nat := 311406162366616654444271

theorem tailTrace_1364538 : CollatzResearch.WordTrace tailWord_1364538 prefixEnd_1364538 311406162366616654444271 := by
  unfold tailWord_1364538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442197382629836345471567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33179193020346230254590845 12442197382629836345471567)
  ·
    refine ⟨18663296073944754518207351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12442197382629836345471567 18663296073944754518207351)
    ·
      refine ⟨27994944110917131777311027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663296073944754518207351 27994944110917131777311027)
      ·
        refine ⟨41992416166375697665966541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27994944110917131777311027 41992416166375697665966541)
        ·
          refine ⟨15747156062390886624737453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41992416166375697665966541 15747156062390886624737453)
          ·
            refine ⟨5905183523396582484276545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15747156062390886624737453 5905183523396582484276545)
            ·
              refine ⟨4428887642547436863207409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905183523396582484276545 4428887642547436863207409)
              ·
                refine ⟨3321665731910577647405557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428887642547436863207409 3321665731910577647405557)
                ·
                  refine ⟨311406162366616654444271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321665731910577647405557 311406162366616654444271)
                  ·
                    rfl

theorem cell21_1364538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1364538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364538 prefixEnd_1364538 := by exact prefixLift 1364538
  have htrace : WordTrace (prefixWord ++ tailWord_1364538) baseStart_1364538 baseEnd_1364538 := by
    simpa [prefixWord, tailWord_1364538, baseEnd_1364538] using wordTrace_append hprefix tailTrace_1364538
  have hstable : (prefixWord ++ tailWord_1364538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364538).length < 2 ^ (prefixWord ++ tailWord_1364538).sum := by decide
  have hdescent : baseEnd_1364538 < baseStart_1364538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364541 : List Nat := [1, 4, 1, 3, 2, 3, 2, 5]
def baseStart_1364541 : Nat := 118140960795 + 1364541 * 2 ^ 59
def prefixEnd_1364541 : Nat := 4983230072969 + 3 ^ 40 * 1364541 * 2
def baseEnd_1364541 : Nat := 103802282335829771964755

theorem tailTrace_1364541 : CollatzResearch.WordTrace tailWord_1364541 prefixEnd_1364541 103802282335829771964755 := by
  unfold tailWord_1364541
  simp only [CollatzResearch.WordTrace]
  refine ⟨49768898949508476894245477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33179265966338984596163651 49768898949508476894245477)
  ·
    refine ⟨9331668553032839417671027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49768898949508476894245477 9331668553032839417671027)
    ·
      refine ⟨13997502829549259126506541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9331668553032839417671027 13997502829549259126506541)
      ·
        refine ⟨5249063561080972172439953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13997502829549259126506541 5249063561080972172439953)
        ·
          refine ⟨3936797670810729129329965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249063561080972172439953 3936797670810729129329965)
          ·
            refine ⟨1476299126554023423498737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3936797670810729129329965 1476299126554023423498737)
            ·
              refine ⟨1107224344915517567624053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476299126554023423498737 1107224344915517567624053)
              ·
                refine ⟨103802282335829771964755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107224344915517567624053 103802282335829771964755)
                ·
                  rfl

theorem cell21_1364541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].length) (baseStart_1364541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364541 prefixEnd_1364541 := by exact prefixLift 1364541
  have htrace : WordTrace (prefixWord ++ tailWord_1364541) baseStart_1364541 baseEnd_1364541 := by
    simpa [prefixWord, tailWord_1364541, baseEnd_1364541] using wordTrace_append hprefix tailTrace_1364541
  have hstable : (prefixWord ++ tailWord_1364541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364541).length < 2 ^ (prefixWord ++ tailWord_1364541).sum := by decide
  have hdescent : baseEnd_1364541 < baseStart_1364541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364555 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 3]
def baseStart_1364555 : Nat := 118140960795 + 1364555 * 2 ^ 59
def prefixEnd_1364555 : Nat := 4983230072969 + 3 ^ 40 * 1364555 * 2
def baseEnd_1364555 : Nat := 311410041998228402660903

theorem tailTrace_1364555 : CollatzResearch.WordTrace tailWord_1364555 prefixEnd_1364555 311410041998228402660903 := by
  unfold tailWord_1364555
  simp only [CollatzResearch.WordTrace]
  refine ⟨49769409571457757285255119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33179606380971838190170079 49769409571457757285255119)
  ·
    refine ⟨74654114357186635927882679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49769409571457757285255119 74654114357186635927882679)
    ·
      refine ⟨111981171535779953891824019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74654114357186635927882679 111981171535779953891824019)
      ·
        refine ⟨167971757303669930837736029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111981171535779953891824019 167971757303669930837736029)
        ·
          refine ⟨62989408988876224064151011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167971757303669930837736029 62989408988876224064151011)
          ·
            refine ⟨94484113483314336096226517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62989408988876224064151011 94484113483314336096226517)
            ·
              refine ⟨2214471409765179752255309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94484113483314336096226517 2214471409765179752255309)
              ·
                refine ⟨830426778661942407095741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2214471409765179752255309 830426778661942407095741)
                ·
                  refine ⟨311410041998228402660903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830426778661942407095741 311410041998228402660903)
                  ·
                    rfl

theorem cell21_1364555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].length) (baseStart_1364555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364555 prefixEnd_1364555 := by exact prefixLift 1364555
  have htrace : WordTrace (prefixWord ++ tailWord_1364555) baseStart_1364555 baseEnd_1364555 := by
    simpa [prefixWord, tailWord_1364555, baseEnd_1364555] using wordTrace_append hprefix tailTrace_1364555
  have hstable : (prefixWord ++ tailWord_1364555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364555).length < 2 ^ (prefixWord ++ tailWord_1364555).sum := by decide
  have hdescent : baseEnd_1364555 < baseStart_1364555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364572 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1364572 : Nat := 118140960795 + 1364572 * 2 ^ 59
def prefixEnd_1364572 : Nat := 4983230072969 + 3 ^ 40 * 1364572 * 2
def baseEnd_1364572 : Nat := 311413921629840150877535

theorem tailTrace_1364572 : CollatzResearch.WordTrace tailWord_1364572 prefixEnd_1364572 311413921629840150877535 := by
  unfold tailWord_1364572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885014806198084594311985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33180019741597446125749313 24885014806198084594311985)
  ·
    refine ⟨18663761104648563445733989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24885014806198084594311985 18663761104648563445733989)
    ·
      refine ⟨3499455207121605646075123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18663761104648563445733989 3499455207121605646075123)
      ·
        refine ⟨5249182810682408469112685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499455207121605646075123 5249182810682408469112685)
        ·
          refine ⟨1968443554005903175917257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5249182810682408469112685 1968443554005903175917257)
          ·
            refine ⟨1476332665504427381937943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968443554005903175917257 1476332665504427381937943)
            ·
              refine ⟨2214498998256641072906915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476332665504427381937943 2214498998256641072906915)
              ·
                refine ⟨3321748497384961609360373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214498998256641072906915 3321748497384961609360373)
                ·
                  refine ⟨311413921629840150877535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321748497384961609360373 311413921629840150877535)
                  ·
                    rfl

theorem cell21_1364572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1364572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364572 prefixEnd_1364572 := by exact prefixLift 1364572
  have htrace : WordTrace (prefixWord ++ tailWord_1364572) baseStart_1364572 baseEnd_1364572 := by
    simpa [prefixWord, tailWord_1364572, baseEnd_1364572] using wordTrace_append hprefix tailTrace_1364572
  have hstable : (prefixWord ++ tailWord_1364572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364572).length < 2 ^ (prefixWord ++ tailWord_1364572).sum := by decide
  have hdescent : baseEnd_1364572 < baseStart_1364572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364631 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 3]
def baseStart_1364631 : Nat := 118140960795 + 1364631 * 2 ^ 59
def prefixEnd_1364631 : Nat := 4983230072969 + 3 ^ 40 * 1364631 * 2
def baseEnd_1364631 : Nat := 311427386233669159394081

theorem tailTrace_1364631 : CollatzResearch.WordTrace tailWord_1364631 prefixEnd_1364631 311427386233669159394081 := by
  unfold tailWord_1364631
  simp only [CollatzResearch.WordTrace]
  refine ⟨49772181519182422265021747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33181454346121614843347831 49772181519182422265021747)
  ·
    refine ⟨74658272278773633397532621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49772181519182422265021747 74658272278773633397532621)
    ·
      refine ⟨27996852104540112524074733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74658272278773633397532621 27996852104540112524074733)
      ·
        refine ⟨10498819539202542196528025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27996852104540112524074733 10498819539202542196528025)
        ·
          refine ⟨7874114654401906647396019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10498819539202542196528025 7874114654401906647396019)
          ·
            refine ⟨11811171981602859971094029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7874114654401906647396019 11811171981602859971094029)
            ·
              refine ⟨4429189493101072489160261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11811171981602859971094029 4429189493101072489160261)
              ·
                refine ⟨830473029956451091717549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4429189493101072489160261 830473029956451091717549)
                ·
                  refine ⟨311427386233669159394081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830473029956451091717549 311427386233669159394081)
                  ·
                    rfl

theorem cell21_1364631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].length) (baseStart_1364631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364631 prefixEnd_1364631 := by exact prefixLift 1364631
  have htrace : WordTrace (prefixWord ++ tailWord_1364631) baseStart_1364631 baseEnd_1364631 := by
    simpa [prefixWord, tailWord_1364631, baseEnd_1364631] using wordTrace_append hprefix tailTrace_1364631
  have hstable : (prefixWord ++ tailWord_1364631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364631).length < 2 ^ (prefixWord ++ tailWord_1364631).sum := by decide
  have hdescent : baseEnd_1364631 < baseStart_1364631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364634 : List Nat := [3, 1, 1, 6, 2, 1, 1, 6]
def baseStart_1364634 : Nat := 118140960795 + 1364634 * 2 ^ 59
def prefixEnd_1364634 : Nat := 4983230072969 + 3 ^ 40 * 1364634 * 2
def baseEnd_1364634 : Nat := 103809356958180606948025

theorem tailTrace_1364634 : CollatzResearch.WordTrace tailWord_1364634 prefixEnd_1364634 103809356958180606948025 := by
  unfold tailWord_1364634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443072734542888444345239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33181527292114369184920637 12443072734542888444345239)
  ·
    refine ⟨18664609101814332666517859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443072734542888444345239 18664609101814332666517859)
    ·
      refine ⟨27996913652721498999776789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18664609101814332666517859 27996913652721498999776789)
      ·
        refine ⟨1312355327471320265614537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27996913652721498999776789 1312355327471320265614537)
        ·
          refine ⟨984266495603490199210903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312355327471320265614537 984266495603490199210903)
          ·
            refine ⟨1476399743405235298816355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984266495603490199210903 1476399743405235298816355)
            ·
              refine ⟨2214599615107852948224533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476399743405235298816355 2214599615107852948224533)
              ·
                refine ⟨103809356958180606948025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2214599615107852948224533 103809356958180606948025)
                ·
                  rfl

theorem cell21_1364634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_1364634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364634 prefixEnd_1364634 := by exact prefixLift 1364634
  have htrace : WordTrace (prefixWord ++ tailWord_1364634) baseStart_1364634 baseEnd_1364634 := by
    simpa [prefixWord, tailWord_1364634, baseEnd_1364634] using wordTrace_append hprefix tailTrace_1364634
  have hstable : (prefixWord ++ tailWord_1364634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364634).length < 2 ^ (prefixWord ++ tailWord_1364634).sum := by decide
  have hdescent : baseEnd_1364634 < baseStart_1364634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364794 : List Nat := [3, 1, 1, 1, 15]
def baseStart_1364794 : Nat := 118140960795 + 1364794 * 2 ^ 59
def prefixEnd_1364794 : Nat := 4983230072969 + 3 ^ 40 * 1364794 * 2
def baseEnd_1364794 : Nat := 3845241790795272817001

theorem tailTrace_1364794 : CollatzResearch.WordTrace tailWord_1364794 prefixEnd_1364794 3845241790795272817001 := by
  unfold tailWord_1364794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12444531654397975275801359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33185417745061267402136957 12444531654397975275801359)
  ·
    refine ⟨18666797481596962913702039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12444531654397975275801359 18666797481596962913702039)
    ·
      refine ⟨28000196222395444370553059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18666797481596962913702039 28000196222395444370553059)
      ·
        refine ⟨42000294333593166555829589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28000196222395444370553059 42000294333593166555829589)
        ·
          refine ⟨3845241790795272817001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 42000294333593166555829589 3845241790795272817001)
          ·
            rfl

theorem cell21_1364794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 15].length) (baseStart_1364794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364794 prefixEnd_1364794 := by exact prefixLift 1364794
  have htrace : WordTrace (prefixWord ++ tailWord_1364794) baseStart_1364794 baseEnd_1364794 := by
    simpa [prefixWord, tailWord_1364794, baseEnd_1364794] using wordTrace_append hprefix tailTrace_1364794
  have hstable : (prefixWord ++ tailWord_1364794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364794).length < 2 ^ (prefixWord ++ tailWord_1364794).sum := by decide
  have hdescent : baseEnd_1364794 < baseStart_1364794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364825 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_1364825 : Nat := 118140960795 + 1364825 * 2 ^ 59
def prefixEnd_1364825 : Nat := 4983230072969 + 3 ^ 40 * 1364825 * 2
def baseEnd_1364825 : Nat := 311471659676767933160351

theorem tailTrace_1364825 : CollatzResearch.WordTrace tailWord_1364825 prefixEnd_1364825 311471659676767933160351 := by
  unfold tailWord_1364825
  simp only [CollatzResearch.WordTrace]
  refine ⟨49779257280479593397583929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33186171520319728931722619 49779257280479593397583929)
  ·
    refine ⟨37334442960359695048187947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49779257280479593397583929 37334442960359695048187947)
    ·
      refine ⟨56001664440539542572281921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37334442960359695048187947 56001664440539542572281921)
      ·
        refine ⟨42001248330404656929211441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56001664440539542572281921 42001248330404656929211441)
        ·
          refine ⟨31500936247803492696908581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42001248330404656929211441 31500936247803492696908581)
          ·
            refine ⟨5906425546463154880670359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31500936247803492696908581 5906425546463154880670359)
            ·
              refine ⟨8859638319694732321005539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906425546463154880670359 8859638319694732321005539)
              ·
                refine ⟨13289457479542098481508309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859638319694732321005539 13289457479542098481508309)
                ·
                  refine ⟨311471659676767933160351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13289457479542098481508309 311471659676767933160351)
                  ·
                    rfl

theorem cell21_1364825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_1364825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364825 prefixEnd_1364825 := by exact prefixLift 1364825
  have htrace : WordTrace (prefixWord ++ tailWord_1364825) baseStart_1364825 baseEnd_1364825 := by
    simpa [prefixWord, tailWord_1364825, baseEnd_1364825] using wordTrace_append hprefix tailTrace_1364825
  have hstable : (prefixWord ++ tailWord_1364825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364825).length < 2 ^ (prefixWord ++ tailWord_1364825).sum := by decide
  have hdescent : baseEnd_1364825 < baseStart_1364825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364856 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1364856 : Nat := 118140960795 + 1364856 * 2 ^ 59
def prefixEnd_1364856 : Nat := 4983230072969 + 3 ^ 40 * 1364856 * 2
def baseEnd_1364856 : Nat := 311478734299118768143621

theorem tailTrace_1364856 : CollatzResearch.WordTrace tailWord_1364856 prefixEnd_1364856 311478734299118768143621 := by
  unfold tailWord_1364856
  simp only [CollatzResearch.WordTrace]
  refine ⟨24890193971683642845981211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33186925295578190461308281 24890193971683642845981211)
  ·
    refine ⟨37335290957525464268971817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24890193971683642845981211 37335290957525464268971817)
    ·
      refine ⟨28001468218144098201728863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37335290957525464268971817 28001468218144098201728863)
      ·
        refine ⟨42002202327216147302593295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28001468218144098201728863 42002202327216147302593295)
        ·
          refine ⟨63003303490824220953889943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42002202327216147302593295 63003303490824220953889943)
          ·
            refine ⟨94504955236236331430834915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63003303490824220953889943 94504955236236331430834915)
            ·
              refine ⟨141757432854354497146252373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94504955236236331430834915 141757432854354497146252373)
              ·
                refine ⟨1661219916261966763432645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 141757432854354497146252373 1661219916261966763432645)
                ·
                  refine ⟨311478734299118768143621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661219916261966763432645 311478734299118768143621)
                  ·
                    rfl

theorem cell21_1364856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1364856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364856 prefixEnd_1364856 := by exact prefixLift 1364856
  have htrace : WordTrace (prefixWord ++ tailWord_1364856) baseStart_1364856 baseEnd_1364856 := by
    simpa [prefixWord, tailWord_1364856, baseEnd_1364856] using wordTrace_append hprefix tailTrace_1364856
  have hstable : (prefixWord ++ tailWord_1364856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364856).length < 2 ^ (prefixWord ++ tailWord_1364856).sum := by decide
  have hdescent : baseEnd_1364856 < baseStart_1364856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364991 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_1364991 : Nat := 118140960795 + 1364991 * 2 ^ 59
def prefixEnd_1364991 : Nat := 4983230072969 + 3 ^ 40 * 1364991 * 2
def baseEnd_1364991 : Nat := 311509543138388533393345

theorem tailTrace_1364991 : CollatzResearch.WordTrace tailWord_1364991 prefixEnd_1364991 311509543138388533393345 := by
  unfold tailWord_1364991
  simp only [CollatzResearch.WordTrace]
  refine ⟨49785311797878203748126827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33190207865252135832084551 49785311797878203748126827)
  ·
    refine ⟨74677967696817305622190241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49785311797878203748126827 74677967696817305622190241)
    ·
      refine ⟨56008475772612979216642681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74677967696817305622190241 56008475772612979216642681)
      ·
        refine ⟨42006356829459734412482011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56008475772612979216642681 42006356829459734412482011)
        ·
          refine ⟨63009535244189601618723017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42006356829459734412482011 63009535244189601618723017)
          ·
            refine ⟨47257151433142201214042263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63009535244189601618723017 47257151433142201214042263)
            ·
              refine ⟨70885727149713301821063395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47257151433142201214042263 70885727149713301821063395)
              ·
                refine ⟨106328590724569952731595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70885727149713301821063395 106328590724569952731595093)
                ·
                  refine ⟨311509543138388533393345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 106328590724569952731595093 311509543138388533393345)
                  ·
                    rfl

theorem cell21_1364991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_1364991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1364991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1364991 prefixEnd_1364991 := by exact prefixLift 1364991
  have htrace : WordTrace (prefixWord ++ tailWord_1364991) baseStart_1364991 baseEnd_1364991 := by
    simpa [prefixWord, tailWord_1364991, baseEnd_1364991] using wordTrace_append hprefix tailTrace_1364991
  have hstable : (prefixWord ++ tailWord_1364991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364991).length < 2 ^ (prefixWord ++ tailWord_1364991).sum := by decide
  have hdescent : baseEnd_1364991 < baseStart_1364991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365025 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_1365025 : Nat := 118140960795 + 1365025 * 2 ^ 59
def prefixEnd_1365025 : Nat := 4983230072969 + 3 ^ 40 * 1365025 * 2
def baseEnd_1365025 : Nat := 311517302401612029826609

theorem tailTrace_1365025 : CollatzResearch.WordTrace tailWord_1365025 prefixEnd_1365025 311517302401612029826609 := by
  unfold tailWord_1365025
  simp only [CollatzResearch.WordTrace]
  refine ⟨49786551879755027554864529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33191034586503351703243019 49786551879755027554864529)
  ·
    refine ⟨37339913909816270666148397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49786551879755027554864529 37339913909816270666148397)
    ·
      refine ⟨14002467716181101499805649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37339913909816270666148397 14002467716181101499805649)
      ·
        refine ⟨10501850787135826124854237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14002467716181101499805649 10501850787135826124854237)
        ·
          refine ⟨3938194045175934796820339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10501850787135826124854237 3938194045175934796820339)
          ·
            refine ⟨5907291067763902195230509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938194045175934796820339 5907291067763902195230509)
            ·
              refine ⟨2215234150411463323211441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5907291067763902195230509 2215234150411463323211441)
              ·
                refine ⟨1661425612808597492408581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215234150411463323211441 1661425612808597492408581)
                ·
                  refine ⟨311517302401612029826609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661425612808597492408581 311517302401612029826609)
                  ·
                    rfl

theorem cell21_1365025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_1365025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365025 prefixEnd_1365025 := by exact prefixLift 1365025
  have htrace : WordTrace (prefixWord ++ tailWord_1365025) baseStart_1365025 baseEnd_1365025 := by
    simpa [prefixWord, tailWord_1365025, baseEnd_1365025] using wordTrace_append hprefix tailTrace_1365025
  have hstable : (prefixWord ++ tailWord_1365025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365025).length < 2 ^ (prefixWord ++ tailWord_1365025).sum := by decide
  have hdescent : baseEnd_1365025 < baseStart_1365025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365084 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1365084 : Nat := 118140960795 + 1365084 * 2 ^ 59
def prefixEnd_1365084 : Nat := 4983230072969 + 3 ^ 40 * 1365084 * 2
def baseEnd_1365084 : Nat := 311530767005441038343155

theorem tailTrace_1365084 : CollatzResearch.WordTrace tailWord_1365084 prefixEnd_1365084 311530767005441038343155 := by
  unfold tailWord_1365084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894351893270640315631153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33192469191027520420841537 24894351893270640315631153)
  ·
    refine ⟨18670763919952980236723365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24894351893270640315631153 18670763919952980236723365)
    ·
      refine ⟨3500768234991183794385631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18670763919952980236723365 3500768234991183794385631)
      ·
        refine ⟨5251152352486775691578447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500768234991183794385631 5251152352486775691578447)
        ·
          refine ⟨7876728528730163537367671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251152352486775691578447 7876728528730163537367671)
          ·
            refine ⟨11815092793095245306051507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876728528730163537367671 11815092793095245306051507)
            ·
              refine ⟨17722639189642867959077261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815092793095245306051507 17722639189642867959077261)
              ·
                refine ⟨6645989696116075484653973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17722639189642867959077261 6645989696116075484653973)
                ·
                  refine ⟨311530767005441038343155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6645989696116075484653973 311530767005441038343155)
                  ·
                    rfl

theorem cell21_1365084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1365084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365084 prefixEnd_1365084 := by exact prefixLift 1365084
  have htrace : WordTrace (prefixWord ++ tailWord_1365084) baseStart_1365084 baseEnd_1365084 := by
    simpa [prefixWord, tailWord_1365084, baseEnd_1365084] using wordTrace_append hprefix tailTrace_1365084
  have hstable : (prefixWord ++ tailWord_1365084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365084).length < 2 ^ (prefixWord ++ tailWord_1365084).sum := by decide
  have hdescent : baseEnd_1365084 < baseStart_1365084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365087 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 3]
def baseStart_1365087 : Nat := 118140960795 + 1365087 * 2 ^ 59
def prefixEnd_1365087 : Nat := 4983230072969 + 3 ^ 40 * 1365087 * 2
def baseEnd_1365087 : Nat := 311531451646313699793149

theorem tailTrace_1365087 : CollatzResearch.WordTrace tailWord_1365087 prefixEnd_1365087 311531451646313699793149 := by
  unfold tailWord_1365087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49788813205530412143621515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33192542137020274762414343 49788813205530412143621515)
  ·
    refine ⟨74683219808295618215432273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49788813205530412143621515 74683219808295618215432273)
    ·
      refine ⟨56012414856221713661574205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74683219808295618215432273 56012414856221713661574205)
      ·
        refine ⟨21004655571083142623090327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56012414856221713661574205 21004655571083142623090327)
        ·
          refine ⟨31506983356624713934635491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21004655571083142623090327 31506983356624713934635491)
          ·
            refine ⟨47260475034937070901953237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31506983356624713934635491 47260475034937070901953237)
            ·
              refine ⟨1107667383631337599264529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47260475034937070901953237 1107667383631337599264529)
              ·
                refine ⟨830750537723503199448397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107667383631337599264529 830750537723503199448397)
                ·
                  refine ⟨311531451646313699793149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830750537723503199448397 311531451646313699793149)
                  ·
                    rfl

theorem cell21_1365087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].length) (baseStart_1365087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365087 prefixEnd_1365087 := by exact prefixLift 1365087
  have htrace : WordTrace (prefixWord ++ tailWord_1365087) baseStart_1365087 baseEnd_1365087 := by
    simpa [prefixWord, tailWord_1365087, baseEnd_1365087] using wordTrace_append hprefix tailTrace_1365087
  have hstable : (prefixWord ++ tailWord_1365087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365087).length < 2 ^ (prefixWord ++ tailWord_1365087).sum := by decide
  have hdescent : baseEnd_1365087 < baseStart_1365087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365101 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1365101 : Nat := 118140960795 + 1365101 * 2 ^ 59
def prefixEnd_1365101 : Nat := 4983230072969 + 3 ^ 40 * 1365101 * 2
def baseEnd_1365101 : Nat := 311534646637052786559787

theorem tailTrace_1365101 : CollatzResearch.WordTrace tailWord_1365101 prefixEnd_1365101 311534646637052786559787 := by
  unfold tailWord_1365101
  simp only [CollatzResearch.WordTrace]
  refine ⟨49789323827479692534631157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33192882551653128356420771 49789323827479692534631157)
  ·
    refine ⟨4667749108826221175121671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49789323827479692534631157 4667749108826221175121671)
    ·
      refine ⟨7001623663239331762682507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667749108826221175121671 7001623663239331762682507)
      ·
        refine ⟨10502435494858997644023761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001623663239331762682507 10502435494858997644023761)
        ·
          refine ⟨7876826621144248233017821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10502435494858997644023761 7876826621144248233017821)
          ·
            refine ⟨2953809982929093087381683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7876826621144248233017821 2953809982929093087381683)
            ·
              refine ⟨4430714974393639631072525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953809982929093087381683 4430714974393639631072525)
              ·
                refine ⟨1661518115397614861652197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430714974393639631072525 1661518115397614861652197)
                ·
                  refine ⟨311534646637052786559787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661518115397614861652197 311534646637052786559787)
                  ·
                    rfl

theorem cell21_1365101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1365101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365101 prefixEnd_1365101 := by exact prefixLift 1365101
  have htrace : WordTrace (prefixWord ++ tailWord_1365101) baseStart_1365101 baseEnd_1365101 := by
    simpa [prefixWord, tailWord_1365101, baseEnd_1365101] using wordTrace_append hprefix tailTrace_1365101
  have hstable : (prefixWord ++ tailWord_1365101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365101).length < 2 ^ (prefixWord ++ tailWord_1365101).sum := by decide
  have hdescent : baseEnd_1365101 < baseStart_1365101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365256 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_1365256 : Nat := 118140960795 + 1365256 * 2 ^ 59
def prefixEnd_1365256 : Nat := 4983230072969 + 3 ^ 40 * 1365256 * 2
def baseEnd_1365256 : Nat := 311570019748806961476137

theorem tailTrace_1365256 : CollatzResearch.WordTrace tailWord_1365256 prefixEnd_1365256 311570019748806961476137 := by
  unfold tailWord_1365256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897488570959077003261811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33196651427945436004349081 24897488570959077003261811)
  ·
    refine ⟨37346232856438615504892717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24897488570959077003261811 37346232856438615504892717)
    ·
      refine ⟨14004837321164480814334769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37346232856438615504892717 14004837321164480814334769)
      ·
        refine ⟨10503627990873360610751077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14004837321164480814334769 10503627990873360610751077)
        ·
          refine ⟨1969430248288755114515827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10503627990873360610751077 1969430248288755114515827)
          ·
            refine ⟨2954145372433132671773741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969430248288755114515827 2954145372433132671773741)
            ·
              refine ⟨1107804514662424751915153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954145372433132671773741 1107804514662424751915153)
              ·
                refine ⟨830853385996818563936365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107804514662424751915153 830853385996818563936365)
                ·
                  refine ⟨311570019748806961476137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830853385996818563936365 311570019748806961476137)
                  ·
                    rfl

theorem cell21_1365256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_1365256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365256 prefixEnd_1365256 := by exact prefixLift 1365256
  have htrace : WordTrace (prefixWord ++ tailWord_1365256) baseStart_1365256 baseEnd_1365256 := by
    simpa [prefixWord, tailWord_1365256, baseEnd_1365256] using wordTrace_append hprefix tailTrace_1365256
  have hstable : (prefixWord ++ tailWord_1365256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365256).length < 2 ^ (prefixWord ++ tailWord_1365256).sum := by decide
  have hdescent : baseEnd_1365256 < baseStart_1365256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365312 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_1365312 : Nat := 118140960795 + 1365312 * 2 ^ 59
def prefixEnd_1365312 : Nat := 4983230072969 + 3 ^ 40 * 1365312 * 2
def baseEnd_1365312 : Nat := 311582799711763308542689

theorem tailTrace_1365312 : CollatzResearch.WordTrace tailWord_1365312 prefixEnd_1365312 311582799711763308542689 := by
  unfold tailWord_1365312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24898509814857637785281095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33198013086476850380374793 24898509814857637785281095)
  ·
    refine ⟨37347764722286456677921643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24898509814857637785281095 37347764722286456677921643)
    ·
      refine ⟨56021647083429685016882465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37347764722286456677921643 56021647083429685016882465)
      ·
        refine ⟨42016235312572263762661849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56021647083429685016882465 42016235312572263762661849)
        ·
          refine ⟨31512176484429197821996387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42016235312572263762661849 31512176484429197821996387)
          ·
            refine ⟨47268264726643796732994581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31512176484429197821996387 47268264726643796732994581)
            ·
              refine ⟨2215699909061427971859121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47268264726643796732994581 2215699909061427971859121)
              ·
                refine ⟨1661774931796070978894341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215699909061427971859121 1661774931796070978894341)
                ·
                  refine ⟨311582799711763308542689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661774931796070978894341 311582799711763308542689)
                  ·
                    rfl

theorem cell21_1365312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_1365312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365312 prefixEnd_1365312 := by exact prefixLift 1365312
  have htrace : WordTrace (prefixWord ++ tailWord_1365312) baseStart_1365312 baseEnd_1365312 := by
    simpa [prefixWord, tailWord_1365312, baseEnd_1365312] using wordTrace_append hprefix tailTrace_1365312
  have hstable : (prefixWord ++ tailWord_1365312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365312).length < 2 ^ (prefixWord ++ tailWord_1365312).sum := by decide
  have hdescent : baseEnd_1365312 < baseStart_1365312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365318 : List Nat := [6, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1365318 : Nat := 118140960795 + 1365318 * 2 ^ 59
def prefixEnd_1365318 : Nat := 4983230072969 + 3 ^ 40 * 1365318 * 2
def baseEnd_1365318 : Nat := 103861389664502877147559

theorem tailTrace_1365318 : CollatzResearch.WordTrace tailWord_1365318 prefixEnd_1365318 103861389664502877147559 := by
  unfold tailWord_1365318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556163702115423081102519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33198158978462359063520405 1556163702115423081102519)
  ·
    refine ⟨2334245553173134621653779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556163702115423081102519 2334245553173134621653779)
    ·
      refine ⟨3501368329759701932480669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2334245553173134621653779 3501368329759701932480669)
      ·
        refine ⟨1313013123659888224680251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3501368329759701932480669 1313013123659888224680251)
        ·
          refine ⟨1969519685489832337020377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313013123659888224680251 1969519685489832337020377)
          ·
            refine ⟨1477139764117374252765283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969519685489832337020377 1477139764117374252765283)
            ·
              refine ⟨2215709646176061379147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477139764117374252765283 2215709646176061379147925)
              ·
                refine ⟨103861389664502877147559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2215709646176061379147925 103861389664502877147559)
                ·
                  rfl

theorem cell21_1365318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1365318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365318 prefixEnd_1365318 := by exact prefixLift 1365318
  have htrace : WordTrace (prefixWord ++ tailWord_1365318) baseStart_1365318 baseEnd_1365318 := by
    simpa [prefixWord, tailWord_1365318, baseEnd_1365318] using wordTrace_append hprefix tailTrace_1365318
  have hstable : (prefixWord ++ tailWord_1365318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365318).length < 2 ^ (prefixWord ++ tailWord_1365318).sum := by decide
  have hdescent : baseEnd_1365318 < baseStart_1365318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365371 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_1365371 : Nat := 118140960795 + 1365371 * 2 ^ 59
def prefixEnd_1365371 : Nat := 4983230072969 + 3 ^ 40 * 1365371 * 2
def baseEnd_1365371 : Nat := 311596264315592317059235

theorem tailTrace_1365371 : CollatzResearch.WordTrace tailWord_1365371 prefixEnd_1365371 311596264315592317059235 := by
  unfold tailWord_1365371
  simp only [CollatzResearch.WordTrace]
  refine ⟨49799171536501528646959967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33199447691001019097973311 49799171536501528646959967)
  ·
    refine ⟨74698757304752292970439951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49799171536501528646959967 74698757304752292970439951)
    ·
      refine ⟨112048135957128439455659927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74698757304752292970439951 112048135957128439455659927)
      ·
        refine ⟨168072203935692659183489891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112048135957128439455659927 168072203935692659183489891)
        ·
          refine ⟨252108305903538988775234837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168072203935692659183489891 252108305903538988775234837)
          ·
            refine ⟨11817576839228390098839133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252108305903538988775234837 11817576839228390098839133)
            ·
              refine ⟨4431591314710646287064675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11817576839228390098839133 4431591314710646287064675)
              ·
                refine ⟨6647386972065969430597013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431591314710646287064675 6647386972065969430597013)
                ·
                  refine ⟨311596264315592317059235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6647386972065969430597013 311596264315592317059235)
                  ·
                    rfl

theorem cell21_1365371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_1365371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365371 prefixEnd_1365371 := by exact prefixLift 1365371
  have htrace : WordTrace (prefixWord ++ tailWord_1365371) baseStart_1365371 baseEnd_1365371 := by
    simpa [prefixWord, tailWord_1365371, baseEnd_1365371] using wordTrace_append hprefix tailTrace_1365371
  have hstable : (prefixWord ++ tailWord_1365371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365371).length < 2 ^ (prefixWord ++ tailWord_1365371).sum := by decide
  have hdescent : baseEnd_1365371 < baseStart_1365371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365394 : List Nat := [3, 2, 3, 3, 2, 1, 2, 5]
def baseStart_1365394 : Nat := 118140960795 + 1365394 * 2 ^ 59
def prefixEnd_1365394 : Nat := 4983230072969 + 3 ^ 40 * 1365394 * 2
def baseEnd_1365394 : Nat := 103867171076316462725285

theorem tailTrace_1365394 : CollatzResearch.WordTrace tailWord_1365394 prefixEnd_1365394 103867171076316462725285 := by
  unfold tailWord_1365394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12450002603854550893761809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33200006943612135716698157 12450002603854550893761809)
  ·
    refine ⟨9337501952890913170321357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12450002603854550893761809 9337501952890913170321357)
    ·
      refine ⟨3501563232334092438870509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9337501952890913170321357 3501563232334092438870509)
      ·
        refine ⟨1313086212125284664576441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3501563232334092438870509 1313086212125284664576441)
        ·
          refine ⟨984814659093963498432331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313086212125284664576441 984814659093963498432331)
          ·
            refine ⟨1477221988640945247648497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984814659093963498432331 1477221988640945247648497)
            ·
              refine ⟨1107916491480708935736373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477221988640945247648497 1107916491480708935736373)
              ·
                refine ⟨103867171076316462725285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107916491480708935736373 103867171076316462725285)
                ·
                  rfl

theorem cell21_1365394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_1365394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365394 prefixEnd_1365394 := by exact prefixLift 1365394
  have htrace : WordTrace (prefixWord ++ tailWord_1365394) baseStart_1365394 baseEnd_1365394 := by
    simpa [prefixWord, tailWord_1365394, baseEnd_1365394] using wordTrace_append hprefix tailTrace_1365394
  have hstable : (prefixWord ++ tailWord_1365394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365394).length < 2 ^ (prefixWord ++ tailWord_1365394).sum := by decide
  have hdescent : baseEnd_1365394 < baseStart_1365394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365402 : List Nat := [3, 1, 1, 4, 1, 1, 3, 7]
def baseStart_1365402 : Nat := 118140960795 + 1365402 * 2 ^ 59
def prefixEnd_1365402 : Nat := 4983230072969 + 3 ^ 40 * 1365402 * 2
def baseEnd_1365402 : Nat := 103867779645981050680835

theorem tailTrace_1365402 : CollatzResearch.WordTrace tailWord_1365402 prefixEnd_1365402 103867779645981050680835 := by
  unfold tailWord_1365402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12450075549847305235334615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33200201466259480627558973 12450075549847305235334615)
  ·
    refine ⟨18675113324770957853001923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12450075549847305235334615 18675113324770957853001923)
    ·
      refine ⟨28012669987156436779502885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18675113324770957853001923 28012669987156436779502885)
      ·
        refine ⟨5252375622591831896156791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28012669987156436779502885 5252375622591831896156791)
        ·
          refine ⟨7878563433887747844235187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252375622591831896156791 7878563433887747844235187)
          ·
            refine ⟨11817845150831621766352781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7878563433887747844235187 11817845150831621766352781)
            ·
              refine ⟨4431691931561858162382293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11817845150831621766352781 4431691931561858162382293)
              ·
                refine ⟨103867779645981050680835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4431691931561858162382293 103867779645981050680835)
                ·
                  rfl

theorem cell21_1365402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_1365402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365402 prefixEnd_1365402 := by exact prefixLift 1365402
  have htrace : WordTrace (prefixWord ++ tailWord_1365402) baseStart_1365402 baseEnd_1365402 := by
    simpa [prefixWord, tailWord_1365402, baseEnd_1365402] using wordTrace_append hprefix tailTrace_1365402
  have hstable : (prefixWord ++ tailWord_1365402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365402).length < 2 ^ (prefixWord ++ tailWord_1365402).sum := by decide
  have hdescent : baseEnd_1365402 < baseStart_1365402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365557 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1365557 : Nat := 118140960795 + 1365557 * 2 ^ 59
def prefixEnd_1365557 : Nat := 4983230072969 + 3 ^ 40 * 1365557 * 2
def baseEnd_1365557 : Nat := 311638712049697326958855

theorem tailTrace_1365557 : CollatzResearch.WordTrace tailWord_1365557 prefixEnd_1365557 311638712049697326958855 := by
  unfold tailWord_1365557
  simp only [CollatzResearch.WordTrace]
  refine ⟨49805955513827682413230925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33203970342551788275487283 49805955513827682413230925)
  ·
    refine ⟨18677233317685380904961597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49805955513827682413230925 18677233317685380904961597)
    ·
      refine ⟨7003962494132017839360599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18677233317685380904961597 7003962494132017839360599)
      ·
        refine ⟨10505943741198026759040899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003962494132017839360599 10505943741198026759040899)
        ·
          refine ⟨15758915611797040138561349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505943741198026759040899 15758915611797040138561349)
          ·
            refine ⟨2954796677211945025980253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15758915611797040138561349 2954796677211945025980253)
            ·
              refine ⟨1108048753954479384742595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954796677211945025980253 1108048753954479384742595)
              ·
                refine ⟨1662073130931719077113893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108048753954479384742595 1662073130931719077113893)
                ·
                  refine ⟨311638712049697326958855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662073130931719077113893 311638712049697326958855)
                  ·
                    rfl

theorem cell21_1365557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1365557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365557 prefixEnd_1365557 := by exact prefixLift 1365557
  have htrace : WordTrace (prefixWord ++ tailWord_1365557) baseStart_1365557 baseEnd_1365557 := by
    simpa [prefixWord, tailWord_1365557, baseEnd_1365557] using wordTrace_append hprefix tailTrace_1365557
  have hstable : (prefixWord ++ tailWord_1365557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365557).length < 2 ^ (prefixWord ++ tailWord_1365557).sum := by decide
  have hdescent : baseEnd_1365557 < baseStart_1365557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365616 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_1365616 : Nat := 118140960795 + 1365616 * 2 ^ 59
def prefixEnd_1365616 : Nat := 4983230072969 + 3 ^ 40 * 1365616 * 2
def baseEnd_1365616 : Nat := 311652176653526335475401

theorem tailTrace_1365616 : CollatzResearch.WordTrace tailWord_1365616 prefixEnd_1365616 311652176653526335475401 := by
  unfold tailWord_1365616
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904053710306967744814351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33205404947075956993085801 24904053710306967744814351)
  ·
    refine ⟨37356080565460451617221527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24904053710306967744814351 37356080565460451617221527)
    ·
      refine ⟨56034120848190677425832291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37356080565460451617221527 56034120848190677425832291)
      ·
        refine ⟨84051181272286016138748437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56034120848190677425832291 84051181272286016138748437)
        ·
          refine ⟨3939899122138407006503833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84051181272286016138748437 3939899122138407006503833)
          ·
            refine ⟨2954924341603805254877875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939899122138407006503833 2954924341603805254877875)
            ·
              refine ⟨4432386512405707882316813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954924341603805254877875 4432386512405707882316813)
              ·
                refine ⟨1662144942152140455868805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4432386512405707882316813 1662144942152140455868805)
                ·
                  refine ⟨311652176653526335475401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662144942152140455868805 311652176653526335475401)
                  ·
                    rfl

theorem cell21_1365616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_1365616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365616 prefixEnd_1365616 := by exact prefixLift 1365616
  have htrace : WordTrace (prefixWord ++ tailWord_1365616) baseStart_1365616 baseEnd_1365616 := by
    simpa [prefixWord, tailWord_1365616, baseEnd_1365616] using wordTrace_append hprefix tailTrace_1365616
  have hstable : (prefixWord ++ tailWord_1365616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365616).length < 2 ^ (prefixWord ++ tailWord_1365616).sum := by decide
  have hdescent : baseEnd_1365616 < baseStart_1365616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365689 : List Nat := [1, 2, 1, 4, 1, 1, 2, 9]
def baseStart_1365689 : Nat := 118140960795 + 1365689 * 2 ^ 59
def prefixEnd_1365689 : Nat := 4983230072969 + 3 ^ 40 * 1365689 * 2
def baseEnd_1365689 : Nat := 103889612082698143586195

theorem tailTrace_1365689 : CollatzResearch.WordTrace tailWord_1365689 prefixEnd_1365689 103889612082698143586195 := by
  unfold tailWord_1365689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49810769949349468957036121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33207179966232979304690747 49810769949349468957036121)
  ·
    refine ⟨37358077462012101717777091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49810769949349468957036121 37358077462012101717777091)
    ·
      refine ⟨56037116193018152576665637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37358077462012101717777091 56037116193018152576665637)
      ·
        refine ⟨10506959286190903608124807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56037116193018152576665637 10506959286190903608124807)
        ·
          refine ⟨15760438929286355412187211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506959286190903608124807 15760438929286355412187211)
          ·
            refine ⟨23640658393929533118280817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15760438929286355412187211 23640658393929533118280817)
            ·
              refine ⟨17730493795447149838710613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23640658393929533118280817 17730493795447149838710613)
              ·
                refine ⟨103889612082698143586195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17730493795447149838710613 103889612082698143586195)
                ·
                  rfl

theorem cell21_1365689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_1365689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365689 prefixEnd_1365689 := by exact prefixLift 1365689
  have htrace : WordTrace (prefixWord ++ tailWord_1365689) baseStart_1365689 baseEnd_1365689 := by
    simpa [prefixWord, tailWord_1365689, baseEnd_1365689] using wordTrace_append hprefix tailTrace_1365689
  have hstable : (prefixWord ++ tailWord_1365689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365689).length < 2 ^ (prefixWord ++ tailWord_1365689).sum := by decide
  have hdescent : baseEnd_1365689 < baseStart_1365689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365706 : List Nat := [3, 1, 2, 1, 5, 1, 8]
def baseStart_1365706 : Nat := 118140960795 + 1365706 * 2 ^ 59
def prefixEnd_1365706 : Nat := 4983230072969 + 3 ^ 40 * 1365706 * 2
def baseEnd_1365706 : Nat := 34630301764411797663913

theorem tailTrace_1365706 : CollatzResearch.WordTrace tailWord_1365706 prefixEnd_1365706 34630301764411797663913 := by
  unfold tailWord_1365706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452847497571970215101243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33207593326858587240269981 12452847497571970215101243)
  ·
    refine ⟨18679271246357955322651865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452847497571970215101243 18679271246357955322651865)
    ·
      refine ⟨14009453434768466491988899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18679271246357955322651865 14009453434768466491988899)
      ·
        refine ⟨21014180152152699737983349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009453434768466491988899 21014180152152699737983349)
        ·
          refine ⟨1970079389264315600435939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21014180152152699737983349 1970079389264315600435939)
          ·
            refine ⟨2955119083896473400653909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970079389264315600435939 2955119083896473400653909)
            ·
              refine ⟨34630301764411797663913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2955119083896473400653909 34630301764411797663913)
              ·
                rfl

theorem cell21_1365706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 8].length) (baseStart_1365706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365706 prefixEnd_1365706 := by exact prefixLift 1365706
  have htrace : WordTrace (prefixWord ++ tailWord_1365706) baseStart_1365706 baseEnd_1365706 := by
    simpa [prefixWord, tailWord_1365706, baseEnd_1365706] using wordTrace_append hprefix tailTrace_1365706
  have hstable : (prefixWord ++ tailWord_1365706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365706).length < 2 ^ (prefixWord ++ tailWord_1365706).sum := by decide
  have hdescent : baseEnd_1365706 < baseStart_1365706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365709 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1365709 : Nat := 118140960795 + 1365709 * 2 ^ 59
def prefixEnd_1365709 : Nat := 4983230072969 + 3 ^ 40 * 1365709 * 2
def baseEnd_1365709 : Nat := 311673400520578840425211

theorem tailTrace_1365709 : CollatzResearch.WordTrace tailWord_1365709 prefixEnd_1365709 311673400520578840425211 := by
  unfold tailWord_1365709
  simp only [CollatzResearch.WordTrace]
  refine ⟨49811499409277012372764181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33207666272851341581842787 49811499409277012372764181)
  ·
    refine ⟨2334914034809859954973321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49811499409277012372764181 2334914034809859954973321)
    ·
      refine ⟨1751185526107394966229991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334914034809859954973321 1751185526107394966229991)
      ·
        refine ⟨2626778289161092449344987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751185526107394966229991 2626778289161092449344987)
        ·
          refine ⟨3940167433741638674017481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626778289161092449344987 3940167433741638674017481)
          ·
            refine ⟨2955125575306229005513111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3940167433741638674017481 2955125575306229005513111)
            ·
              refine ⟨4432688362959343508269667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955125575306229005513111 4432688362959343508269667)
              ·
                refine ⟨6649032544439015262404501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432688362959343508269667 6649032544439015262404501)
                ·
                  refine ⟨311673400520578840425211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6649032544439015262404501 311673400520578840425211)
                  ·
                    rfl

theorem cell21_1365709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1365709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365709 prefixEnd_1365709 := by exact prefixLift 1365709
  have htrace : WordTrace (prefixWord ++ tailWord_1365709) baseStart_1365709 baseEnd_1365709 := by
    simpa [prefixWord, tailWord_1365709, baseEnd_1365709] using wordTrace_append hprefix tailTrace_1365709
  have hstable : (prefixWord ++ tailWord_1365709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365709).length < 2 ^ (prefixWord ++ tailWord_1365709).sum := by decide
  have hdescent : baseEnd_1365709 < baseStart_1365709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365827 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_1365827 : Nat := 118140960795 + 1365827 * 2 ^ 59
def prefixEnd_1365827 : Nat := 4983230072969 + 3 ^ 40 * 1365827 * 2
def baseEnd_1365827 : Nat := 311700329728236857458303

theorem tailTrace_1365827 : CollatzResearch.WordTrace tailWord_1365827 prefixEnd_1365827 311700329728236857458303 := by
  unfold tailWord_1365827
  simp only [CollatzResearch.WordTrace]
  refine ⟨49815803222849518525559735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33210535481899679017039823 49815803222849518525559735)
  ·
    refine ⟨74723704834274277788339603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49815803222849518525559735 74723704834274277788339603)
    ·
      refine ⟨112085557251411416682509405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74723704834274277788339603 112085557251411416682509405)
      ·
        refine ⟨42032083969279281255941027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112085557251411416682509405 42032083969279281255941027)
        ·
          refine ⟨63048125953918921883911541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42032083969279281255941027 63048125953918921883911541)
          ·
            refine ⟨5910761808179898926616707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63048125953918921883911541 5910761808179898926616707)
            ·
              refine ⟨8866142712269848389925061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910761808179898926616707 8866142712269848389925061)
              ·
                refine ⟨1662401758550596573110949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8866142712269848389925061 1662401758550596573110949)
                ·
                  refine ⟨311700329728236857458303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662401758550596573110949 311700329728236857458303)
                  ·
                    rfl

theorem cell21_1365827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_1365827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365827 prefixEnd_1365827 := by exact prefixLift 1365827
  have htrace : WordTrace (prefixWord ++ tailWord_1365827) baseStart_1365827 baseEnd_1365827 := by
    simpa [prefixWord, tailWord_1365827, baseEnd_1365827] using wordTrace_append hprefix tailTrace_1365827
  have hstable : (prefixWord ++ tailWord_1365827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365827).length < 2 ^ (prefixWord ++ tailWord_1365827).sum := by decide
  have hdescent : baseEnd_1365827 < baseStart_1365827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365844 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1365844 : Nat := 118140960795 + 1365844 * 2 ^ 59
def prefixEnd_1365844 : Nat := 4983230072969 + 3 ^ 40 * 1365844 * 2
def baseEnd_1365844 : Nat := 311704209359848605674935

theorem tailTrace_1365844 : CollatzResearch.WordTrace tailWord_1365844 prefixEnd_1365844 311704209359848605674935 := by
  unfold tailWord_1365844
  simp only [CollatzResearch.WordTrace]
  refine ⟨24908211631893965214464293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33210948842525286952619057 24908211631893965214464293)
  ·
    refine ⟨4670289680980118477712055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24908211631893965214464293 4670289680980118477712055)
    ·
      refine ⟨7005434521470177716568083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670289680980118477712055 7005434521470177716568083)
      ·
        refine ⟨10508151782205266574852125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005434521470177716568083 10508151782205266574852125)
        ·
          refine ⟨3940556918326974965569547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10508151782205266574852125 3940556918326974965569547)
          ·
            refine ⟨5910835377490462448354321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940556918326974965569547 5910835377490462448354321)
            ·
              refine ⟨4433126533117846836265741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910835377490462448354321 4433126533117846836265741)
              ·
                refine ⟨1662422449919192563599653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433126533117846836265741 1662422449919192563599653)
                ·
                  refine ⟨311704209359848605674935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662422449919192563599653 311704209359848605674935)
                  ·
                    rfl

theorem cell21_1365844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1365844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365844 prefixEnd_1365844 := by exact prefixLift 1365844
  have htrace : WordTrace (prefixWord ++ tailWord_1365844) baseStart_1365844 baseEnd_1365844 := by
    simpa [prefixWord, tailWord_1365844, baseEnd_1365844] using wordTrace_append hprefix tailTrace_1365844
  have hstable : (prefixWord ++ tailWord_1365844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365844).length < 2 ^ (prefixWord ++ tailWord_1365844).sum := by decide
  have hdescent : baseEnd_1365844 < baseStart_1365844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365878 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1365878 : Nat := 118140960795 + 1365878 * 2 ^ 59
def prefixEnd_1365878 : Nat := 4983230072969 + 3 ^ 40 * 1365878 * 2
def baseEnd_1365878 : Nat := 311711968623072102108199

theorem tailTrace_1365878 : CollatzResearch.WordTrace tailWord_1365878 prefixEnd_1365878 311711968623072102108199 := by
  unfold tailWord_1365878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113603959104047139729143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33211775563776502823777525 3113603959104047139729143)
  ·
    refine ⟨4670405938656070709593715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113603959104047139729143 4670405938656070709593715)
    ·
      refine ⟨7005608907984106064390573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670405938656070709593715 7005608907984106064390573)
      ·
        refine ⟨2627103340494039774146465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7005608907984106064390573 2627103340494039774146465)
        ·
          refine ⟨1970327505370529830609849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627103340494039774146465 1970327505370529830609849)
          ·
            refine ⟨1477745629027897372957387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970327505370529830609849 1477745629027897372957387)
            ·
              refine ⟨2216618443541846059436081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477745629027897372957387 2216618443541846059436081)
              ·
                refine ⟨1662463832656384544577061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216618443541846059436081 1662463832656384544577061)
                ·
                  refine ⟨311711968623072102108199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662463832656384544577061 311711968623072102108199)
                  ·
                    rfl

theorem cell21_1365878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1365878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365878 prefixEnd_1365878 := by exact prefixLift 1365878
  have htrace : WordTrace (prefixWord ++ tailWord_1365878) baseStart_1365878 baseEnd_1365878 := by
    simpa [prefixWord, tailWord_1365878, baseEnd_1365878] using wordTrace_append hprefix tailTrace_1365878
  have hstable : (prefixWord ++ tailWord_1365878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365878).length < 2 ^ (prefixWord ++ tailWord_1365878).sum := by decide
  have hdescent : baseEnd_1365878 < baseStart_1365878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365940 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1365940 : Nat := 118140960795 + 1365940 * 2 ^ 59
def prefixEnd_1365940 : Nat := 4983230072969 + 3 ^ 40 * 1365940 * 2
def baseEnd_1365940 : Nat := 311726117867773772074739

theorem tailTrace_1365940 : CollatzResearch.WordTrace tailWord_1365940 prefixEnd_1365940 311726117867773772074739 := by
  unfold tailWord_1365940
  simp only [CollatzResearch.WordTrace]
  refine ⟨24909962335720069412211637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33213283114293425882948849 24909962335720069412211637)
  ·
    refine ⟨2335308968973756507394841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24909962335720069412211637 2335308968973756507394841)
    ·
      refine ⟨1751481726730317380546131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335308968973756507394841 1751481726730317380546131)
      ·
        refine ⟨2627222590095476070819197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751481726730317380546131 2627222590095476070819197)
        ·
          refine ⟨985208471285803526557199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2627222590095476070819197 985208471285803526557199)
          ·
            refine ⟨1477812706928705289835799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985208471285803526557199 1477812706928705289835799)
            ·
              refine ⟨2216719060393057934753699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477812706928705289835799 2216719060393057934753699)
              ·
                refine ⟨3325078590589586902130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216719060393057934753699 3325078590589586902130549)
                ·
                  refine ⟨311726117867773772074739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325078590589586902130549 311726117867773772074739)
                  ·
                    rfl

theorem cell21_1365940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1365940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1365940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1365940 prefixEnd_1365940 := by exact prefixLift 1365940
  have htrace : WordTrace (prefixWord ++ tailWord_1365940) baseStart_1365940 baseEnd_1365940 := by
    simpa [prefixWord, tailWord_1365940, baseEnd_1365940] using wordTrace_append hprefix tailTrace_1365940
  have hstable : (prefixWord ++ tailWord_1365940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365940).length < 2 ^ (prefixWord ++ tailWord_1365940).sum := by decide
  have hdescent : baseEnd_1365940 < baseStart_1365940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366007 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_1366007 : Nat := 118140960795 + 1366007 * 2 ^ 59
def prefixEnd_1366007 : Nat := 4983230072969 + 3 ^ 40 * 1366007 * 2
def baseEnd_1366007 : Nat := 311741408180596544457935

theorem tailTrace_1366007 : CollatzResearch.WordTrace tailWord_1366007 prefixEnd_1366007 311741408180596544457935 := by
  unfold tailWord_1366007
  simp only [CollatzResearch.WordTrace]
  refine ⟨49822368362197409267112275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33214912241464939511408183 49822368362197409267112275)
  ·
    refine ⟨74733552543296113900668413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49822368362197409267112275 74733552543296113900668413)
    ·
      refine ⟨28025082203736042712750655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74733552543296113900668413 28025082203736042712750655)
      ·
        refine ⟨42037623305604064069125983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28025082203736042712750655 42037623305604064069125983)
        ·
          refine ⟨63056434958406096103688975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42037623305604064069125983 63056434958406096103688975)
          ·
            refine ⟨94584652437609144155533463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63056434958406096103688975 94584652437609144155533463)
            ·
              refine ⟨141876978656413716233300195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94584652437609144155533463 141876978656413716233300195)
              ·
                refine ⟨212815467984620574349950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141876978656413716233300195 212815467984620574349950293)
                ·
                  refine ⟨311741408180596544457935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 212815467984620574349950293 311741408180596544457935)
                  ·
                    rfl

theorem cell21_1366007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_1366007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366007 prefixEnd_1366007 := by exact prefixLift 1366007
  have htrace : WordTrace (prefixWord ++ tailWord_1366007) baseStart_1366007 baseEnd_1366007 := by
    simpa [prefixWord, tailWord_1366007, baseEnd_1366007] using wordTrace_append hprefix tailTrace_1366007
  have hstable : (prefixWord ++ tailWord_1366007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366007).length < 2 ^ (prefixWord ++ tailWord_1366007).sum := by decide
  have hdescent : baseEnd_1366007 < baseStart_1366007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366024 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_1366024 : Nat := 118140960795 + 1366024 * 2 ^ 59
def prefixEnd_1366024 : Nat := 4983230072969 + 3 ^ 40 * 1366024 * 2
def baseEnd_1366024 : Nat := 311745287812208292674567

theorem tailTrace_1366024 : CollatzResearch.WordTrace tailWord_1366024 prefixEnd_1366024 311745287812208292674567 := by
  unfold tailWord_1366024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24911494201567910585240563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33215325602090547446987417 24911494201567910585240563)
  ·
    refine ⟨37367241302351865877860845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24911494201567910585240563 37367241302351865877860845)
    ·
      refine ⟨14012715488381949704197817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37367241302351865877860845 14012715488381949704197817)
      ·
        refine ⟨10509536616286462278148363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14012715488381949704197817 10509536616286462278148363)
        ·
          refine ⟨15764304924429693417222545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509536616286462278148363 15764304924429693417222545)
          ·
            refine ⟨11823228693322270062916909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15764304924429693417222545 11823228693322270062916909)
            ·
              refine ⟨4433710759995851273593841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11823228693322270062916909 4433710759995851273593841)
              ·
                refine ⟨3325283069996888455195381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433710759995851273593841 3325283069996888455195381)
                ·
                  refine ⟨311745287812208292674567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325283069996888455195381 311745287812208292674567)
                  ·
                    rfl

theorem cell21_1366024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_1366024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366024 prefixEnd_1366024 := by exact prefixLift 1366024
  have htrace : WordTrace (prefixWord ++ tailWord_1366024) baseStart_1366024 baseEnd_1366024 := by
    simpa [prefixWord, tailWord_1366024, baseEnd_1366024] using wordTrace_append hprefix tailTrace_1366024
  have hstable : (prefixWord ++ tailWord_1366024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366024).length < 2 ^ (prefixWord ++ tailWord_1366024).sum := by decide
  have hdescent : baseEnd_1366024 < baseStart_1366024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366058 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_1366058 : Nat := 118140960795 + 1366058 * 2 ^ 59
def prefixEnd_1366058 : Nat := 4983230072969 + 3 ^ 40 * 1366058 * 2
def baseEnd_1366058 : Nat := 311753047075431789107831

theorem tailTrace_1366058 : CollatzResearch.WordTrace tailWord_1366058 prefixEnd_1366058 311753047075431789107831 := by
  unfold tailWord_1366058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456057121253161244304707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33216152323341763318145885 12456057121253161244304707)
  ·
    refine ⟨18684085681879741866457061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12456057121253161244304707 18684085681879741866457061)
    ·
      refine ⟨3503266065352451599960699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18684085681879741866457061 3503266065352451599960699)
      ·
        refine ⟨5254899098028677399941049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503266065352451599960699 5254899098028677399941049)
        ·
          refine ⟨3941174323521508049955787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5254899098028677399941049 3941174323521508049955787)
          ·
            refine ⟨5911761485282262074933681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941174323521508049955787 5911761485282262074933681)
            ·
              refine ⟨4433821113961696556200261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911761485282262074933681 4433821113961696556200261)
              ·
                refine ⟨831341458867818104287549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4433821113961696556200261 831341458867818104287549)
                ·
                  refine ⟨311753047075431789107831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831341458867818104287549 311753047075431789107831)
                  ·
                    rfl

theorem cell21_1366058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_1366058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366058 prefixEnd_1366058 := by exact prefixLift 1366058
  have htrace : WordTrace (prefixWord ++ tailWord_1366058) baseStart_1366058 baseEnd_1366058 := by
    simpa [prefixWord, tailWord_1366058, baseEnd_1366058] using wordTrace_append hprefix tailTrace_1366058
  have hstable : (prefixWord ++ tailWord_1366058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366058).length < 2 ^ (prefixWord ++ tailWord_1366058).sum := by decide
  have hdescent : baseEnd_1366058 < baseStart_1366058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366083 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_1366083 : Nat := 118140960795 + 1366083 * 2 ^ 59
def prefixEnd_1366083 : Nat := 4983230072969 + 3 ^ 40 * 1366083 * 2
def baseEnd_1366083 : Nat := 311758752416037301191113

theorem tailTrace_1366083 : CollatzResearch.WordTrace tailWord_1366083 prefixEnd_1366083 311758752416037301191113 := by
  unfold tailWord_1366083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49825140309922074246878903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33216760206614716164585935 49825140309922074246878903)
  ·
    refine ⟨74737710464883111370318355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49825140309922074246878903 74737710464883111370318355)
    ·
      refine ⟨112106565697324667055477533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74737710464883111370318355 112106565697324667055477533)
      ·
        refine ⟨42039962136496750145804075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112106565697324667055477533 42039962136496750145804075)
        ·
          refine ⟨63059943204745125218706113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42039962136496750145804075 63059943204745125218706113)
          ·
            refine ⟨47294957403558843914029585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63059943204745125218706113 47294957403558843914029585)
            ·
              refine ⟨35471218052669132935522189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47294957403558843914029585 35471218052669132935522189)
              ·
                refine ⟨13301706769750924850820821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35471218052669132935522189 13301706769750924850820821)
                ·
                  refine ⟨311758752416037301191113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13301706769750924850820821 311758752416037301191113)
                  ·
                    rfl

theorem cell21_1366083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_1366083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366083 prefixEnd_1366083 := by exact prefixLift 1366083
  have htrace : WordTrace (prefixWord ++ tailWord_1366083) baseStart_1366083 baseEnd_1366083 := by
    simpa [prefixWord, tailWord_1366083, baseEnd_1366083] using wordTrace_append hprefix tailTrace_1366083
  have hstable : (prefixWord ++ tailWord_1366083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366083).length < 2 ^ (prefixWord ++ tailWord_1366083).sum := by decide
  have hdescent : baseEnd_1366083 < baseStart_1366083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366117 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_1366117 : Nat := 118140960795 + 1366117 * 2 ^ 59
def prefixEnd_1366117 : Nat := 4983230072969 + 3 ^ 40 * 1366117 * 2
def baseEnd_1366117 : Nat := 311766511679260797624377

theorem tailTrace_1366117 : CollatzResearch.WordTrace tailWord_1366117 prefixEnd_1366117 311766511679260797624377 := by
  unfold tailWord_1366117
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826380391798898053616605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33217586927865932035744403 49826380391798898053616605)
  ·
    refine ⟨18684892646924586770106227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49826380391798898053616605 18684892646924586770106227)
    ·
      refine ⟨28027338970386880155159341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18684892646924586770106227 28027338970386880155159341)
      ·
        refine ⟨10510252113895080058184753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28027338970386880155159341 10510252113895080058184753)
        ·
          refine ⟨7882689085421310043638565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10510252113895080058184753 7882689085421310043638565)
          ·
            refine ⟨1478004203516495633182231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7882689085421310043638565 1478004203516495633182231)
            ·
              refine ⟨2217006305274743449773347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478004203516495633182231 2217006305274743449773347)
              ·
                refine ⟨3325509457912115174660021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217006305274743449773347 3325509457912115174660021)
                ·
                  refine ⟨311766511679260797624377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325509457912115174660021 311766511679260797624377)
                  ·
                    rfl

theorem cell21_1366117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_1366117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366117 prefixEnd_1366117 := by exact prefixLift 1366117
  have htrace : WordTrace (prefixWord ++ tailWord_1366117) baseStart_1366117 baseEnd_1366117 := by
    simpa [prefixWord, tailWord_1366117, baseEnd_1366117] using wordTrace_append hprefix tailTrace_1366117
  have hstable : (prefixWord ++ tailWord_1366117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366117).length < 2 ^ (prefixWord ++ tailWord_1366117).sum := by decide
  have hdescent : baseEnd_1366117 < baseStart_1366117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366168 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_1366168 : Nat := 118140960795 + 1366168 * 2 ^ 59
def prefixEnd_1366168 : Nat := 4983230072969 + 3 ^ 40 * 1366168 * 2
def baseEnd_1366168 : Nat := 311778150574096042274273

theorem tailTrace_1366168 : CollatzResearch.WordTrace tailWord_1366168 prefixEnd_1366168 311778150574096042274273 := by
  unfold tailWord_1366168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24914120257307066881861579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33218827009742755842482105 24914120257307066881861579)
  ·
    refine ⟨37371180385960600322792369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24914120257307066881861579 37371180385960600322792369)
    ·
      refine ⟨28028385289470450242094277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37371180385960600322792369 28028385289470450242094277)
      ·
        refine ⟨5255322241775709420392677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28028385289470450242094277 5255322241775709420392677)
        ·
          refine ⟨985372920332945516323627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5255322241775709420392677 985372920332945516323627)
          ·
            refine ⟨1478059380499418274485441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985372920332945516323627 1478059380499418274485441)
            ·
              refine ⟨1108544535374563705864081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478059380499418274485441 1108544535374563705864081)
              ·
                refine ⟨831408401530922779398061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108544535374563705864081 831408401530922779398061)
                ·
                  refine ⟨311778150574096042274273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831408401530922779398061 311778150574096042274273)
                  ·
                    rfl

theorem cell21_1366168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_1366168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366168 prefixEnd_1366168 := by exact prefixLift 1366168
  have htrace : WordTrace (prefixWord ++ tailWord_1366168) baseStart_1366168 baseEnd_1366168 := by
    simpa [prefixWord, tailWord_1366168, baseEnd_1366168] using wordTrace_append hprefix tailTrace_1366168
  have hstable : (prefixWord ++ tailWord_1366168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366168).length < 2 ^ (prefixWord ++ tailWord_1366168).sum := by decide
  have hdescent : baseEnd_1366168 < baseStart_1366168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366193 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_1366193 : Nat := 118140960795 + 1366193 * 2 ^ 59
def prefixEnd_1366193 : Nat := 4983230072969 + 3 ^ 40 * 1366193 * 2
def baseEnd_1366193 : Nat := 311783855914701554357555

theorem tailTrace_1366193 : CollatzResearch.WordTrace tailWord_1366193 prefixEnd_1366193 311783855914701554357555 := by
  unfold tailWord_1366193
  simp only [CollatzResearch.WordTrace]
  refine ⟨49829152339523563033383233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33219434893015708688922155 49829152339523563033383233)
  ·
    refine ⟨37371864254642672275037425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49829152339523563033383233 37371864254642672275037425)
    ·
      refine ⟨28028898190982004206278069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37371864254642672275037425 28028898190982004206278069)
      ·
        refine ⟨2627709205404562894338569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28028898190982004206278069 2627709205404562894338569)
        ·
          refine ⟨1970781904053422170753927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627709205404562894338569 1970781904053422170753927)
          ·
            refine ⟨2956172856080133256130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970781904053422170753927 2956172856080133256130891)
            ·
              refine ⟨4434259284120199884196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956172856080133256130891 4434259284120199884196337)
              ·
                refine ⟨3325694463090149913147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434259284120199884196337 3325694463090149913147253)
                ·
                  refine ⟨311783855914701554357555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325694463090149913147253 311783855914701554357555)
                  ·
                    rfl

theorem cell21_1366193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_1366193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366193 prefixEnd_1366193 := by exact prefixLift 1366193
  have htrace : WordTrace (prefixWord ++ tailWord_1366193) baseStart_1366193 baseEnd_1366193 := by
    simpa [prefixWord, tailWord_1366193, baseEnd_1366193] using wordTrace_append hprefix tailTrace_1366193
  have hstable : (prefixWord ++ tailWord_1366193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366193).length < 2 ^ (prefixWord ++ tailWord_1366193).sum := by decide
  have hdescent : baseEnd_1366193 < baseStart_1366193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_1366235 : Nat := 118140960795 + 1366235 * 2 ^ 59
def prefixEnd_1366235 : Nat := 4983230072969 + 3 ^ 40 * 1366235 * 2
def baseEnd_1366235 : Nat := 311793440886918814657469

theorem tailTrace_1366235 : CollatzResearch.WordTrace tailWord_1366235 prefixEnd_1366235 311793440886918814657469 := by
  unfold tailWord_1366235
  simp only [CollatzResearch.WordTrace]
  refine ⟨49830684205371404206412159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33220456136914269470941439 49830684205371404206412159)
  ·
    refine ⟨74746026308057106309618239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49830684205371404206412159 74746026308057106309618239)
    ·
      refine ⟨112119039462085659464427359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74746026308057106309618239 112119039462085659464427359)
      ·
        refine ⟨168178559193128489196641039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112119039462085659464427359 168178559193128489196641039)
        ·
          refine ⟨252267838789692733794961559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168178559193128489196641039 252267838789692733794961559)
          ·
            refine ⟨378401758184539100692442339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252267838789692733794961559 378401758184539100692442339)
            ·
              refine ⟨567602637276808651038663509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378401758184539100692442339 567602637276808651038663509)
              ·
                refine ⟨3325796702793800689679669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 567602637276808651038663509 3325796702793800689679669)
                ·
                  refine ⟨311793440886918814657469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325796702793800689679669 311793440886918814657469)
                  ·
                    rfl

theorem cell21_1366235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_1366235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366235 prefixEnd_1366235 := by exact prefixLift 1366235
  have htrace : WordTrace (prefixWord ++ tailWord_1366235) baseStart_1366235 baseEnd_1366235 := by
    simpa [prefixWord, tailWord_1366235, baseEnd_1366235] using wordTrace_append hprefix tailTrace_1366235
  have hstable : (prefixWord ++ tailWord_1366235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366235).length < 2 ^ (prefixWord ++ tailWord_1366235).sum := by decide
  have hdescent : baseEnd_1366235 < baseStart_1366235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366266 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1366266 : Nat := 118140960795 + 1366266 * 2 ^ 59
def prefixEnd_1366266 : Nat := 4983230072969 + 3 ^ 40 * 1366266 * 2
def baseEnd_1366266 : Nat := 311800515509269649640739

theorem tailTrace_1366266 : CollatzResearch.WordTrace tailWord_1366266 prefixEnd_1366266 311800515509269649640739 := by
  unfold tailWord_1366266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457953717064774125197663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33221209912172731000527101 12457953717064774125197663)
  ·
    refine ⟨18686930575597161187796495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12457953717064774125197663 18686930575597161187796495)
    ·
      refine ⟨28030395863395741781694743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686930575597161187796495 28030395863395741781694743)
      ·
        refine ⟨42045593795093612672542115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28030395863395741781694743 42045593795093612672542115)
        ·
          refine ⟨63068390692640419008813173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42045593795093612672542115 63068390692640419008813173)
          ·
            refine ⟨5912661627435039282076235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63068390692640419008813173 5912661627435039282076235)
            ·
              refine ⟨8868992441152558923114353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912661627435039282076235 8868992441152558923114353)
              ·
                refine ⟨6651744330864419192335765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8868992441152558923114353 6651744330864419192335765)
                ·
                  refine ⟨311800515509269649640739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6651744330864419192335765 311800515509269649640739)
                  ·
                    rfl

theorem cell21_1366266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1366266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366266 prefixEnd_1366266 := by exact prefixLift 1366266
  have htrace : WordTrace (prefixWord ++ tailWord_1366266) baseStart_1366266 baseEnd_1366266 := by
    simpa [prefixWord, tailWord_1366266, baseEnd_1366266] using wordTrace_append hprefix tailTrace_1366266
  have hstable : (prefixWord ++ tailWord_1366266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366266).length < 2 ^ (prefixWord ++ tailWord_1366266).sum := by decide
  have hdescent : baseEnd_1366266 < baseStart_1366266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366286 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_1366286 : Nat := 118140960795 + 1366286 * 2 ^ 59
def prefixEnd_1366286 : Nat := 4983230072969 + 3 ^ 40 * 1366286 * 2
def baseEnd_1366286 : Nat := 311805079781754059307365

theorem tailTrace_1366286 : CollatzResearch.WordTrace tailWord_1366286 prefixEnd_1366286 311805079781754059307365 := by
  unfold tailWord_1366286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229068041023329989564839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33221696218791093277679141 6229068041023329989564839)
  ·
    refine ⟨9343602061534994984347259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229068041023329989564839 9343602061534994984347259)
    ·
      refine ⟨14015403092302492476520889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343602061534994984347259 14015403092302492476520889)
      ·
        refine ⟨10511552319226869357390667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14015403092302492476520889 10511552319226869357390667)
        ·
          refine ⟨15767328478840304036086001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10511552319226869357390667 15767328478840304036086001)
          ·
            refine ⟨11825496359130228027064501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15767328478840304036086001 11825496359130228027064501)
            ·
              refine ⟨1108640283668458877537297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11825496359130228027064501 1108640283668458877537297)
              ·
                refine ⟨831480212751344158152973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108640283668458877537297 831480212751344158152973)
                ·
                  refine ⟨311805079781754059307365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831480212751344158152973 311805079781754059307365)
                  ·
                    rfl

theorem cell21_1366286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_1366286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366286 prefixEnd_1366286 := by exact prefixLift 1366286
  have htrace : WordTrace (prefixWord ++ tailWord_1366286) baseStart_1366286 baseEnd_1366286 := by
    simpa [prefixWord, tailWord_1366286, baseEnd_1366286] using wordTrace_append hprefix tailTrace_1366286
  have hstable : (prefixWord ++ tailWord_1366286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366286).length < 2 ^ (prefixWord ++ tailWord_1366286).sum := by decide
  have hdescent : baseEnd_1366286 < baseStart_1366286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366404 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1366404 : Nat := 118140960795 + 1366404 * 2 ^ 59
def prefixEnd_1366404 : Nat := 4983230072969 + 3 ^ 40 * 1366404 * 2
def baseEnd_1366404 : Nat := 311832008989412076340457

theorem tailTrace_1366404 : CollatzResearch.WordTrace tailWord_1366404 prefixEnd_1366404 311832008989412076340457 := by
  unfold tailWord_1366404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918424070879573034657133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33224565427839430712876177 24918424070879573034657133)
  ·
    refine ⟨9344409026579839887996425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24918424070879573034657133 9344409026579839887996425)
    ·
      refine ⟨7008306769934879915997319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9344409026579839887996425 7008306769934879915997319)
      ·
        refine ⟨10512460154902319873995979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7008306769934879915997319 10512460154902319873995979)
        ·
          refine ⟨15768690232353479810993969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10512460154902319873995979 15768690232353479810993969)
          ·
            refine ⟨11826517674265109858245477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15768690232353479810993969 11826517674265109858245477)
            ·
              refine ⟨2217472063924708098421027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11826517674265109858245477 2217472063924708098421027)
              ·
                refine ⟨3326208095887062147631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217472063924708098421027 3326208095887062147631541)
                ·
                  refine ⟨311832008989412076340457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326208095887062147631541 311832008989412076340457)
                  ·
                    rfl

theorem cell21_1366404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1366404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366404 prefixEnd_1366404 := by exact prefixLift 1366404
  have htrace : WordTrace (prefixWord ++ tailWord_1366404) baseStart_1366404 baseEnd_1366404 := by
    simpa [prefixWord, tailWord_1366404, baseEnd_1366404] using wordTrace_append hprefix tailTrace_1366404
  have hstable : (prefixWord ++ tailWord_1366404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366404).length < 2 ^ (prefixWord ++ tailWord_1366404).sum := by decide
  have hdescent : baseEnd_1366404 < baseStart_1366404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366449 : List Nat := [1, 2, 2, 4, 1, 4, 7]
def baseStart_1366449 : Nat := 118140960795 + 1366449 * 2 ^ 59
def prefixEnd_1366449 : Nat := 4983230072969 + 3 ^ 40 * 1366449 * 2
def baseEnd_1366449 : Nat := 34649142066944666454485

theorem tailTrace_1366449 : CollatzResearch.WordTrace tailWord_1366449 prefixEnd_1366449 34649142066944666454485 := by
  unfold tailWord_1366449
  simp only [CollatzResearch.WordTrace]
  refine ⟨49838489426596118754702401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33225659617730745836468267 49838489426596118754702401)
  ·
    refine ⟨37378867069947089066026801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49838489426596118754702401 37378867069947089066026801)
    ·
      refine ⟨28034150302460316799520101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37378867069947089066026801 28034150302460316799520101)
      ·
        refine ⟨5256403181711309399910019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28034150302460316799520101 5256403181711309399910019)
        ·
          refine ⟨7884604772566964099865029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256403181711309399910019 7884604772566964099865029)
          ·
            refine ⟨1478363394856305768724693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7884604772566964099865029 1478363394856305768724693)
            ·
              refine ⟨34649142066944666454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1478363394856305768724693 34649142066944666454485)
              ·
                rfl

theorem cell21_1366449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 7].length) (baseStart_1366449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366449 prefixEnd_1366449 := by exact prefixLift 1366449
  have htrace : WordTrace (prefixWord ++ tailWord_1366449) baseStart_1366449 baseEnd_1366449 := by
    simpa [prefixWord, tailWord_1366449, baseEnd_1366449] using wordTrace_append hprefix tailTrace_1366449
  have hstable : (prefixWord ++ tailWord_1366449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366449).length < 2 ^ (prefixWord ++ tailWord_1366449).sum := by decide
  have hdescent : baseEnd_1366449 < baseStart_1366449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366514 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_1366514 : Nat := 118140960795 + 1366514 * 2 ^ 59
def prefixEnd_1366514 : Nat := 4983230072969 + 3 ^ 40 * 1366514 * 2
def baseEnd_1366514 : Nat := 311857112488076329506899

theorem tailTrace_1366514 : CollatzResearch.WordTrace tailWord_1366514 prefixEnd_1366514 311857112488076329506899 := by
  unfold tailWord_1366514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12460215042840158713954649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33227240114240423237212397 12460215042840158713954649)
  ·
    refine ⟨9345161282130119035465987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12460215042840158713954649 9345161282130119035465987)
    ·
      refine ⟨14017741923195178553198981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9345161282130119035465987 14017741923195178553198981)
      ·
        refine ⟨2628326610599095978724809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14017741923195178553198981 2628326610599095978724809)
        ·
          refine ⟨1971244957949321984043607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2628326610599095978724809 1971244957949321984043607)
          ·
            refine ⟨2956867436923982976065411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971244957949321984043607 2956867436923982976065411)
            ·
              refine ⟨4435301155385974464098117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956867436923982976065411 4435301155385974464098117)
              ·
                refine ⟨831618966634870212018397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4435301155385974464098117 831618966634870212018397)
                ·
                  refine ⟨311857112488076329506899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831618966634870212018397 311857112488076329506899)
                  ·
                    rfl

theorem cell21_1366514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_1366514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366514 prefixEnd_1366514 := by exact prefixLift 1366514
  have htrace : WordTrace (prefixWord ++ tailWord_1366514) baseStart_1366514 baseEnd_1366514 := by
    simpa [prefixWord, tailWord_1366514, baseEnd_1366514] using wordTrace_append hprefix tailTrace_1366514
  have hstable : (prefixWord ++ tailWord_1366514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366514).length < 2 ^ (prefixWord ++ tailWord_1366514).sum := by decide
  have hdescent : baseEnd_1366514 < baseStart_1366514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366539 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_1366539 : Nat := 118140960795 + 1366539 * 2 ^ 59
def prefixEnd_1366539 : Nat := 4983230072969 + 3 ^ 40 * 1366539 * 2
def baseEnd_1366539 : Nat := 311862817828681841590181

theorem tailTrace_1366539 : CollatzResearch.WordTrace tailWord_1366539 prefixEnd_1366539 311862817828681841590181 := by
  unfold tailWord_1366539
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841771996270064125478671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33227847997513376083652447 49841771996270064125478671)
  ·
    refine ⟨74762657994405096188218007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49841771996270064125478671 74762657994405096188218007)
    ·
      refine ⟨112143986991607644282327011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74762657994405096188218007 112143986991607644282327011)
      ·
        refine ⟨168215980487411466423490517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112143986991607644282327011 168215980487411466423490517)
        ·
          refine ⟨3942562042673706244300559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168215980487411466423490517 3942562042673706244300559)
          ·
            refine ⟨5913843064010559366450839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942562042673706244300559 5913843064010559366450839)
            ·
              refine ⟨8870764596015839049676259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913843064010559366450839 8870764596015839049676259)
              ·
                refine ⟨13306146894023758574514389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870764596015839049676259 13306146894023758574514389)
                ·
                  refine ⟨311862817828681841590181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13306146894023758574514389 311862817828681841590181)
                  ·
                    rfl

theorem cell21_1366539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_1366539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366539 prefixEnd_1366539 := by exact prefixLift 1366539
  have htrace : WordTrace (prefixWord ++ tailWord_1366539) baseStart_1366539 baseEnd_1366539 := by
    simpa [prefixWord, tailWord_1366539, baseEnd_1366539] using wordTrace_append hprefix tailTrace_1366539
  have hstable : (prefixWord ++ tailWord_1366539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366539).length < 2 ^ (prefixWord ++ tailWord_1366539).sum := by decide
  have hdescent : baseEnd_1366539 < baseStart_1366539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366542 : List Nat := [4, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1366542 : Nat := 118140960795 + 1366542 * 2 ^ 59
def prefixEnd_1366542 : Nat := 4983230072969 + 3 ^ 40 * 1366542 * 2
def baseEnd_1366542 : Nat := 103954500823184834346725

theorem tailTrace_1366542 : CollatzResearch.WordTrace tailWord_1366542 prefixEnd_1366542 103954500823184834346725 := by
  unfold tailWord_1366542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230235176907399454729735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33227920943506130425225253 6230235176907399454729735)
  ·
    refine ⟨9345352765361099182094603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6230235176907399454729735 9345352765361099182094603)
    ·
      refine ⟨14018029148041648773141905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9345352765361099182094603 14018029148041648773141905)
      ·
        refine ⟨10513521861031236579856429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14018029148041648773141905 10513521861031236579856429)
        ·
          refine ⟨3942570697886713717446161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10513521861031236579856429 3942570697886713717446161)
          ·
            refine ⟨2956928023415035288084621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3942570697886713717446161 2956928023415035288084621)
            ·
              refine ⟨1108848008780638233031733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2956928023415035288084621 1108848008780638233031733)
              ·
                refine ⟨103954500823184834346725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1108848008780638233031733 103954500823184834346725)
                ·
                  rfl

theorem cell21_1366542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1366542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366542 prefixEnd_1366542 := by exact prefixLift 1366542
  have htrace : WordTrace (prefixWord ++ tailWord_1366542) baseStart_1366542 baseEnd_1366542 := by
    simpa [prefixWord, tailWord_1366542, baseEnd_1366542] using wordTrace_append hprefix tailTrace_1366542
  have hstable : (prefixWord ++ tailWord_1366542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366542).length < 2 ^ (prefixWord ++ tailWord_1366542).sum := by decide
  have hdescent : baseEnd_1366542 < baseStart_1366542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366553 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_1366553 : Nat := 118140960795 + 1366553 * 2 ^ 59
def prefixEnd_1366553 : Nat := 4983230072969 + 3 ^ 40 * 1366553 * 2
def baseEnd_1366553 : Nat := 311866012819420928356819

theorem tailTrace_1366553 : CollatzResearch.WordTrace tailWord_1366553 prefixEnd_1366553 311866012819420928356819 := by
  unfold tailWord_1366553
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842282618219344516488313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33228188412146229677658875 49842282618219344516488313)
  ·
    refine ⟨37381711963664508387366235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49842282618219344516488313 37381711963664508387366235)
    ·
      refine ⟨56072567945496762581049353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37381711963664508387366235 56072567945496762581049353)
      ·
        refine ⟨42054425959122571935787015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56072567945496762581049353 42054425959122571935787015)
        ·
          refine ⟨63081638938683857903680523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42054425959122571935787015 63081638938683857903680523)
          ·
            refine ⟨94622458408025786855520785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63081638938683857903680523 94622458408025786855520785)
            ·
              refine ⟨70966843806019340141640589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94622458408025786855520785 70966843806019340141640589)
              ·
                refine ⟨26612566427257252553115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70966843806019340141640589 26612566427257252553115221)
                ·
                  refine ⟨311866012819420928356819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26612566427257252553115221 311866012819420928356819)
                  ·
                    rfl

theorem cell21_1366553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_1366553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366553 prefixEnd_1366553 := by exact prefixLift 1366553
  have htrace : WordTrace (prefixWord ++ tailWord_1366553) baseStart_1366553 baseEnd_1366553 := by
    simpa [prefixWord, tailWord_1366553, baseEnd_1366553] using wordTrace_append hprefix tailTrace_1366553
  have hstable : (prefixWord ++ tailWord_1366553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366553).length < 2 ^ (prefixWord ++ tailWord_1366553).sum := by decide
  have hdescent : baseEnd_1366553 < baseStart_1366553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366584 : List Nat := [2, 1, 2, 1, 4, 1, 2, 8]
def baseStart_1366584 : Nat := 118140960795 + 1366584 * 2 ^ 59
def prefixEnd_1366584 : Nat := 4983230072969 + 3 ^ 40 * 1366584 * 2
def baseEnd_1366584 : Nat := 103957695813923921113363

theorem tailTrace_1366584 : CollatzResearch.WordTrace tailWord_1366584 prefixEnd_1366584 103957695813923921113363 := by
  unfold tailWord_1366584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24921706640553518405433403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33228942187404691207244537 24921706640553518405433403)
  ·
    refine ⟨37382559960830277608150105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24921706640553518405433403 37382559960830277608150105)
    ·
      refine ⟨28036919970622708206112579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37382559960830277608150105 28036919970622708206112579)
      ·
        refine ⟨42055379955934062309168869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28036919970622708206112579 42055379955934062309168869)
        ·
          refine ⟨7885383741737636682969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42055379955934062309168869 7885383741737636682969163)
          ·
            refine ⟨11828075612606455024453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7885383741737636682969163 11828075612606455024453745)
            ·
              refine ⟨8871056709454841268340309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11828075612606455024453745 8871056709454841268340309)
              ·
                refine ⟨103957695813923921113363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8871056709454841268340309 103957695813923921113363)
                ·
                  rfl

theorem cell21_1366584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_1366584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366584 prefixEnd_1366584 := by exact prefixLift 1366584
  have htrace : WordTrace (prefixWord ++ tailWord_1366584) baseStart_1366584 baseEnd_1366584 := by
    simpa [prefixWord, tailWord_1366584, baseEnd_1366584] using wordTrace_append hprefix tailTrace_1366584
  have hstable : (prefixWord ++ tailWord_1366584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366584).length < 2 ^ (prefixWord ++ tailWord_1366584).sum := by decide
  have hdescent : baseEnd_1366584 < baseStart_1366584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366767 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_1366767 : Nat := 118140960795 + 1366767 * 2 ^ 59
def prefixEnd_1366767 : Nat := 4983230072969 + 3 ^ 40 * 1366767 * 2
def baseEnd_1366767 : Nat := 311914850535004111789715

theorem tailTrace_1366767 : CollatzResearch.WordTrace tailWord_1366767 prefixEnd_1366767 311914850535004111789715 := by
  unfold tailWord_1366767
  simp only [CollatzResearch.WordTrace]
  refine ⟨49850087839444059064778555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33233391892962706043185703 49850087839444059064778555)
  ·
    refine ⟨74775131759166088597167833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49850087839444059064778555 74775131759166088597167833)
    ·
      refine ⟨56081348819374566447875875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74775131759166088597167833 56081348819374566447875875)
      ·
        refine ⟨84122023229061849671813813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56081348819374566447875875 84122023229061849671813813)
        ·
          refine ⟨7886439677724548406732545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84122023229061849671813813 7886439677724548406732545)
          ·
            refine ⟨5914829758293411305049409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886439677724548406732545 5914829758293411305049409)
            ·
              refine ⟨4436122318720058478787057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914829758293411305049409 4436122318720058478787057)
              ·
                refine ⟨3327091739040043859090293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436122318720058478787057 3327091739040043859090293)
                ·
                  refine ⟨311914850535004111789715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3327091739040043859090293 311914850535004111789715)
                  ·
                    rfl

theorem cell21_1366767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_1366767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366767 prefixEnd_1366767 := by exact prefixLift 1366767
  have htrace : WordTrace (prefixWord ++ tailWord_1366767) baseStart_1366767 baseEnd_1366767 := by
    simpa [prefixWord, tailWord_1366767, baseEnd_1366767] using wordTrace_append hprefix tailTrace_1366767
  have hstable : (prefixWord ++ tailWord_1366767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366767).length < 2 ^ (prefixWord ++ tailWord_1366767).sum := by decide
  have hdescent : baseEnd_1366767 < baseStart_1366767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366770 : List Nat := [3, 2, 1, 3, 1, 4, 2, 5]
def baseStart_1366770 : Nat := 118140960795 + 1366770 * 2 ^ 59
def prefixEnd_1366770 : Nat := 4983230072969 + 3 ^ 40 * 1366770 * 2
def baseEnd_1366770 : Nat := 103971845058625591079903

theorem tailTrace_1366770 : CollatzResearch.WordTrace tailWord_1366770 prefixEnd_1366770 103971845058625591079903 := by
  unfold tailWord_1366770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462549314608297644284441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33233464838955460384758509 12462549314608297644284441)
  ·
    refine ⟨9346911985956223233213331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12462549314608297644284441 9346911985956223233213331)
    ·
      refine ⟨14020367978934334849819997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9346911985956223233213331 14020367978934334849819997)
      ·
        refine ⟨5257637992100375568682499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14020367978934334849819997 5257637992100375568682499)
        ·
          refine ⟨7886456988150563353023749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257637992100375568682499 7886456988150563353023749)
          ·
            refine ⟨1478710685278230628691953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7886456988150563353023749 1478710685278230628691953)
            ·
              refine ⟨1109033013958672971518965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478710685278230628691953 1109033013958672971518965)
              ·
                refine ⟨103971845058625591079903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1109033013958672971518965 103971845058625591079903)
                ·
                  rfl

theorem cell21_1366770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_1366770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366770 prefixEnd_1366770 := by exact prefixLift 1366770
  have htrace : WordTrace (prefixWord ++ tailWord_1366770) baseStart_1366770 baseEnd_1366770 := by
    simpa [prefixWord, tailWord_1366770, baseEnd_1366770] using wordTrace_append hprefix tailTrace_1366770
  have hstable : (prefixWord ++ tailWord_1366770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366770).length < 2 ^ (prefixWord ++ tailWord_1366770).sum := by decide
  have hdescent : baseEnd_1366770 < baseStart_1366770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366781 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1366781 : Nat := 118140960795 + 1366781 * 2 ^ 59
def prefixEnd_1366781 : Nat := 4983230072969 + 3 ^ 40 * 1366781 * 2
def baseEnd_1366781 : Nat := 311918045525743198556353

theorem tailTrace_1366781 : CollatzResearch.WordTrace tailWord_1366781 prefixEnd_1366781 311918045525743198556353 := by
  unfold tailWord_1366781
  simp only [CollatzResearch.WordTrace]
  refine ⟨49850598461393339455788197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33233732307595559637192131 49850598461393339455788197)
  ·
    refine ⟨9346987211511251147960287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49850598461393339455788197 9346987211511251147960287)
    ·
      refine ⟨14020480817266876721940431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9346987211511251147960287 14020480817266876721940431)
      ·
        refine ⟨21030721225900315082910647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14020480817266876721940431 21030721225900315082910647)
        ·
          refine ⟨31546081838850472624365971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21030721225900315082910647 31546081838850472624365971)
          ·
            refine ⟨47319122758275708936548957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31546081838850472624365971 47319122758275708936548957)
            ·
              refine ⟨17744671034353390851205859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47319122758275708936548957 17744671034353390851205859)
              ·
                refine ⟨26617006551530086276808789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17744671034353390851205859 26617006551530086276808789)
                ·
                  refine ⟨311918045525743198556353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26617006551530086276808789 311918045525743198556353)
                  ·
                    rfl

theorem cell21_1366781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1366781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366781 prefixEnd_1366781 := by exact prefixLift 1366781
  have htrace : WordTrace (prefixWord ++ tailWord_1366781) baseStart_1366781 baseEnd_1366781 := by
    simpa [prefixWord, tailWord_1366781, baseEnd_1366781] using wordTrace_append hprefix tailTrace_1366781
  have hstable : (prefixWord ++ tailWord_1366781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366781).length < 2 ^ (prefixWord ++ tailWord_1366781).sum := by decide
  have hdescent : baseEnd_1366781 < baseStart_1366781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366798 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1366798 : Nat := 118140960795 + 1366798 * 2 ^ 59
def prefixEnd_1366798 : Nat := 4983230072969 + 3 ^ 40 * 1366798 * 2
def baseEnd_1366798 : Nat := 311921925157354946772985

theorem tailTrace_1366798 : CollatzResearch.WordTrace tailWord_1366798 prefixEnd_1366798 311921925157354946772985 := by
  unfold tailWord_1366798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231402312791468919894631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33234145668221167572771365 6231402312791468919894631)
  ·
    refine ⟨9347103469187203379841947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231402312791468919894631 9347103469187203379841947)
    ·
      refine ⟨14020655203780805069762921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9347103469187203379841947 14020655203780805069762921)
      ·
        refine ⟨10515491402835603802322191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14020655203780805069762921 10515491402835603802322191)
        ·
          refine ⟨15773237104253405703483287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515491402835603802322191 15773237104253405703483287)
          ·
            refine ⟨23659855656380108555224931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15773237104253405703483287 23659855656380108555224931)
            ·
              refine ⟨35489783484570162832837397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23659855656380108555224931 35489783484570162832837397)
              ·
                refine ⟨1663583600839226382789253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35489783484570162832837397 1663583600839226382789253)
                ·
                  refine ⟨311921925157354946772985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663583600839226382789253 311921925157354946772985)
                  ·
                    rfl

theorem cell21_1366798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1366798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366798 prefixEnd_1366798 := by exact prefixLift 1366798
  have htrace : WordTrace (prefixWord ++ tailWord_1366798) baseStart_1366798 baseEnd_1366798 := by
    simpa [prefixWord, tailWord_1366798, baseEnd_1366798] using wordTrace_append hprefix tailTrace_1366798
  have hstable : (prefixWord ++ tailWord_1366798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366798).length < 2 ^ (prefixWord ++ tailWord_1366798).sum := by decide
  have hdescent : baseEnd_1366798 < baseStart_1366798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366812 : List Nat := [2, 2, 3, 1, 1, 3, 1, 8]
def baseStart_1366812 : Nat := 118140960795 + 1366812 * 2 ^ 59
def prefixEnd_1366812 : Nat := 4983230072969 + 3 ^ 40 * 1366812 * 2
def baseEnd_1366812 : Nat := 103975040049364677846541

theorem tailTrace_1366812 : CollatzResearch.WordTrace tailWord_1366812 prefixEnd_1366812 103975040049364677846541 := by
  unfold tailWord_1366812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24925864562140515875083345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33234486082854021166777793 24925864562140515875083345)
  ·
    refine ⟨18694398421605386906312509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24925864562140515875083345 18694398421605386906312509)
    ·
      refine ⟨7010399408102020089867191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18694398421605386906312509 7010399408102020089867191)
      ·
        refine ⟨10515599112153030134800787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010399408102020089867191 10515599112153030134800787)
        ·
          refine ⟨15773398668229545202201181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515599112153030134800787 15773398668229545202201181)
          ·
            refine ⟨5915024500586079450825443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15773398668229545202201181 5915024500586079450825443)
            ·
              refine ⟨8872536750879119176238165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915024500586079450825443 8872536750879119176238165)
              ·
                refine ⟨103975040049364677846541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8872536750879119176238165 103975040049364677846541)
                ·
                  rfl

theorem cell21_1366812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_1366812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366812 prefixEnd_1366812 := by exact prefixLift 1366812
  have htrace : WordTrace (prefixWord ++ tailWord_1366812) baseStart_1366812 baseEnd_1366812 := by
    simpa [prefixWord, tailWord_1366812, baseEnd_1366812] using wordTrace_append hprefix tailTrace_1366812
  have hstable : (prefixWord ++ tailWord_1366812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366812).length < 2 ^ (prefixWord ++ tailWord_1366812).sum := by decide
  have hdescent : baseEnd_1366812 < baseStart_1366812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366815 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 4]
def baseStart_1366815 : Nat := 118140960795 + 1366815 * 2 ^ 59
def prefixEnd_1366815 : Nat := 4983230072969 + 3 ^ 40 * 1366815 * 2
def baseEnd_1366815 : Nat := 311925804788966694989617

theorem tailTrace_1366815 : CollatzResearch.WordTrace tailWord_1366815 prefixEnd_1366815 311925804788966694989617 := by
  unfold tailWord_1366815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49851838543270163262525899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33234559028846775508350599 49851838543270163262525899)
  ·
    refine ⟨74777757814905244893788849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49851838543270163262525899 74777757814905244893788849)
    ·
      refine ⟨56083318361178933670341637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74777757814905244893788849 56083318361178933670341637)
      ·
        refine ⟨10515622192721050063189057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56083318361178933670341637 10515622192721050063189057)
        ·
          refine ⟨7886716644540787547391793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515622192721050063189057 7886716644540787547391793)
          ·
            refine ⟨5915037483405590660543845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886716644540787547391793 5915037483405590660543845)
            ·
              refine ⟨1109069528138548248851971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5915037483405590660543845 1109069528138548248851971)
              ·
                refine ⟨1663604292207822373277957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109069528138548248851971 1663604292207822373277957)
                ·
                  refine ⟨311925804788966694989617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663604292207822373277957 311925804788966694989617)
                  ·
                    rfl

theorem cell21_1366815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_1366815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366815 prefixEnd_1366815 := by exact prefixLift 1366815
  have htrace : WordTrace (prefixWord ++ tailWord_1366815) baseStart_1366815 baseEnd_1366815 := by
    simpa [prefixWord, tailWord_1366815, baseEnd_1366815] using wordTrace_append hprefix tailTrace_1366815
  have hstable : (prefixWord ++ tailWord_1366815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366815).length < 2 ^ (prefixWord ++ tailWord_1366815).sum := by decide
  have hdescent : baseEnd_1366815 < baseStart_1366815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366852 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1366852 : Nat := 118140960795 + 1366852 * 2 ^ 59
def prefixEnd_1366852 : Nat := 4983230072969 + 3 ^ 40 * 1366852 * 2
def baseEnd_1366852 : Nat := 311934248693062852872875

theorem tailTrace_1366852 : CollatzResearch.WordTrace tailWord_1366852 prefixEnd_1366852 311934248693062852872875 := by
  unfold tailWord_1366852
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926594022068059290811405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33235458696090745721081873 24926594022068059290811405)
  ·
    refine ⟨9347472758275522234054277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24926594022068059290811405 9347472758275522234054277)
    ·
      refine ⟨1752651142176660418885177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9347472758275522234054277 1752651142176660418885177)
      ·
        refine ⟨1314488356632495314163883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1752651142176660418885177 1314488356632495314163883)
        ·
          refine ⟨1971732534948742971245825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314488356632495314163883 1971732534948742971245825)
          ·
            refine ⟨1478799401211557228434369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971732534948742971245825 1478799401211557228434369)
            ·
              refine ⟨1109099550908667921325777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478799401211557228434369 1109099550908667921325777)
              ·
                refine ⟨831824663181500940994333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109099550908667921325777 831824663181500940994333)
                ·
                  refine ⟨311934248693062852872875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831824663181500940994333 311934248693062852872875)
                  ·
                    rfl

theorem cell21_1366852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1366852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366852 prefixEnd_1366852 := by exact prefixLift 1366852
  have htrace : WordTrace (prefixWord ++ tailWord_1366852) baseStart_1366852 baseEnd_1366852 := by
    simpa [prefixWord, tailWord_1366852, baseEnd_1366852] using wordTrace_append hprefix tailTrace_1366852
  have hstable : (prefixWord ++ tailWord_1366852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366852).length < 2 ^ (prefixWord ++ tailWord_1366852).sum := by decide
  have hdescent : baseEnd_1366852 < baseStart_1366852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366874 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1366874 : Nat := 118140960795 + 1366874 * 2 ^ 59
def prefixEnd_1366874 : Nat := 4983230072969 + 3 ^ 40 * 1366874 * 2
def baseEnd_1366874 : Nat := 311939269392795703506163

theorem tailTrace_1366874 : CollatzResearch.WordTrace tailWord_1366874 prefixEnd_1366874 311939269392795703506163 := by
  unfold tailWord_1366874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463497612514104084730919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33235993633370944225949117 12463497612514104084730919)
  ·
    refine ⟨18695246418771156127096379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12463497612514104084730919 18695246418771156127096379)
    ·
      refine ⟨28042869628156734190644569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18695246418771156127096379 28042869628156734190644569)
      ·
        refine ⟨21032152221117550642983427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28042869628156734190644569 21032152221117550642983427)
        ·
          refine ⟨31548228331676325964475141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21032152221117550642983427 31548228331676325964475141)
          ·
            refine ⟨5915292812189311118339089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31548228331676325964475141 5915292812189311118339089)
            ·
              refine ⟨4436469609141983338754317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5915292812189311118339089 4436469609141983338754317)
              ·
                refine ⟨1663676103428243752032869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4436469609141983338754317 1663676103428243752032869)
                ·
                  refine ⟨311939269392795703506163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663676103428243752032869 311939269392795703506163)
                  ·
                    rfl

theorem cell21_1366874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1366874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366874 prefixEnd_1366874 := by exact prefixLift 1366874
  have htrace : WordTrace (prefixWord ++ tailWord_1366874) baseStart_1366874 baseEnd_1366874 := by
    simpa [prefixWord, tailWord_1366874, baseEnd_1366874] using wordTrace_append hprefix tailTrace_1366874
  have hstable : (prefixWord ++ tailWord_1366874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366874).length < 2 ^ (prefixWord ++ tailWord_1366874).sum := by decide
  have hdescent : baseEnd_1366874 < baseStart_1366874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366894 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_1366894 : Nat := 118140960795 + 1366894 * 2 ^ 59
def prefixEnd_1366894 : Nat := 4983230072969 + 3 ^ 40 * 1366894 * 2
def baseEnd_1366894 : Nat := 311943833665280113172789

theorem tailTrace_1366894 : CollatzResearch.WordTrace tailWord_1366894 prefixEnd_1366894 311943833665280113172789 := by
  unfold tailWord_1366894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231839988747994969331467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33236479939989306503101157 6231839988747994969331467)
  ·
    refine ⟨9347759983121992453997201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231839988747994969331467 9347759983121992453997201)
    ·
      refine ⟨7010819987341494340497901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347759983121992453997201 7010819987341494340497901)
      ·
        refine ⟨2629057495253060377686713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7010819987341494340497901 2629057495253060377686713)
        ·
          refine ⟨1971793121439795283265035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629057495253060377686713 1971793121439795283265035)
          ·
            refine ⟨2957689682159692924897553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971793121439795283265035 2957689682159692924897553)
            ·
              refine ⟨2218267261619769693673165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957689682159692924897553 2218267261619769693673165)
              ·
                refine ⟨831850223107413635127437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218267261619769693673165 831850223107413635127437)
                ·
                  refine ⟨311943833665280113172789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831850223107413635127437 311943833665280113172789)
                  ·
                    rfl

theorem cell21_1366894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_1366894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366894 prefixEnd_1366894 := by exact prefixLift 1366894
  have htrace : WordTrace (prefixWord ++ tailWord_1366894) baseStart_1366894 baseEnd_1366894 := by
    simpa [prefixWord, tailWord_1366894, baseEnd_1366894] using wordTrace_append hprefix tailTrace_1366894
  have hstable : (prefixWord ++ tailWord_1366894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366894).length < 2 ^ (prefixWord ++ tailWord_1366894).sum := by decide
  have hdescent : baseEnd_1366894 < baseStart_1366894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366919 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_1366919 : Nat := 118140960795 + 1366919 * 2 ^ 59
def prefixEnd_1366919 : Nat := 4983230072969 + 3 ^ 40 * 1366919 * 2
def baseEnd_1366919 : Nat := 311949539005885625256071

theorem tailTrace_1366919 : CollatzResearch.WordTrace tailWord_1366919 prefixEnd_1366919 311949539005885625256071 := by
  unfold tailWord_1366919
  simp only [CollatzResearch.WordTrace]
  refine ⟨49855631734893389024311811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33237087823262259349541207 49855631734893389024311811)
  ·
    refine ⟨74783447602340083536467717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49855631734893389024311811 74783447602340083536467717)
    ·
      refine ⟨14021896425438765663087697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74783447602340083536467717 14021896425438765663087697)
      ·
        refine ⟨10516422319079074247315773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14021896425438765663087697 10516422319079074247315773)
        ·
          refine ⟨3943658369654652842743415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10516422319079074247315773 3943658369654652842743415)
          ·
            refine ⟨5915487554481979264115123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943658369654652842743415 5915487554481979264115123)
            ·
              refine ⟨8873231331722968896172685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915487554481979264115123 8873231331722968896172685)
              ·
                refine ⟨3327461749396113336064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8873231331722968896172685 3327461749396113336064757)
                ·
                  refine ⟨311949539005885625256071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3327461749396113336064757 311949539005885625256071)
                  ·
                    rfl

theorem cell21_1366919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_1366919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366919 prefixEnd_1366919 := by exact prefixLift 1366919
  have htrace : WordTrace (prefixWord ++ tailWord_1366919) baseStart_1366919 baseEnd_1366919 := by
    simpa [prefixWord, tailWord_1366919, baseEnd_1366919] using wordTrace_append hprefix tailTrace_1366919
  have hstable : (prefixWord ++ tailWord_1366919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366919).length < 2 ^ (prefixWord ++ tailWord_1366919).sum := by decide
  have hdescent : baseEnd_1366919 < baseStart_1366919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366984 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_1366984 : Nat := 118140960795 + 1366984 * 2 ^ 59
def prefixEnd_1366984 : Nat := 4983230072969 + 3 ^ 40 * 1366984 * 2
def baseEnd_1366984 : Nat := 311964372891459956672605

theorem tailTrace_1366984 : CollatzResearch.WordTrace tailWord_1366984 prefixEnd_1366984 311964372891459956672605 := by
  unfold tailWord_1366984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24929001239828952562714003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33238668319771936750285337 24929001239828952562714003)
  ·
    refine ⟨37393501859743428844071005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24929001239828952562714003 37393501859743428844071005)
    ·
      refine ⟨14022563197403785816526627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37393501859743428844071005 14022563197403785816526627)
      ·
        refine ⟨21033844796105678724789941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14022563197403785816526627 21033844796105678724789941)
        ·
          refine ⟨1971922949634907380449057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21033844796105678724789941 1971922949634907380449057)
          ·
            refine ⟨1478942212226180535336793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971922949634907380449057 1478942212226180535336793)
            ·
              refine ⟨1109206659169635401502595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478942212226180535336793 1109206659169635401502595)
              ·
                refine ⟨1663809988754453102253893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109206659169635401502595 1663809988754453102253893)
                ·
                  refine ⟨311964372891459956672605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663809988754453102253893 311964372891459956672605)
                  ·
                    rfl

theorem cell21_1366984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_1366984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1366984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1366984 prefixEnd_1366984 := by exact prefixLift 1366984
  have htrace : WordTrace (prefixWord ++ tailWord_1366984) baseStart_1366984 baseEnd_1366984 := by
    simpa [prefixWord, tailWord_1366984, baseEnd_1366984] using wordTrace_append hprefix tailTrace_1366984
  have hstable : (prefixWord ++ tailWord_1366984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366984).length < 2 ^ (prefixWord ++ tailWord_1366984).sum := by decide
  have hdescent : baseEnd_1366984 < baseStart_1366984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367023 : List Nat := [1, 1, 2, 1, 4, 12]
def baseStart_1367023 : Nat := 118140960795 + 1367023 * 2 ^ 59
def prefixEnd_1367023 : Nat := 4983230072969 + 3 ^ 40 * 1367023 * 2
def baseEnd_1367023 : Nat := 11554565674918687241575

theorem tailTrace_1367023 : CollatzResearch.WordTrace tailWord_1367023 prefixEnd_1367023 11554565674918687241575 := by
  unfold tailWord_1367023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49859424926516614786097723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33239616617677743190731815 49859424926516614786097723)
  ·
    refine ⟨74789137389774922179146585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49859424926516614786097723 74789137389774922179146585)
    ·
      refine ⟨56091853042331191634359939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74789137389774922179146585 56091853042331191634359939)
      ·
        refine ⟨84137779563496787451539909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56091853042331191634359939 84137779563496787451539909)
        ·
          refine ⟨15775833668155647647163733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84137779563496787451539909 15775833668155647647163733)
          ·
            refine ⟨11554565674918687241575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15775833668155647647163733 11554565674918687241575)
            ·
              rfl

theorem cell21_1367023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 12].length) (baseStart_1367023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367023 prefixEnd_1367023 := by exact prefixLift 1367023
  have htrace : WordTrace (prefixWord ++ tailWord_1367023) baseStart_1367023 baseEnd_1367023 := by
    simpa [prefixWord, tailWord_1367023, baseEnd_1367023] using wordTrace_append hprefix tailTrace_1367023
  have hstable : (prefixWord ++ tailWord_1367023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367023).length < 2 ^ (prefixWord ++ tailWord_1367023).sum := by decide
  have hdescent : baseEnd_1367023 < baseStart_1367023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367198 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1367198 : Nat := 118140960795 + 1367198 * 2 ^ 59
def prefixEnd_1367198 : Nat := 4983230072969 + 3 ^ 40 * 1367198 * 2
def baseEnd_1367198 : Nat := 312013210607043140105501

theorem tailTrace_1367198 : CollatzResearch.WordTrace tailWord_1367198 prefixEnd_1367198 312013210607043140105501 := by
  unfold tailWord_1367198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233225962610327459214781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33243871800588413115812165 6233225962610327459214781)
  ·
    refine ⟨2337459735978872797205543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6233225962610327459214781 2337459735978872797205543)
    ·
      refine ⟨3506189603968309195808315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2337459735978872797205543 3506189603968309195808315)
      ·
        refine ⟨5259284405952463793712473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506189603968309195808315 5259284405952463793712473)
        ·
          refine ⟨3944463304464347845284355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5259284405952463793712473 3944463304464347845284355)
          ·
            refine ⟨5916694956696521767926533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944463304464347845284355 5916694956696521767926533)
            ·
              refine ⟨1109380304380597831486225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5916694956696521767926533 1109380304380597831486225)
              ·
                refine ⟨832035228285448373614669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109380304380597831486225 832035228285448373614669)
                ·
                  refine ⟨312013210607043140105501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832035228285448373614669 312013210607043140105501)
                  ·
                    rfl

theorem cell21_1367198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1367198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367198 prefixEnd_1367198 := by exact prefixLift 1367198
  have htrace : WordTrace (prefixWord ++ tailWord_1367198) baseStart_1367198 baseEnd_1367198 := by
    simpa [prefixWord, tailWord_1367198, baseEnd_1367198] using wordTrace_append hprefix tailTrace_1367198
  have hstable : (prefixWord ++ tailWord_1367198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367198).length < 2 ^ (prefixWord ++ tailWord_1367198).sum := by decide
  have hdescent : baseEnd_1367198 < baseStart_1367198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367313 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_1367313 : Nat := 118140960795 + 1367313 * 2 ^ 59
def prefixEnd_1367313 : Nat := 4983230072969 + 3 ^ 40 * 1367313 * 2
def baseEnd_1367313 : Nat := 312039455173828495688599

theorem tailTrace_1367313 : CollatzResearch.WordTrace tailWord_1367313 prefixEnd_1367313 312039455173828495688599 := by
  unfold tailWord_1367313
  simp only [CollatzResearch.WordTrace]
  refine ⟨49870002095465994314154593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33246668063643996209436395 49870002095465994314154593)
  ·
    refine ⟨37402501571599495735615945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49870002095465994314154593 37402501571599495735615945)
    ·
      refine ⟨28051876178699621801711959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37402501571599495735615945 28051876178699621801711959)
      ·
        refine ⟨42077814268049432702567939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28051876178699621801711959 42077814268049432702567939)
        ·
          refine ⟨63116721402074149053851909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42077814268049432702567939 63116721402074149053851909)
          ·
            refine ⟨11834385262888902947597233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63116721402074149053851909 11834385262888902947597233)
            ·
              refine ⟨8875788947166677210697925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11834385262888902947597233 8875788947166677210697925)
              ·
                refine ⟨1664210427593751977005861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8875788947166677210697925 1664210427593751977005861)
                ·
                  refine ⟨312039455173828495688599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664210427593751977005861 312039455173828495688599)
                  ·
                    rfl

theorem cell21_1367313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_1367313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367313 prefixEnd_1367313 := by exact prefixLift 1367313
  have htrace : WordTrace (prefixWord ++ tailWord_1367313) baseStart_1367313 baseEnd_1367313 := by
    simpa [prefixWord, tailWord_1367313, baseEnd_1367313] using wordTrace_append hprefix tailTrace_1367313
  have hstable : (prefixWord ++ tailWord_1367313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367313).length < 2 ^ (prefixWord ++ tailWord_1367313).sum := by decide
  have hdescent : baseEnd_1367313 < baseStart_1367313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367524 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1367524 : Nat := 118140960795 + 1367524 * 2 ^ 59
def prefixEnd_1367524 : Nat := 4983230072969 + 3 ^ 40 * 1367524 * 2
def baseEnd_1367524 : Nat := 312087608248539017671501

theorem tailTrace_1367524 : CollatzResearch.WordTrace tailWord_1367524 prefixEnd_1367524 312087608248539017671501 := by
  unfold tailWord_1367524
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938848948850788675042813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33251798598467718233390417 24938848948850788675042813)
  ·
    refine ⟨9352068355819045753141055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24938848948850788675042813 9352068355819045753141055)
    ·
      refine ⟨14028102533728568629711583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352068355819045753141055 14028102533728568629711583)
      ·
        refine ⟨21042153800592852944567375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14028102533728568629711583 21042153800592852944567375)
        ·
          refine ⟨31563230700889279416851063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21042153800592852944567375 31563230700889279416851063)
          ·
            refine ⟨47344846051333919125276595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31563230700889279416851063 47344846051333919125276595)
            ·
              refine ⟨71017269077000878687914893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47344846051333919125276595 71017269077000878687914893)
              ·
                refine ⟨26631475903875329507968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71017269077000878687914893 26631475903875329507968085)
                ·
                  refine ⟨312087608248539017671501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26631475903875329507968085 312087608248539017671501)
                  ·
                    rfl

theorem cell21_1367524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1367524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367524 prefixEnd_1367524 := by exact prefixLift 1367524
  have htrace : WordTrace (prefixWord ++ tailWord_1367524) baseStart_1367524 baseEnd_1367524 := by
    simpa [prefixWord, tailWord_1367524, baseEnd_1367524] using wordTrace_append hprefix tailTrace_1367524
  have hstable : (prefixWord ++ tailWord_1367524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367524).length < 2 ^ (prefixWord ++ tailWord_1367524).sum := by decide
  have hdescent : baseEnd_1367524 < baseStart_1367524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367544 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_1367544 : Nat := 118140960795 + 1367544 * 2 ^ 59
def prefixEnd_1367544 : Nat := 4983230072969 + 3 ^ 40 * 1367544 * 2
def baseEnd_1367544 : Nat := 312092172521023427338127

theorem tailTrace_1367544 : CollatzResearch.WordTrace tailWord_1367544 prefixEnd_1367544 312092172521023427338127 := by
  unfold tailWord_1367544
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939213678814560382906843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33252284905086080510542457 24939213678814560382906843)
  ·
    refine ⟨37408820518221840574360265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24939213678814560382906843 37408820518221840574360265)
    ·
      refine ⟨28056615388666380430770199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37408820518221840574360265 28056615388666380430770199)
      ·
        refine ⟨42084923082999570646155299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28056615388666380430770199 42084923082999570646155299)
        ·
          refine ⟨63127384624499355969232949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42084923082999570646155299 63127384624499355969232949)
          ·
            refine ⟨5918192308546814622115589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63127384624499355969232949 5918192308546814622115589)
            ·
              refine ⟨1109661057852527741646673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5918192308546814622115589 1109661057852527741646673)
              ·
                refine ⟨832245793389395806235005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109661057852527741646673 832245793389395806235005)
                ·
                  refine ⟨312092172521023427338127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832245793389395806235005 312092172521023427338127)
                  ·
                    rfl

theorem cell21_1367544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_1367544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367544 prefixEnd_1367544 := by exact prefixLift 1367544
  have htrace : WordTrace (prefixWord ++ tailWord_1367544) baseStart_1367544 baseEnd_1367544 := by
    simpa [prefixWord, tailWord_1367544, baseEnd_1367544] using wordTrace_append hprefix tailTrace_1367544
  have hstable : (prefixWord ++ tailWord_1367544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367544).length < 2 ^ (prefixWord ++ tailWord_1367544).sum := by decide
  have hdescent : baseEnd_1367544 < baseStart_1367544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367592 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_1367592 : Nat := 118140960795 + 1367592 * 2 ^ 59
def prefixEnd_1367592 : Nat := 4983230072969 + 3 ^ 40 * 1367592 * 2
def baseEnd_1367592 : Nat := 312103126774986010538029

theorem tailTrace_1367592 : CollatzResearch.WordTrace tailWord_1367592 prefixEnd_1367592 312103126774986010538029 := by
  unfold tailWord_1367592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24940089030727612481780515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33253452040970149975707353 24940089030727612481780515)
  ·
    refine ⟨37410133546091418722670773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24940089030727612481780515 37410133546091418722670773)
    ·
      refine ⟨3507200019946070505250385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37410133546091418722670773 3507200019946070505250385)
      ·
        refine ⟨2630400014959552878937789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507200019946070505250385 2630400014959552878937789)
        ·
          refine ⟨986400005609832329601671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2630400014959552878937789 986400005609832329601671)
          ·
            refine ⟨1479600008414748494402507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986400005609832329601671 1479600008414748494402507)
            ·
              refine ⟨2219400012622122741603761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479600008414748494402507 2219400012622122741603761)
              ·
                refine ⟨1664550009466592056202821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219400012622122741603761 1664550009466592056202821)
                ·
                  refine ⟨312103126774986010538029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664550009466592056202821 312103126774986010538029)
                  ·
                    rfl

theorem cell21_1367592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_1367592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367592 prefixEnd_1367592 := by exact prefixLift 1367592
  have htrace : WordTrace (prefixWord ++ tailWord_1367592) baseStart_1367592 baseEnd_1367592 := by
    simpa [prefixWord, tailWord_1367592, baseEnd_1367592] using wordTrace_append hprefix tailTrace_1367592
  have hstable : (prefixWord ++ tailWord_1367592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367592).length < 2 ^ (prefixWord ++ tailWord_1367592).sum := by decide
  have hdescent : baseEnd_1367592 < baseStart_1367592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367603 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 3]
def baseStart_1367603 : Nat := 118140960795 + 1367603 * 2 ^ 59
def prefixEnd_1367603 : Nat := 4983230072969 + 3 ^ 40 * 1367603 * 2
def baseEnd_1367603 : Nat := 312105637124852435854673

theorem tailTrace_1367603 : CollatzResearch.WordTrace tailWord_1367603 prefixEnd_1367603 312105637124852435854673 := by
  unfold tailWord_1367603
  simp only [CollatzResearch.WordTrace]
  refine ⟨49880579264415373842211463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33253719509610249228140975 49880579264415373842211463)
  ·
    refine ⟨74820868896623060763317195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49880579264415373842211463 74820868896623060763317195)
    ·
      refine ⟨112231303344934591144975793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74820868896623060763317195 112231303344934591144975793)
      ·
        refine ⟨84173477508700943358731845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112231303344934591144975793 84173477508700943358731845)
        ·
          refine ⟨15782527032881426879762221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84173477508700943358731845 15782527032881426879762221)
          ·
            refine ⟨5918447637330535079910833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15782527032881426879762221 5918447637330535079910833)
            ·
              refine ⟨4438835727997901309933125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918447637330535079910833 4438835727997901309933125)
              ·
                refine ⟨832281698999606495612461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4438835727997901309933125 832281698999606495612461)
                ·
                  refine ⟨312105637124852435854673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832281698999606495612461 312105637124852435854673)
                  ·
                    rfl

theorem cell21_1367603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].length) (baseStart_1367603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367603 prefixEnd_1367603 := by exact prefixLift 1367603
  have htrace : WordTrace (prefixWord ++ tailWord_1367603) baseStart_1367603 baseEnd_1367603 := by
    simpa [prefixWord, tailWord_1367603, baseEnd_1367603] using wordTrace_append hprefix tailTrace_1367603
  have hstable : (prefixWord ++ tailWord_1367603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367603).length < 2 ^ (prefixWord ++ tailWord_1367603).sum := by decide
  have hdescent : baseEnd_1367603 < baseStart_1367603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367710 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1367710 : Nat := 118140960795 + 1367710 * 2 ^ 59
def prefixEnd_1367710 : Nat := 4983230072969 + 3 ^ 40 * 1367710 * 2
def baseEnd_1367710 : Nat := 312130055982644027571121

theorem tailTrace_1367710 : CollatzResearch.WordTrace tailWord_1367710 prefixEnd_1367710 312130055982644027571121 := by
  unfold tailWord_1367710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235560234378466389544573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33256321250018487410904389 6235560234378466389544573)
  ·
    refine ⟨2338335087891924896079215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6235560234378466389544573 2338335087891924896079215)
    ·
      refine ⟨3507502631837887344118823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2338335087891924896079215 3507502631837887344118823)
      ·
        refine ⟨5261253947756831016178235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507502631837887344118823 5261253947756831016178235)
        ·
          refine ⟨7891880921635246524267353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261253947756831016178235 7891880921635246524267353)
          ·
            refine ⟨5918910691226434893200515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891880921635246524267353 5918910691226434893200515)
            ·
              refine ⟨8878366036839652339800773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918910691226434893200515 8878366036839652339800773)
              ·
                refine ⟨1664693631907434813712645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8878366036839652339800773 1664693631907434813712645)
                ·
                  refine ⟨312130055982644027571121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664693631907434813712645 312130055982644027571121)
                  ·
                    rfl

theorem cell21_1367710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1367710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367710 prefixEnd_1367710 := by exact prefixLift 1367710
  have htrace : WordTrace (prefixWord ++ tailWord_1367710) baseStart_1367710 baseEnd_1367710 := by
    simpa [prefixWord, tailWord_1367710, baseEnd_1367710] using wordTrace_append hprefix tailTrace_1367710
  have hstable : (prefixWord ++ tailWord_1367710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367710).length < 2 ^ (prefixWord ++ tailWord_1367710).sum := by decide
  have hdescent : baseEnd_1367710 < baseStart_1367710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367713 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 3]
def baseStart_1367713 : Nat := 118140960795 + 1367713 * 2 ^ 59
def prefixEnd_1367713 : Nat := 4983230072969 + 3 ^ 40 * 1367713 * 2
def baseEnd_1367713 : Nat := 312130740623516689021115

theorem tailTrace_1367713 : CollatzResearch.WordTrace tailWord_1367713 prefixEnd_1367713 312130740623516689021115 := by
  unfold tailWord_1367713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49884591294016862628715793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33256394196011241752477195 49884591294016862628715793)
  ·
    refine ⟨37413443470512646971536845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49884591294016862628715793 37413443470512646971536845)
    ·
      refine ⟨14030041301442242614326317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37413443470512646971536845 14030041301442242614326317)
      ·
        refine ⟨5261265488040840980372369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14030041301442242614326317 5261265488040840980372369)
        ·
          refine ⟨3945949116030630735279277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261265488040840980372369 3945949116030630735279277)
          ·
            refine ⟨1479730918511486525729729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3945949116030630735279277 1479730918511486525729729)
            ·
              refine ⟨1109798188883614894297297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479730918511486525729729 1109798188883614894297297)
              ·
                refine ⟨832348641662711170722973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109798188883614894297297 832348641662711170722973)
                ·
                  refine ⟨312130740623516689021115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832348641662711170722973 312130740623516689021115)
                  ·
                    rfl

theorem cell21_1367713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_1367713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367713 prefixEnd_1367713 := by exact prefixLift 1367713
  have htrace : WordTrace (prefixWord ++ tailWord_1367713) baseStart_1367713 baseEnd_1367713 := by
    simpa [prefixWord, tailWord_1367713, baseEnd_1367713] using wordTrace_append hprefix tailTrace_1367713
  have hstable : (prefixWord ++ tailWord_1367713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367713).length < 2 ^ (prefixWord ++ tailWord_1367713).sum := by decide
  have hdescent : baseEnd_1367713 < baseStart_1367713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367738 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1367738 : Nat := 118140960795 + 1367738 * 2 ^ 59
def prefixEnd_1367738 : Nat := 4983230072969 + 3 ^ 40 * 1367738 * 2
def baseEnd_1367738 : Nat := 312136445964122201104397

theorem tailTrace_1367738 : CollatzResearch.WordTrace tailWord_1367738 prefixEnd_1367738 312136445964122201104397 := by
  unfold tailWord_1367738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12471375779731572974593967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33257002079284194598917245 12471375779731572974593967)
  ·
    refine ⟨18707063669597359461890951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12471375779731572974593967 18707063669597359461890951)
    ·
      refine ⟨28060595504396039192836427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18707063669597359461890951 28060595504396039192836427)
      ·
        refine ⟨42090893256594058789254641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28060595504396039192836427 42090893256594058789254641)
        ·
          refine ⟨31568169942445544091940981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42090893256594058789254641 31568169942445544091940981)
          ·
            refine ⟨2959515932104269758619467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31568169942445544091940981 2959515932104269758619467)
            ·
              refine ⟨4439273898156404637929201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959515932104269758619467 4439273898156404637929201)
              ·
                refine ⟨3329455423617303478446901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439273898156404637929201 3329455423617303478446901)
                ·
                  refine ⟨312136445964122201104397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329455423617303478446901 312136445964122201104397)
                  ·
                    rfl

theorem cell21_1367738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1367738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367738 prefixEnd_1367738 := by exact prefixLift 1367738
  have htrace : WordTrace (prefixWord ++ tailWord_1367738) baseStart_1367738 baseEnd_1367738 := by
    simpa [prefixWord, tailWord_1367738, baseEnd_1367738] using wordTrace_append hprefix tailTrace_1367738
  have hstable : (prefixWord ++ tailWord_1367738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367738).length < 2 ^ (prefixWord ++ tailWord_1367738).sum := by decide
  have hdescent : baseEnd_1367738 < baseStart_1367738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367752 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_1367752 : Nat := 118140960795 + 1367752 * 2 ^ 59
def prefixEnd_1367752 : Nat := 4983230072969 + 3 ^ 40 * 1367752 * 2
def baseEnd_1367752 : Nat := 312139640954861287871035

theorem tailTrace_1367752 : CollatzResearch.WordTrace tailWord_1367752 prefixEnd_1367752 312139640954861287871035 := by
  unfold tailWord_1367752
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943006870437786144692755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33257342493917048192923673 24943006870437786144692755)
  ·
    refine ⟨37414510305656679217039133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24943006870437786144692755 37414510305656679217039133)
    ·
      refine ⟨14030441364621254706389675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37414510305656679217039133 14030441364621254706389675)
      ·
        refine ⟨21045662046931882059584513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030441364621254706389675 21045662046931882059584513)
        ·
          refine ⟨15784246535198911544688385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21045662046931882059584513 15784246535198911544688385)
          ·
            refine ⟨11838184901399183658516289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15784246535198911544688385 11838184901399183658516289)
            ·
              refine ⟨8878638676049387743887217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11838184901399183658516289 8878638676049387743887217)
              ·
                refine ⟨6658979007037040807915413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8878638676049387743887217 6658979007037040807915413)
                ·
                  refine ⟨312139640954861287871035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6658979007037040807915413 312139640954861287871035)
                  ·
                    rfl

theorem cell21_1367752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_1367752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367752 prefixEnd_1367752 := by exact prefixLift 1367752
  have htrace : WordTrace (prefixWord ++ tailWord_1367752) baseStart_1367752 baseEnd_1367752 := by
    simpa [prefixWord, tailWord_1367752, baseEnd_1367752] using wordTrace_append hprefix tailTrace_1367752
  have hstable : (prefixWord ++ tailWord_1367752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367752).length < 2 ^ (prefixWord ++ tailWord_1367752).sum := by decide
  have hdescent : baseEnd_1367752 < baseStart_1367752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367769 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1367769 : Nat := 118140960795 + 1367769 * 2 ^ 59
def prefixEnd_1367769 : Nat := 4983230072969 + 3 ^ 40 * 1367769 * 2
def baseEnd_1367769 : Nat := 312143520586473036087667

theorem tailTrace_1367769 : CollatzResearch.WordTrace tailWord_1367769 prefixEnd_1367769 312143520586473036087667 := by
  unfold tailWord_1367769
  simp only [CollatzResearch.WordTrace]
  refine ⟨49886633781813984192754361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33257755854542656128502907 49886633781813984192754361)
  ·
    refine ⟨37414975336360488144565771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49886633781813984192754361 37414975336360488144565771)
    ·
      refine ⟨56122463004540732216848657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37414975336360488144565771 56122463004540732216848657)
      ·
        refine ⟨42091847253405549162636493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56122463004540732216848657 42091847253405549162636493)
        ·
          refine ⟨15784442720027080935988685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42091847253405549162636493 15784442720027080935988685)
          ·
            refine ⟨5919166020010155350995757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15784442720027080935988685 5919166020010155350995757)
            ·
              refine ⟨2219687257503808256623409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5919166020010155350995757 2219687257503808256623409)
              ·
                refine ⟨1664765443127856192467557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219687257503808256623409 1664765443127856192467557)
                ·
                  refine ⟨312143520586473036087667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664765443127856192467557 312143520586473036087667)
                  ·
                    rfl

theorem cell21_1367769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1367769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367769 prefixEnd_1367769 := by exact prefixLift 1367769
  have htrace : WordTrace (prefixWord ++ tailWord_1367769) baseStart_1367769 baseEnd_1367769 := by
    simpa [prefixWord, tailWord_1367769, baseEnd_1367769] using wordTrace_append hprefix tailTrace_1367769
  have hstable : (prefixWord ++ tailWord_1367769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367769).length < 2 ^ (prefixWord ++ tailWord_1367769).sum := by decide
  have hdescent : baseEnd_1367769 < baseStart_1367769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367772 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1367772 : Nat := 118140960795 + 1367772 * 2 ^ 59
def prefixEnd_1367772 : Nat := 4983230072969 + 3 ^ 40 * 1367772 * 2
def baseEnd_1367772 : Nat := 312144205227345697537661

theorem tailTrace_1367772 : CollatzResearch.WordTrace tailWord_1367772 prefixEnd_1367772 312144205227345697537661 := by
  unfold tailWord_1367772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943371600401557852556785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33257828800535410470075713 24943371600401557852556785)
  ·
    refine ⟨18707528700301168389417589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24943371600401557852556785 18707528700301168389417589)
    ·
      refine ⟨1753830815653234536507899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18707528700301168389417589 1753830815653234536507899)
      ·
        refine ⟨2630746223479851804761849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753830815653234536507899 2630746223479851804761849)
        ·
          refine ⟨1973059667609888853571387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630746223479851804761849 1973059667609888853571387)
          ·
            refine ⟨2959589501414833280357081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973059667609888853571387 2959589501414833280357081)
            ·
              refine ⟨2219692126061124960267811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959589501414833280357081 2219692126061124960267811)
              ·
                refine ⟨3329538189091687440401717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219692126061124960267811 3329538189091687440401717)
                ·
                  refine ⟨312144205227345697537661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329538189091687440401717 312144205227345697537661)
                  ·
                    rfl

theorem cell21_1367772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1367772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367772 prefixEnd_1367772 := by exact prefixLift 1367772
  have htrace : WordTrace (prefixWord ++ tailWord_1367772) baseStart_1367772 baseEnd_1367772 := by
    simpa [prefixWord, tailWord_1367772, baseEnd_1367772] using wordTrace_append hprefix tailTrace_1367772
  have hstable : (prefixWord ++ tailWord_1367772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367772).length < 2 ^ (prefixWord ++ tailWord_1367772).sum := by decide
  have hdescent : baseEnd_1367772 < baseStart_1367772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367806 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1367806 : Nat := 118140960795 + 1367806 * 2 ^ 59
def prefixEnd_1367806 : Nat := 4983230072969 + 3 ^ 40 * 1367806 * 2
def baseEnd_1367806 : Nat := 312151964490569193970925

theorem tailTrace_1367806 : CollatzResearch.WordTrace tailWord_1367806 prefixEnd_1367806 312151964490569193970925 := by
  unfold tailWord_1367806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235997910334992438981409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33258655521786626341234181 6235997910334992438981409)
  ·
    refine ⟨4676998432751244329236057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6235997910334992438981409 4676998432751244329236057)
    ·
      refine ⟨3507748824563433246927043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676998432751244329236057 3507748824563433246927043)
      ·
        refine ⟨5261623236845149870390565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507748824563433246927043 5261623236845149870390565)
        ·
          refine ⟨986554356908465600698231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5261623236845149870390565 986554356908465600698231)
          ·
            refine ⟨1479831535362698401047347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986554356908465600698231 1479831535362698401047347)
            ·
              refine ⟨2219747303044047601571021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479831535362698401047347 2219747303044047601571021)
              ·
                refine ⟨832405238641517850589133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2219747303044047601571021 832405238641517850589133)
                ·
                  refine ⟨312151964490569193970925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832405238641517850589133 312151964490569193970925)
                  ·
                    rfl

theorem cell21_1367806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1367806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367806 prefixEnd_1367806 := by exact prefixLift 1367806
  have htrace : WordTrace (prefixWord ++ tailWord_1367806) baseStart_1367806 baseEnd_1367806 := by
    simpa [prefixWord, tailWord_1367806, baseEnd_1367806] using wordTrace_append hprefix tailTrace_1367806
  have hstable : (prefixWord ++ tailWord_1367806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367806).length < 2 ^ (prefixWord ++ tailWord_1367806).sum := by decide
  have hdescent : baseEnd_1367806 < baseStart_1367806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367831 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_1367831 : Nat := 118140960795 + 1367831 * 2 ^ 59
def prefixEnd_1367831 : Nat := 4983230072969 + 3 ^ 40 * 1367831 * 2
def baseEnd_1367831 : Nat := 312157669831174706054207

theorem tailTrace_1367831 : CollatzResearch.WordTrace tailWord_1367831 prefixEnd_1367831 312157669831174706054207 := by
  unfold tailWord_1367831
  simp only [CollatzResearch.WordTrace]
  refine ⟨49888895107589368781511347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33259263405059579187674231 49888895107589368781511347)
  ·
    refine ⟨74833342661384053172267021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49888895107589368781511347 74833342661384053172267021)
    ·
      refine ⟨28062503498019019939600133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74833342661384053172267021 28062503498019019939600133)
      ·
        refine ⟨5261719405878566238675025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28062503498019019939600133 5261719405878566238675025)
        ·
          refine ⟨3946289554408924679006269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261719405878566238675025 3946289554408924679006269)
          ·
            refine ⟨1479858582903346754627351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3946289554408924679006269 1479858582903346754627351)
            ·
              refine ⟨2219787874355020131941027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479858582903346754627351 2219787874355020131941027)
              ·
                refine ⟨3329681811532530197911541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219787874355020131941027 3329681811532530197911541)
                ·
                  refine ⟨312157669831174706054207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329681811532530197911541 312157669831174706054207)
                  ·
                    rfl

theorem cell21_1367831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_1367831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367831 prefixEnd_1367831 := by exact prefixLift 1367831
  have htrace : WordTrace (prefixWord ++ tailWord_1367831) baseStart_1367831 baseEnd_1367831 := by
    simpa [prefixWord, tailWord_1367831, baseEnd_1367831] using wordTrace_append hprefix tailTrace_1367831
  have hstable : (prefixWord ++ tailWord_1367831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367831).length < 2 ^ (prefixWord ++ tailWord_1367831).sum := by decide
  have hdescent : baseEnd_1367831 < baseStart_1367831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367845 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_1367845 : Nat := 118140960795 + 1367845 * 2 ^ 59
def prefixEnd_1367845 : Nat := 4983230072969 + 3 ^ 40 * 1367845 * 2
def baseEnd_1367845 : Nat := 312160864821913792820845

theorem tailTrace_1367845 : CollatzResearch.WordTrace tailWord_1367845 prefixEnd_1367845 312160864821913792820845 := by
  unfold tailWord_1367845
  simp only [CollatzResearch.WordTrace]
  refine ⟨49889405729538649172520989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33259603819692432781680659 49889405729538649172520989)
  ·
    refine ⟨18708527148576993439695371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49889405729538649172520989 18708527148576993439695371)
    ·
      refine ⟨28062790722865490159543057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18708527148576993439695371 28062790722865490159543057)
      ·
        refine ⟨21047093042149117619657293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28062790722865490159543057 21047093042149117619657293)
        ·
          refine ⟨7892659890805919107371485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21047093042149117619657293 7892659890805919107371485)
          ·
            refine ⟨2959747459052219665264307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7892659890805919107371485 2959747459052219665264307)
            ·
              refine ⟨4439621188578329497896461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959747459052219665264307 4439621188578329497896461)
              ·
                refine ⟨1664857945716873561711173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439621188578329497896461 1664857945716873561711173)
                ·
                  refine ⟨312160864821913792820845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664857945716873561711173 312160864821913792820845)
                  ·
                    rfl

theorem cell21_1367845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_1367845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367845 prefixEnd_1367845 := by exact prefixLift 1367845
  have htrace : WordTrace (prefixWord ++ tailWord_1367845) baseStart_1367845 baseEnd_1367845 := by
    simpa [prefixWord, tailWord_1367845, baseEnd_1367845] using wordTrace_append hprefix tailTrace_1367845
  have hstable : (prefixWord ++ tailWord_1367845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367845).length < 2 ^ (prefixWord ++ tailWord_1367845).sum := by decide
  have hdescent : baseEnd_1367845 < baseStart_1367845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367969 : List Nat := [1, 2, 3, 4, 2, 2, 2, 5]
def baseStart_1367969 : Nat := 118140960795 + 1367969 * 2 ^ 59
def prefixEnd_1367969 : Nat := 4983230072969 + 3 ^ 40 * 1367969 * 2
def baseEnd_1367969 : Nat := 104063054437105710917975

theorem tailTrace_1367969 : CollatzResearch.WordTrace tailWord_1367969 prefixEnd_1367969 104063054437105710917975 := by
  unfold tailWord_1367969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893928381089418350034961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33262618920726278900023307 49893928381089418350034961)
  ·
    refine ⟨37420446285817063762526221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49893928381089418350034961 37420446285817063762526221)
    ·
      refine ⟨14032667357181398910947333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37420446285817063762526221 14032667357181398910947333)
      ·
        refine ⟨2631125129471512295802625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14032667357181398910947333 2631125129471512295802625)
        ·
          refine ⟨1973343847103634221851969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631125129471512295802625 1973343847103634221851969)
          ·
            refine ⟨1480007885327725666388977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973343847103634221851969 1480007885327725666388977)
            ·
              refine ⟨1110005913995794249791733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480007885327725666388977 1110005913995794249791733)
              ·
                refine ⟨104063054437105710917975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1110005913995794249791733 104063054437105710917975)
                ·
                  rfl

theorem cell21_1367969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].length) (baseStart_1367969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1367969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1367969 prefixEnd_1367969 := by exact prefixLift 1367969
  have htrace : WordTrace (prefixWord ++ tailWord_1367969) baseStart_1367969 baseEnd_1367969 := by
    simpa [prefixWord, tailWord_1367969, baseEnd_1367969] using wordTrace_append hprefix tailTrace_1367969
  have hstable : (prefixWord ++ tailWord_1367969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367969).length < 2 ^ (prefixWord ++ tailWord_1367969).sum := by decide
  have hdescent : baseEnd_1367969 < baseStart_1367969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368056 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_1368056 : Nat := 118140960795 + 1368056 * 2 ^ 59
def prefixEnd_1368056 : Nat := 4983230072969 + 3 ^ 40 * 1368056 * 2
def baseEnd_1368056 : Nat := 312209017896624314803747

theorem tailTrace_1368056 : CollatzResearch.WordTrace tailWord_1368056 prefixEnd_1368056 312209017896624314803747 := by
  unfold tailWord_1368056
  simp only [CollatzResearch.WordTrace]
  refine ⟨24948550765887116104226011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33264734354516154805634681 24948550765887116104226011)
  ·
    refine ⟨37422826148830674156339017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24948550765887116104226011 37422826148830674156339017)
    ·
      refine ⟨28067119611623005617254263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37422826148830674156339017 28067119611623005617254263)
      ·
        refine ⟨42100679417434508425881395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28067119611623005617254263 42100679417434508425881395)
        ·
          refine ⟨63151019126151762638822093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42100679417434508425881395 63151019126151762638822093)
          ·
            refine ⟨23681632172306910989558285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63151019126151762638822093 23681632172306910989558285)
            ·
              refine ⟨8880612064615091621084357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23681632172306910989558285 8880612064615091621084357)
              ·
                refine ⟨1665114762115329678953317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8880612064615091621084357 1665114762115329678953317)
                ·
                  refine ⟨312209017896624314803747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665114762115329678953317 312209017896624314803747)
                  ·
                    rfl

theorem cell21_1368056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_1368056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368056 prefixEnd_1368056 := by exact prefixLift 1368056
  have htrace : WordTrace (prefixWord ++ tailWord_1368056) baseStart_1368056 baseEnd_1368056 := by
    simpa [prefixWord, tailWord_1368056, baseEnd_1368056] using wordTrace_append hprefix tailTrace_1368056
  have hstable : (prefixWord ++ tailWord_1368056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368056).length < 2 ^ (prefixWord ++ tailWord_1368056).sum := by decide
  have hdescent : baseEnd_1368056 < baseStart_1368056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368059 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 3]
def baseStart_1368059 : Nat := 118140960795 + 1368059 * 2 ^ 59
def prefixEnd_1368059 : Nat := 4983230072969 + 3 ^ 40 * 1368059 * 2
def baseEnd_1368059 : Nat := 312209702537496976253741

theorem tailTrace_1368059 : CollatzResearch.WordTrace tailWord_1368059 prefixEnd_1368059 312209702537496976253741 := by
  unfold tailWord_1368059
  simp only [CollatzResearch.WordTrace]
  refine ⟨49897210950763363720811231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33264807300508909147207487 49897210950763363720811231)
  ·
    refine ⟨74845816426145045581216847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49897210950763363720811231 74845816426145045581216847)
    ·
      refine ⟨112268724639217568371825271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74845816426145045581216847 112268724639217568371825271)
      ·
        refine ⟨168403086958826352557737907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112268724639217568371825271 168403086958826352557737907)
        ·
          refine ⟨252604630438239528836606861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168403086958826352557737907 252604630438239528836606861)
          ·
            refine ⟨94726736414339823313727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252604630438239528836606861 94726736414339823313727573)
            ·
              refine ⟨1110078942355544804457745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 94726736414339823313727573 1110078942355544804457745)
              ·
                refine ⟨832559206766658603343309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110078942355544804457745 832559206766658603343309)
                ·
                  refine ⟨312209702537496976253741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832559206766658603343309 312209702537496976253741)
                  ·
                    rfl

theorem cell21_1368059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].length) (baseStart_1368059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368059 prefixEnd_1368059 := by exact prefixLift 1368059
  have htrace : WordTrace (prefixWord ++ tailWord_1368059) baseStart_1368059 baseEnd_1368059 := by
    simpa [prefixWord, tailWord_1368059, baseEnd_1368059] using wordTrace_append hprefix tailTrace_1368059
  have hstable : (prefixWord ++ tailWord_1368059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368059).length < 2 ^ (prefixWord ++ tailWord_1368059).sum := by decide
  have hdescent : baseEnd_1368059 < baseStart_1368059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368104 : List Nat := [2, 1, 5, 3, 1, 1, 8]
def baseStart_1368104 : Nat := 118140960795 + 1368104 * 2 ^ 59
def prefixEnd_1368104 : Nat := 4983230072969 + 3 ^ 40 * 1368104 * 2
def baseEnd_1368104 : Nat := 34691108016731877555961

theorem tailTrace_1368104 : CollatzResearch.WordTrace tailWord_1368104 prefixEnd_1368104 34691108016731877555961 := by
  unfold tailWord_1368104
  simp only [CollatzResearch.WordTrace]
  refine ⟨24949426117800168203099683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33265901490400224270799577 24949426117800168203099683)
  ·
    refine ⟨37424139176700252304649525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24949426117800168203099683 37424139176700252304649525)
    ·
      refine ⟨3508513047815648653560893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37424139176700252304649525 3508513047815648653560893)
      ·
        refine ⟨1315692392930868245085335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3508513047815648653560893 1315692392930868245085335)
        ·
          refine ⟨1973538589396302367628003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315692392930868245085335 1973538589396302367628003)
          ·
            refine ⟨2960307884094453551442005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973538589396302367628003 2960307884094453551442005)
            ·
              refine ⟨34691108016731877555961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2960307884094453551442005 34691108016731877555961)
              ·
                rfl

theorem cell21_1368104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 8].length) (baseStart_1368104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368104 prefixEnd_1368104 := by exact prefixLift 1368104
  have htrace : WordTrace (prefixWord ++ tailWord_1368104) baseStart_1368104 baseEnd_1368104 := by
    simpa [prefixWord, tailWord_1368104, baseEnd_1368104] using wordTrace_append hprefix tailTrace_1368104
  have hstable : (prefixWord ++ tailWord_1368104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368104).length < 2 ^ (prefixWord ++ tailWord_1368104).sum := by decide
  have hdescent : baseEnd_1368104 < baseStart_1368104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368214 : List Nat := [5, 3, 2, 1, 1, 9]
def baseStart_1368214 : Nat := 118140960795 + 1368214 * 2 ^ 59
def prefixEnd_1368214 : Nat := 4983230072969 + 3 ^ 40 * 1368214 * 2
def baseEnd_1368214 : Nat := 11564632431453746339633

theorem tailTrace_1368214 : CollatzResearch.WordTrace tailWord_1368214 prefixEnd_1368214 11564632431453746339633 := by
  unfold tailWord_1368214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118929016575114074543981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33268576176801216795135797 3118929016575114074543981)
  ·
    refine ⟨1169598381215667777953993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3118929016575114074543981 1169598381215667777953993)
    ·
      refine ⟨877198785911750833465495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169598381215667777953993 877198785911750833465495)
      ·
        refine ⟨1315798178867626250198243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877198785911750833465495 1315798178867626250198243)
        ·
          refine ⟨1973697268301439375297365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315798178867626250198243 1973697268301439375297365)
          ·
            refine ⟨11564632431453746339633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1973697268301439375297365 11564632431453746339633)
            ·
              rfl

theorem cell21_1368214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 9].length) (baseStart_1368214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368214 prefixEnd_1368214 := by exact prefixLift 1368214
  have htrace : WordTrace (prefixWord ++ tailWord_1368214) baseStart_1368214 baseEnd_1368214 := by
    simpa [prefixWord, tailWord_1368214, baseEnd_1368214] using wordTrace_append hprefix tailTrace_1368214
  have hstable : (prefixWord ++ tailWord_1368214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368214).length < 2 ^ (prefixWord ++ tailWord_1368214).sum := by decide
  have hdescent : baseEnd_1368214 < baseStart_1368214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368225 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_1368225 : Nat := 118140960795 + 1368225 * 2 ^ 59
def prefixEnd_1368225 : Nat := 4983230072969 + 3 ^ 40 * 1368225 * 2
def baseEnd_1368225 : Nat := 312247585999117576486735

theorem tailTrace_1368225 : CollatzResearch.WordTrace tailWord_1368225 prefixEnd_1368225 312247585999117576486735 := by
  unfold tailWord_1368225
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903265468161974071354129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33268843645441316047569419 49903265468161974071354129)
  ·
    refine ⟨37427449101121480553515597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49903265468161974071354129 37427449101121480553515597)
    ·
      refine ⟨14035293412920555207568349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37427449101121480553515597 14035293412920555207568349)
      ·
        refine ⟨5263235029845208202838131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14035293412920555207568349 5263235029845208202838131)
        ·
          refine ⟨7894852544767812304257197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263235029845208202838131 7894852544767812304257197)
          ·
            refine ⟨2960569704287929614096449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7894852544767812304257197 2960569704287929614096449)
            ·
              refine ⟨2220427278215947210572337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2960569704287929614096449 2220427278215947210572337)
              ·
                refine ⟨1665320458661960407929253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220427278215947210572337 1665320458661960407929253)
                ·
                  refine ⟨312247585999117576486735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665320458661960407929253 312247585999117576486735)
                  ·
                    rfl

theorem cell21_1368225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_1368225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368225 prefixEnd_1368225 := by exact prefixLift 1368225
  have htrace : WordTrace (prefixWord ++ tailWord_1368225) baseStart_1368225 baseEnd_1368225 := by
    simpa [prefixWord, tailWord_1368225, baseEnd_1368225] using wordTrace_append hprefix tailTrace_1368225
  have hstable : (prefixWord ++ tailWord_1368225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368225).length < 2 ^ (prefixWord ++ tailWord_1368225).sum := by decide
  have hdescent : baseEnd_1368225 < baseStart_1368225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368267 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_1368267 : Nat := 118140960795 + 1368267 * 2 ^ 59
def prefixEnd_1368267 : Nat := 4983230072969 + 3 ^ 40 * 1368267 * 2
def baseEnd_1368267 : Nat := 312257170971334836786649

theorem tailTrace_1368267 : CollatzResearch.WordTrace tailWord_1368267 prefixEnd_1368267 312257170971334836786649 := by
  unfold tailWord_1368267
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904797334009815244383055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33269864889339876829588703 49904797334009815244383055)
  ·
    refine ⟨74857196001014722866574583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49904797334009815244383055 74857196001014722866574583)
    ·
      refine ⟨112285794001522084299861875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74857196001014722866574583 112285794001522084299861875)
      ·
        refine ⟨168428691002283126449792813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112285794001522084299861875 168428691002283126449792813)
        ·
          refine ⟨63160759125856172418672305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168428691002283126449792813 63160759125856172418672305)
          ·
            refine ⟨47370569344392129314004229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63160759125856172418672305 47370569344392129314004229)
            ·
              refine ⟨8881981752073524246375793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47370569344392129314004229 8881981752073524246375793)
              ·
                refine ⟨6661486314055143184781845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881981752073524246375793 6661486314055143184781845)
                ·
                  refine ⟨312257170971334836786649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6661486314055143184781845 312257170971334836786649)
                  ·
                    rfl

theorem cell21_1368267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_1368267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368267 prefixEnd_1368267 := by exact prefixLift 1368267
  have htrace : WordTrace (prefixWord ++ tailWord_1368267) baseStart_1368267 baseEnd_1368267 := by
    simpa [prefixWord, tailWord_1368267, baseEnd_1368267] using wordTrace_append hprefix tailTrace_1368267
  have hstable : (prefixWord ++ tailWord_1368267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368267).length < 2 ^ (prefixWord ++ tailWord_1368267).sum := by decide
  have hdescent : baseEnd_1368267 < baseStart_1368267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368298 : List Nat := [3, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1368298 : Nat := 118140960795 + 1368298 * 2 ^ 59
def prefixEnd_1368298 : Nat := 4983230072969 + 3 ^ 40 * 1368298 * 2
def baseEnd_1368298 : Nat := 104088081864561890589973

theorem tailTrace_1368298 : CollatzResearch.WordTrace tailWord_1368298 prefixEnd_1368298 104088081864561890589973 := by
  unfold tailWord_1368298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476481999224376884690387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33270618664598338359174365 12476481999224376884690387)
  ·
    refine ⟨18714722998836565327035581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12476481999224376884690387 18714722998836565327035581)
    ·
      refine ⟨7018021124563711997638343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18714722998836565327035581 7018021124563711997638343)
      ·
        refine ⟨10527031686845567996457515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018021124563711997638343 10527031686845567996457515)
        ·
          refine ⟨15790547530268351994686273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527031686845567996457515 15790547530268351994686273)
          ·
            refine ⟨11842910647701263996014705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15790547530268351994686273 11842910647701263996014705)
            ·
              refine ⟨8882182985775947997011029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11842910647701263996014705 8882182985775947997011029)
              ·
                refine ⟨104088081864561890589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8882182985775947997011029 104088081864561890589973)
                ·
                  rfl

theorem cell21_1368298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1368298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368298 prefixEnd_1368298 := by exact prefixLift 1368298
  have htrace : WordTrace (prefixWord ++ tailWord_1368298) baseStart_1368298 baseEnd_1368298 := by
    simpa [prefixWord, tailWord_1368298, baseEnd_1368298] using wordTrace_append hprefix tailTrace_1368298
  have hstable : (prefixWord ++ tailWord_1368298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368298).length < 2 ^ (prefixWord ++ tailWord_1368298).sum := by decide
  have hdescent : baseEnd_1368298 < baseStart_1368298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368490 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1368490 : Nat := 118140960795 + 1368490 * 2 ^ 59
def prefixEnd_1368490 : Nat := 4983230072969 + 3 ^ 40 * 1368490 * 2
def baseEnd_1368490 : Nat := 312308062609536004569527

theorem tailTrace_1368490 : CollatzResearch.WordTrace tailWord_1368490 prefixEnd_1368490 312308062609536004569527 := by
  unfold tailWord_1368490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478232703050481082437731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33275287208134616219833949 12478232703050481082437731)
  ·
    refine ⟨18717349054575721623656597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12478232703050481082437731 18717349054575721623656597)
    ·
      refine ⟨877375736933236951108903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18717349054575721623656597 877375736933236951108903)
      ·
        refine ⟨1316063605399855426663355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877375736933236951108903 1316063605399855426663355)
        ·
          refine ⟨1974095408099783139995033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316063605399855426663355 1974095408099783139995033)
          ·
            refine ⟨1480571556074837354996275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974095408099783139995033 1480571556074837354996275)
            ·
              refine ⟨2220857334112256032494413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480571556074837354996275 2220857334112256032494413)
              ·
                refine ⟨832821500292096012185405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2220857334112256032494413 832821500292096012185405)
                ·
                  refine ⟨312308062609536004569527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832821500292096012185405 312308062609536004569527)
                  ·
                    rfl

theorem cell21_1368490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1368490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368490 prefixEnd_1368490 := by exact prefixLift 1368490
  have htrace : WordTrace (prefixWord ++ tailWord_1368490) baseStart_1368490 baseEnd_1368490 := by
    simpa [prefixWord, tailWord_1368490, baseEnd_1368490] using wordTrace_append hprefix tailTrace_1368490
  have hstable : (prefixWord ++ tailWord_1368490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368490).length < 2 ^ (prefixWord ++ tailWord_1368490).sum := by decide
  have hdescent : baseEnd_1368490 < baseStart_1368490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368585 : List Nat := [1, 2, 1, 1, 3, 1, 2, 10]
def baseStart_1368585 : Nat := 118140960795 + 1368585 * 2 ^ 59
def prefixEnd_1368585 : Nat := 4983230072969 + 3 ^ 40 * 1368585 * 2
def baseEnd_1368585 : Nat := 104109914301278983495333

theorem tailTrace_1368585 : CollatzResearch.WordTrace tailWord_1368585 prefixEnd_1368585 104109914301278983495333 := by
  unfold tailWord_1368585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49916395746857755554459209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33277597164571837036306139 49916395746857755554459209)
  ·
    refine ⟨37437296810143316665844407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49916395746857755554459209 37437296810143316665844407)
    ·
      refine ⟨56155945215214974998766611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37437296810143316665844407 56155945215214974998766611)
      ·
        refine ⟨84233917822822462498149917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56155945215214974998766611 84233917822822462498149917)
        ·
          refine ⟨31587719183558423436806219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84233917822822462498149917 31587719183558423436806219)
          ·
            refine ⟨47381578775337635155209329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31587719183558423436806219 47381578775337635155209329)
            ·
              refine ⟨35536184081503226366406997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47381578775337635155209329 35536184081503226366406997)
              ·
                refine ⟨104109914301278983495333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35536184081503226366406997 104109914301278983495333)
                ·
                  rfl

theorem cell21_1368585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_1368585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368585 prefixEnd_1368585 := by exact prefixLift 1368585
  have htrace : WordTrace (prefixWord ++ tailWord_1368585) baseStart_1368585 baseEnd_1368585 := by
    simpa [prefixWord, tailWord_1368585, baseEnd_1368585] using wordTrace_append hprefix tailTrace_1368585
  have hstable : (prefixWord ++ tailWord_1368585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368585).length < 2 ^ (prefixWord ++ tailWord_1368585).sum := by decide
  have hdescent : baseEnd_1368585 < baseStart_1368585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368588 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1368588 : Nat := 118140960795 + 1368588 * 2 ^ 59
def prefixEnd_1368588 : Nat := 4983230072969 + 3 ^ 40 * 1368588 * 2
def baseEnd_1368588 : Nat := 312330427544709611935993

theorem tailTrace_1368588 : CollatzResearch.WordTrace tailWord_1368588 prefixEnd_1368588 312330427544709611935993 := by
  unfold tailWord_1368588
  simp only [CollatzResearch.WordTrace]
  refine ⟨24958252582923443533409209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33277670110564591377878945 24958252582923443533409209)
  ·
    refine ⟨18718689437192582650056907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24958252582923443533409209 18718689437192582650056907)
    ·
      refine ⟨28078034155788873975085361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18718689437192582650056907 28078034155788873975085361)
      ·
        refine ⟨21058525616841655481314021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28078034155788873975085361 21058525616841655481314021)
        ·
          refine ⟨3948473553157810402746379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21058525616841655481314021 3948473553157810402746379)
          ·
            refine ⟨5922710329736715604119569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948473553157810402746379 5922710329736715604119569)
            ·
              refine ⟨4442032747302536703089677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922710329736715604119569 4442032747302536703089677)
              ·
                refine ⟨1665762280238451263658629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4442032747302536703089677 1665762280238451263658629)
                ·
                  refine ⟨312330427544709611935993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665762280238451263658629 312330427544709611935993)
                  ·
                    rfl

theorem cell21_1368588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1368588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368588 prefixEnd_1368588 := by exact prefixLift 1368588
  have htrace : WordTrace (prefixWord ++ tailWord_1368588) baseStart_1368588 baseEnd_1368588 := by
    simpa [prefixWord, tailWord_1368588, baseEnd_1368588] using wordTrace_append hprefix tailTrace_1368588
  have hstable : (prefixWord ++ tailWord_1368588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368588).length < 2 ^ (prefixWord ++ tailWord_1368588).sum := by decide
  have hdescent : baseEnd_1368588 < baseStart_1368588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368622 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1368622 : Nat := 118140960795 + 1368622 * 2 ^ 59
def prefixEnd_1368622 : Nat := 4983230072969 + 3 ^ 40 * 1368622 * 2
def baseEnd_1368622 : Nat := 312338186807933108369257

theorem tailTrace_1368622 : CollatzResearch.WordTrace tailWord_1368622 prefixEnd_1368622 312338186807933108369257 := by
  unfold tailWord_1368622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239718155965463859194515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33278496831815807249037413 6239718155965463859194515)
  ·
    refine ⟨9359577233948195788791773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6239718155965463859194515 9359577233948195788791773)
    ·
      refine ⟨3509841462730573420796915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9359577233948195788791773 3509841462730573420796915)
      ·
        refine ⟨5264762194095860131195373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509841462730573420796915 5264762194095860131195373)
        ·
          refine ⟨1974285822785947549198265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5264762194095860131195373 1974285822785947549198265)
          ·
            refine ⟨1480714367089460661898699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974285822785947549198265 1480714367089460661898699)
            ·
              refine ⟨2221071550634190992848049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480714367089460661898699 2221071550634190992848049)
              ·
                refine ⟨1665803662975643244636037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221071550634190992848049 1665803662975643244636037)
                ·
                  refine ⟨312338186807933108369257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665803662975643244636037 312338186807933108369257)
                  ·
                    rfl

theorem cell21_1368622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1368622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368622 prefixEnd_1368622 := by exact prefixLift 1368622
  have htrace : WordTrace (prefixWord ++ tailWord_1368622) baseStart_1368622 baseEnd_1368622 := by
    simpa [prefixWord, tailWord_1368622, baseEnd_1368622] using wordTrace_append hprefix tailTrace_1368622
  have hstable : (prefixWord ++ tailWord_1368622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368622).length < 2 ^ (prefixWord ++ tailWord_1368622).sum := by decide
  have hdescent : baseEnd_1368622 < baseStart_1368622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368633 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1368633 : Nat := 118140960795 + 1368633 * 2 ^ 59
def prefixEnd_1368633 : Nat := 4983230072969 + 3 ^ 40 * 1368633 * 2
def baseEnd_1368633 : Nat := 312340697157799533685901

theorem tailTrace_1368633 : CollatzResearch.WordTrace tailWord_1368633 prefixEnd_1368633 312340697157799533685901 := by
  unfold tailWord_1368633
  simp only [CollatzResearch.WordTrace]
  refine ⟨49918146450683859752206553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278764300455906501471035 49918146450683859752206553)
  ·
    refine ⟨37438609838012894814154915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49918146450683859752206553 37438609838012894814154915)
    ·
      refine ⟨56157914757019342221232373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37438609838012894814154915 56157914757019342221232373)
      ·
        refine ⟨5264804508470563333240535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56157914757019342221232373 5264804508470563333240535)
        ·
          refine ⟨7897206762705844999860803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264804508470563333240535 7897206762705844999860803)
          ·
            refine ⟨11845810144058767499791205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897206762705844999860803 11845810144058767499791205)
            ·
              refine ⟨2221089402011018906210851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11845810144058767499791205 2221089402011018906210851)
              ·
                refine ⟨3331634103016528359316277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221089402011018906210851 3331634103016528359316277)
                ·
                  refine ⟨312340697157799533685901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3331634103016528359316277 312340697157799533685901)
                  ·
                    rfl

theorem cell21_1368633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1368633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368633 prefixEnd_1368633 := by exact prefixLift 1368633
  have htrace : WordTrace (prefixWord ++ tailWord_1368633) baseStart_1368633 baseEnd_1368633 := by
    simpa [prefixWord, tailWord_1368633, baseEnd_1368633] using wordTrace_append hprefix tailTrace_1368633
  have hstable : (prefixWord ++ tailWord_1368633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368633).length < 2 ^ (prefixWord ++ tailWord_1368633).sum := by decide
  have hdescent : baseEnd_1368633 < baseStart_1368633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368670 : List Nat := [4, 4, 1, 2, 2, 1, 7]
def baseStart_1368670 : Nat := 118140960795 + 1368670 * 2 ^ 59
def prefixEnd_1368670 : Nat := 4983230072969 + 3 ^ 40 * 1368670 * 2
def baseEnd_1368670 : Nat := 34705460117988410174351

theorem tailTrace_1368670 : CollatzResearch.WordTrace tailWord_1368670 prefixEnd_1368670 34705460117988410174351 := by
  unfold tailWord_1368670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239936993943726883912933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33279663967699876714202309 6239936993943726883912933)
  ·
    refine ⟨1169988186364448790733675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6239936993943726883912933 1169988186364448790733675)
    ·
      refine ⟨1754982279546673186100513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169988186364448790733675 1754982279546673186100513)
      ·
        refine ⟨1316236709660004889575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754982279546673186100513 1316236709660004889575385)
        ·
          refine ⟨987177532245003667181539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316236709660004889575385 987177532245003667181539)
          ·
            refine ⟨1480766298367505500772309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987177532245003667181539 1480766298367505500772309)
            ·
              refine ⟨34705460117988410174351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1480766298367505500772309 34705460117988410174351)
              ·
                rfl

theorem cell21_1368670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 7].length) (baseStart_1368670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368670 prefixEnd_1368670 := by exact prefixLift 1368670
  have htrace : WordTrace (prefixWord ++ tailWord_1368670) baseStart_1368670 baseEnd_1368670 := by
    simpa [prefixWord, tailWord_1368670, baseEnd_1368670] using wordTrace_append hprefix tailTrace_1368670
  have hstable : (prefixWord ++ tailWord_1368670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368670).length < 2 ^ (prefixWord ++ tailWord_1368670).sum := by decide
  have hdescent : baseEnd_1368670 < baseStart_1368670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368737 : List Nat := [1, 2, 3, 3, 12]
def baseStart_1368737 : Nat := 118140960795 + 1368737 * 2 ^ 59
def prefixEnd_1368737 : Nat := 4983230072969 + 3 ^ 40 * 1368737 * 2
def baseEnd_1368737 : Nat := 3856351004626153875955

theorem tailTrace_1368737 : CollatzResearch.WordTrace tailWord_1368737 prefixEnd_1368737 3856351004626153875955 := by
  unfold tailWord_1368737
  simp only [CollatzResearch.WordTrace]
  refine ⟨49921939642307085513992465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33281293094871390342661643 49921939642307085513992465)
  ·
    refine ⟨37441454731730314135494349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49921939642307085513992465 37441454731730314135494349)
    ·
      refine ⟨14040545524398867800810381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37441454731730314135494349 14040545524398867800810381)
      ·
        refine ⟨5265204571649575425303893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14040545524398867800810381 5265204571649575425303893)
        ·
          refine ⟨3856351004626153875955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5265204571649575425303893 3856351004626153875955)
          ·
            rfl

theorem cell21_1368737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 12].length) (baseStart_1368737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368737 prefixEnd_1368737 := by exact prefixLift 1368737
  have htrace : WordTrace (prefixWord ++ tailWord_1368737) baseStart_1368737 baseEnd_1368737 := by
    simpa [prefixWord, tailWord_1368737, baseEnd_1368737] using wordTrace_append hprefix tailTrace_1368737
  have hstable : (prefixWord ++ tailWord_1368737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368737).length < 2 ^ (prefixWord ++ tailWord_1368737).sum := by decide
  have hdescent : baseEnd_1368737 < baseStart_1368737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368740 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1368740 : Nat := 118140960795 + 1368740 * 2 ^ 59
def prefixEnd_1368740 : Nat := 4983230072969 + 3 ^ 40 * 1368740 * 2
def baseEnd_1368740 : Nat := 312365116015591125402349

theorem tailTrace_1368740 : CollatzResearch.WordTrace tailWord_1368740 prefixEnd_1368740 312365116015591125402349 := by
  unfold tailWord_1368740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961024530648108513175837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33281366040864144684234449 24961024530648108513175837)
  ·
    refine ⟨9360384198993040692440939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24961024530648108513175837 9360384198993040692440939)
    ·
      refine ⟨14040576298489561038661409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360384198993040692440939 14040576298489561038661409)
      ·
        refine ⟨10530432223867170778996057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14040576298489561038661409 10530432223867170778996057)
        ·
          refine ⟨7897824167900378084247043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10530432223867170778996057 7897824167900378084247043)
          ·
            refine ⟨11846736251850567126370565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897824167900378084247043 11846736251850567126370565)
            ·
              refine ⟨2221263047221981336194481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11846736251850567126370565 2221263047221981336194481)
              ·
                refine ⟨1665947285416486002145861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221263047221981336194481 1665947285416486002145861)
                ·
                  refine ⟨312365116015591125402349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665947285416486002145861 312365116015591125402349)
                  ·
                    rfl

theorem cell21_1368740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1368740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368740 prefixEnd_1368740 := by exact prefixLift 1368740
  have htrace : WordTrace (prefixWord ++ tailWord_1368740) baseStart_1368740 baseEnd_1368740 := by
    simpa [prefixWord, tailWord_1368740, baseEnd_1368740] using wordTrace_append hprefix tailTrace_1368740
  have hstable : (prefixWord ++ tailWord_1368740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368740).length < 2 ^ (prefixWord ++ tailWord_1368740).sum := by decide
  have hdescent : baseEnd_1368740 < baseStart_1368740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368768 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_1368768 : Nat := 118140960795 + 1368768 * 2 ^ 59
def prefixEnd_1368768 : Nat := 4983230072969 + 3 ^ 40 * 1368768 * 2
def baseEnd_1368768 : Nat := 312371505997069298935625

theorem tailTrace_1368768 : CollatzResearch.WordTrace tailWord_1368768 prefixEnd_1368768 312371505997069298935625 := by
  unfold tailWord_1368768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961535152597388904185479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33282046870129851872247305 24961535152597388904185479)
  ·
    refine ⟨37442302728896083356278219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24961535152597388904185479 37442302728896083356278219)
    ·
      refine ⟨56163454093344125034417329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37442302728896083356278219 56163454093344125034417329)
      ·
        refine ⟨42122590570008093775812997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56163454093344125034417329 42122590570008093775812997)
        ·
          refine ⟨7897985731876517582964937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42122590570008093775812997 7897985731876517582964937)
          ·
            refine ⟨5923489298907388187223703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7897985731876517582964937 5923489298907388187223703)
            ·
              refine ⟨8885233948361082280835555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923489298907388187223703 8885233948361082280835555)
              ·
                refine ⟨13327850922541623421253333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885233948361082280835555 13327850922541623421253333)
                ·
                  refine ⟨312371505997069298935625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13327850922541623421253333 312371505997069298935625)
                  ·
                    rfl

theorem cell21_1368768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_1368768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368768 prefixEnd_1368768 := by exact prefixLift 1368768
  have htrace : WordTrace (prefixWord ++ tailWord_1368768) baseStart_1368768 baseEnd_1368768 := by
    simpa [prefixWord, tailWord_1368768, baseEnd_1368768] using wordTrace_append hprefix tailTrace_1368768
  have hstable : (prefixWord ++ tailWord_1368768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368768).length < 2 ^ (prefixWord ++ tailWord_1368768).sum := by decide
  have hdescent : baseEnd_1368768 < baseStart_1368768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368799 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_1368799 : Nat := 118140960795 + 1368799 * 2 ^ 59
def prefixEnd_1368799 : Nat := 4983230072969 + 3 ^ 40 * 1368799 * 2
def baseEnd_1368799 : Nat := 312378580619420133918895

theorem tailTrace_1368799 : CollatzResearch.WordTrace tailWord_1368799 prefixEnd_1368799 312378580619420133918895 := by
  unfold tailWord_1368799
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924200968082470102749451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33282800645388313401832967 49924200968082470102749451)
  ·
    refine ⟨74886301452123705154124177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49924200968082470102749451 74886301452123705154124177)
    ·
      refine ⟨56164726089092778865593133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74886301452123705154124177 56164726089092778865593133)
      ·
        refine ⟨21061772283409792074597425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56164726089092778865593133 21061772283409792074597425)
        ·
          refine ⟨15796329212557344055948069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21061772283409792074597425 15796329212557344055948069)
          ·
            refine ⟨2961811727354502010490263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15796329212557344055948069 2961811727354502010490263)
            ·
              refine ⟨4442717591031753015735395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961811727354502010490263 4442717591031753015735395)
              ·
                refine ⟨6664076386547629523603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442717591031753015735395 6664076386547629523603093)
                ·
                  refine ⟨312378580619420133918895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6664076386547629523603093 312378580619420133918895)
                  ·
                    rfl

theorem cell21_1368799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_1368799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368799 prefixEnd_1368799 := by exact prefixLift 1368799
  have htrace : WordTrace (prefixWord ++ tailWord_1368799) baseStart_1368799 baseEnd_1368799 := by
    simpa [prefixWord, tailWord_1368799, baseEnd_1368799] using wordTrace_append hprefix tailTrace_1368799
  have hstable : (prefixWord ++ tailWord_1368799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368799).length < 2 ^ (prefixWord ++ tailWord_1368799).sum := by decide
  have hdescent : baseEnd_1368799 < baseStart_1368799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368816 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1368816 : Nat := 118140960795 + 1368816 * 2 ^ 59
def prefixEnd_1368816 : Nat := 4983230072969 + 3 ^ 40 * 1368816 * 2
def baseEnd_1368816 : Nat := 312382460251031882135527

theorem tailTrace_1368816 : CollatzResearch.WordTrace tailWord_1368816 prefixEnd_1368816 312382460251031882135527 := by
  unfold tailWord_1368816
  simp only [CollatzResearch.WordTrace]
  refine ⟨24962410504510441003059151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33283214006013921337412201 24962410504510441003059151)
  ·
    refine ⟨37443615756765661504588727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24962410504510441003059151 37443615756765661504588727)
    ·
      refine ⟨56165423635148492256883091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37443615756765661504588727 56165423635148492256883091)
      ·
        refine ⟨84248135452722738385324637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56165423635148492256883091 84248135452722738385324637)
        ·
          refine ⟨31593050794771026894496739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84248135452722738385324637 31593050794771026894496739)
          ·
            refine ⟨47389576192156540341745109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31593050794771026894496739 47389576192156540341745109)
            ·
              refine ⟨1110693192003668914259651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47389576192156540341745109 1110693192003668914259651)
              ·
                refine ⟨1666039788005503371389477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110693192003668914259651 1666039788005503371389477)
                ·
                  refine ⟨312382460251031882135527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666039788005503371389477 312382460251031882135527)
                  ·
                    rfl

theorem cell21_1368816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1368816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368816 prefixEnd_1368816 := by exact prefixLift 1368816
  have htrace : WordTrace (prefixWord ++ tailWord_1368816) baseStart_1368816 baseEnd_1368816 := by
    simpa [prefixWord, tailWord_1368816, baseEnd_1368816] using wordTrace_append hprefix tailTrace_1368816
  have hstable : (prefixWord ++ tailWord_1368816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368816).length < 2 ^ (prefixWord ++ tailWord_1368816).sum := by decide
  have hdescent : baseEnd_1368816 < baseStart_1368816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368965 : List Nat := [1, 3, 1, 1, 3, 4, 8]
def baseStart_1368965 : Nat := 118140960795 + 1368965 * 2 ^ 59
def prefixEnd_1368965 : Nat := 4983230072969 + 3 ^ 40 * 1368965 * 2
def baseEnd_1368965 : Nat := 34712940453448970461321

theorem tailTrace_1368965 : CollatzResearch.WordTrace tailWord_1368965 prefixEnd_1368965 34712940453448970461321 := by
  unfold tailWord_1368965
  simp only [CollatzResearch.WordTrace]
  refine ⟨49930255485481080453292349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33286836990320720302194899 49930255485481080453292349)
  ·
    refine ⟨18723845807055405169984631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49930255485481080453292349 18723845807055405169984631)
    ·
      refine ⟨28085768710583107754976947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18723845807055405169984631 28085768710583107754976947)
      ·
        refine ⟨42128653065874661632465421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28085768710583107754976947 42128653065874661632465421)
        ·
          refine ⟨15798244899702998112174533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42128653065874661632465421 15798244899702998112174533)
          ·
            refine ⟨2962170918694312146032725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15798244899702998112174533 2962170918694312146032725)
            ·
              refine ⟨34712940453448970461321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2962170918694312146032725 34712940453448970461321)
              ·
                rfl

theorem cell21_1368965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 8].length) (baseStart_1368965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368965 prefixEnd_1368965 := by exact prefixLift 1368965
  have htrace : WordTrace (prefixWord ++ tailWord_1368965) baseStart_1368965 baseEnd_1368965 := by
    simpa [prefixWord, tailWord_1368965, baseEnd_1368965] using wordTrace_append hprefix tailTrace_1368965
  have hstable : (prefixWord ++ tailWord_1368965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368965).length < 2 ^ (prefixWord ++ tailWord_1368965).sum := by decide
  have hdescent : baseEnd_1368965 < baseStart_1368965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368968 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_1368968 : Nat := 118140960795 + 1368968 * 2 ^ 59
def prefixEnd_1368968 : Nat := 4983230072969 + 3 ^ 40 * 1368968 * 2
def baseEnd_1368968 : Nat := 312417148721913395601883

theorem tailTrace_1368968 : CollatzResearch.WordTrace tailWord_1368968 prefixEnd_1368968 312417148721913395601883 := by
  unfold tailWord_1368968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24965182452235105982825779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33286909936313474643767705 24965182452235105982825779)
  ·
    refine ⟨37447773678352658974238669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24965182452235105982825779 37447773678352658974238669)
    ·
      refine ⟨14042915129382247115339501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37447773678352658974238669 14042915129382247115339501)
      ·
        refine ⟨5266093173518342668252313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14042915129382247115339501 5266093173518342668252313)
        ·
          refine ⟨3949569880138757001189235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5266093173518342668252313 3949569880138757001189235)
          ·
            refine ⟨5924354820208135501783853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949569880138757001189235 5924354820208135501783853)
            ·
              refine ⟨2221633057578050813168945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5924354820208135501783853 2221633057578050813168945)
              ·
                refine ⟨1666224793183538109876709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221633057578050813168945 1666224793183538109876709)
                ·
                  refine ⟨312417148721913395601883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666224793183538109876709 312417148721913395601883)
                  ·
                    rfl

theorem cell21_1368968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_1368968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368968 prefixEnd_1368968 := by exact prefixLift 1368968
  have htrace : WordTrace (prefixWord ++ tailWord_1368968) baseStart_1368968 baseEnd_1368968 := by
    simpa [prefixWord, tailWord_1368968, baseEnd_1368968] using wordTrace_append hprefix tailTrace_1368968
  have hstable : (prefixWord ++ tailWord_1368968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368968).length < 2 ^ (prefixWord ++ tailWord_1368968).sum := by decide
  have hdescent : baseEnd_1368968 < baseStart_1368968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368996 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1368996 : Nat := 118140960795 + 1368996 * 2 ^ 59
def prefixEnd_1368996 : Nat := 4983230072969 + 3 ^ 40 * 1368996 * 2
def baseEnd_1368996 : Nat := 312423538703391569135159

theorem tailTrace_1368996 : CollatzResearch.WordTrace tailWord_1368996 prefixEnd_1368996 312423538703391569135159 := by
  unfold tailWord_1368996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24965693074184386373835421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33287590765579181831780561 24965693074184386373835421)
  ·
    refine ⟨9362134902819144890188283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24965693074184386373835421 9362134902819144890188283)
    ·
      refine ⟨14043202354228717335282425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362134902819144890188283 14043202354228717335282425)
      ·
        refine ⟨10532401765671538001461819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14043202354228717335282425 10532401765671538001461819)
        ·
          refine ⟨15798602648507307002192729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10532401765671538001461819 15798602648507307002192729)
          ·
            refine ⟨11848951986380480251644547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15798602648507307002192729 11848951986380480251644547)
            ·
              refine ⟨17773427979570720377466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848951986380480251644547 17773427979570720377466821)
              ·
                refine ⟨3332517746169510070775029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17773427979570720377466821 3332517746169510070775029)
                ·
                  refine ⟨312423538703391569135159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332517746169510070775029 312423538703391569135159)
                  ·
                    rfl

theorem cell21_1368996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1368996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1368996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1368996 prefixEnd_1368996 := by exact prefixLift 1368996
  have htrace : WordTrace (prefixWord ++ tailWord_1368996) baseStart_1368996 baseEnd_1368996 := by
    simpa [prefixWord, tailWord_1368996, baseEnd_1368996] using wordTrace_append hprefix tailTrace_1368996
  have hstable : (prefixWord ++ tailWord_1368996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368996).length < 2 ^ (prefixWord ++ tailWord_1368996).sum := by decide
  have hdescent : baseEnd_1368996 < baseStart_1368996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369005 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1369005 : Nat := 118140960795 + 1369005 * 2 ^ 59
def prefixEnd_1369005 : Nat := 4983230072969 + 3 ^ 40 * 1369005 * 2
def baseEnd_1369005 : Nat := 312425592626009553485141

theorem tailTrace_1369005 : CollatzResearch.WordTrace tailWord_1369005 prefixEnd_1369005 312425592626009553485141 := by
  unfold tailWord_1369005
  simp only [CollatzResearch.WordTrace]
  refine ⟨49931714405336167284748469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33287809603557444856498979 49931714405336167284748469)
  ·
    refine ⟨4681098225500265682945169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49931714405336167284748469 4681098225500265682945169)
    ·
      refine ⟨3510823669125199262208877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4681098225500265682945169 3510823669125199262208877)
      ·
        refine ⟨1316558875921949723328329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3510823669125199262208877 1316558875921949723328329)
        ·
          refine ⟨987419156941462292496247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316558875921949723328329 987419156941462292496247)
          ·
            refine ⟨1481128735412193438744371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987419156941462292496247 1481128735412193438744371)
            ·
              refine ⟨2221693103118290158116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481128735412193438744371 2221693103118290158116557)
              ·
                refine ⟨833134913669358809293709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221693103118290158116557 833134913669358809293709)
                ·
                  refine ⟨312425592626009553485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833134913669358809293709 312425592626009553485141)
                  ·
                    rfl

theorem cell21_1369005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1369005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369005 prefixEnd_1369005 := by exact prefixLift 1369005
  have htrace : WordTrace (prefixWord ++ tailWord_1369005) baseStart_1369005 baseEnd_1369005 := by
    simpa [prefixWord, tailWord_1369005, baseEnd_1369005] using wordTrace_append hprefix tailTrace_1369005
  have hstable : (prefixWord ++ tailWord_1369005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369005).length < 2 ^ (prefixWord ++ tailWord_1369005).sum := by decide
  have hdescent : baseEnd_1369005 < baseStart_1369005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369041 : List Nat := [1, 2, 2, 1, 2, 1, 6, 6]
def baseStart_1369041 : Nat := 118140960795 + 1369041 * 2 ^ 59
def prefixEnd_1369041 : Nat := 4983230072969 + 3 ^ 40 * 1369041 * 2
def baseEnd_1369041 : Nat := 104144602772160496961689

theorem tailTrace_1369041 : CollatzResearch.WordTrace tailWord_1369041 prefixEnd_1369041 104144602772160496961689 := by
  unfold tailWord_1369041
  simp only [CollatzResearch.WordTrace]
  refine ⟨49933027433205745433058977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33288684955470496955372651 49933027433205745433058977)
  ·
    refine ⟨37449770574904309074794233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49933027433205745433058977 37449770574904309074794233)
    ·
      refine ⟨28087327931178231806095675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37449770574904309074794233 28087327931178231806095675)
      ·
        refine ⟨42130991896767347709143513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28087327931178231806095675 42130991896767347709143513)
        ·
          refine ⟨31598243922575510781857635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42130991896767347709143513 31598243922575510781857635)
          ·
            refine ⟨47397365883863266172786453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31598243922575510781857635 47397365883863266172786453)
            ·
              refine ⟨2221751525806090601849365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47397365883863266172786453 2221751525806090601849365)
              ·
                refine ⟨104144602772160496961689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2221751525806090601849365 104144602772160496961689)
                ·
                  rfl

theorem cell21_1369041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_1369041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369041 prefixEnd_1369041 := by exact prefixLift 1369041
  have htrace : WordTrace (prefixWord ++ tailWord_1369041) baseStart_1369041 baseEnd_1369041 := by
    simpa [prefixWord, tailWord_1369041, baseEnd_1369041] using wordTrace_append hprefix tailTrace_1369041
  have hstable : (prefixWord ++ tailWord_1369041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369041).length < 2 ^ (prefixWord ++ tailWord_1369041).sum := by decide
  have hdescent : baseEnd_1369041 < baseStart_1369041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369044 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1369044 : Nat := 118140960795 + 1369044 * 2 ^ 59
def prefixEnd_1369044 : Nat := 4983230072969 + 3 ^ 40 * 1369044 * 2
def baseEnd_1369044 : Nat := 312434492957354152335061

theorem tailTrace_1369044 : CollatzResearch.WordTrace tailWord_1369044 prefixEnd_1369044 312434492957354152335061 := by
  unfold tailWord_1369044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24966568426097438472709093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33288757901463251296945457 24966568426097438472709093)
  ·
    refine ⟨4681231579893269713632955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24966568426097438472709093 4681231579893269713632955)
    ·
      refine ⟨7021847369839904570449433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681231579893269713632955 7021847369839904570449433)
      ·
        refine ⟨5266385527379928427837075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7021847369839904570449433 5266385527379928427837075)
        ·
          refine ⟨7899578291069892641755613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266385527379928427837075 7899578291069892641755613)
          ·
            refine ⟨2962341859151209740658355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7899578291069892641755613 2962341859151209740658355)
            ·
              refine ⟨4443512788726814610987533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962341859151209740658355 4443512788726814610987533)
              ·
                refine ⟨1666317295772555479120325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4443512788726814610987533 1666317295772555479120325)
                ·
                  refine ⟨312434492957354152335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666317295772555479120325 312434492957354152335061)
                  ·
                    rfl

theorem cell21_1369044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1369044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369044 prefixEnd_1369044 := by exact prefixLift 1369044
  have htrace : WordTrace (prefixWord ++ tailWord_1369044) baseStart_1369044 baseEnd_1369044 := by
    simpa [prefixWord, tailWord_1369044, baseEnd_1369044] using wordTrace_append hprefix tailTrace_1369044
  have hstable : (prefixWord ++ tailWord_1369044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369044).length < 2 ^ (prefixWord ++ tailWord_1369044).sum := by decide
  have hdescent : baseEnd_1369044 < baseStart_1369044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369131 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_1369131 : Nat := 118140960795 + 1369131 * 2 ^ 59
def prefixEnd_1369131 : Nat := 4983230072969 + 3 ^ 40 * 1369131 * 2
def baseEnd_1369131 : Nat := 312454347542661334384883

theorem tailTrace_1369131 : CollatzResearch.WordTrace tailWord_1369131 prefixEnd_1369131 312454347542661334384883 := by
  unfold tailWord_1369131
  simp only [CollatzResearch.WordTrace]
  refine ⟨49936310002879690803835247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33290873335253127202556831 49936310002879690803835247)
  ·
    refine ⟨74904465004319536205752871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49936310002879690803835247 74904465004319536205752871)
    ·
      refine ⟨112356697506479304308629307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74904465004319536205752871 112356697506479304308629307)
      ·
        refine ⟨168535046259718956462943961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112356697506479304308629307 168535046259718956462943961)
        ·
          refine ⟨126401284694789217347207971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168535046259718956462943961 126401284694789217347207971)
          ·
            refine ⟨189601927042183826020811957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126401284694789217347207971 189601927042183826020811957)
            ·
              refine ⟨17775180660204733689451121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189601927042183826020811957 17775180660204733689451121)
              ·
                refine ⟨13331385495153550267088341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17775180660204733689451121 13331385495153550267088341)
                ·
                  refine ⟨312454347542661334384883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13331385495153550267088341 312454347542661334384883)
                  ·
                    rfl

theorem cell21_1369131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_1369131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369131 prefixEnd_1369131 := by exact prefixLift 1369131
  have htrace : WordTrace (prefixWord ++ tailWord_1369131) baseStart_1369131 baseEnd_1369131 := by
    simpa [prefixWord, tailWord_1369131, baseEnd_1369131] using wordTrace_append hprefix tailTrace_1369131
  have hstable : (prefixWord ++ tailWord_1369131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369131).length < 2 ^ (prefixWord ++ tailWord_1369131).sum := by decide
  have hdescent : baseEnd_1369131 < baseStart_1369131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369148 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_1369148 : Nat := 118140960795 + 1369148 * 2 ^ 59
def prefixEnd_1369148 : Nat := 4983230072969 + 3 ^ 40 * 1369148 * 2
def baseEnd_1369148 : Nat := 312458227174273082601515

theorem tailTrace_1369148 : CollatzResearch.WordTrace tailWord_1369148 prefixEnd_1369148 312458227174273082601515 := by
  unfold tailWord_1369148
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968465021909051353602049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33291286695878735138136065 24968465021909051353602049)
  ·
    refine ⟨18726348766431788515201537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24968465021909051353602049 18726348766431788515201537)
    ·
      refine ⟨14044761574823841386401153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18726348766431788515201537 14044761574823841386401153)
      ·
        refine ⟨10533571181117881039800865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14044761574823841386401153 10533571181117881039800865)
        ·
          refine ⟨7900178385838410779850649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10533571181117881039800865 7900178385838410779850649)
          ·
            refine ⟨5925133789378808084887987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7900178385838410779850649 5925133789378808084887987)
            ·
              refine ⟨8887700684068212127331981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925133789378808084887987 8887700684068212127331981)
              ·
                refine ⟨3332887756525579547749493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8887700684068212127331981 3332887756525579547749493)
                ·
                  refine ⟨312458227174273082601515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332887756525579547749493 312458227174273082601515)
                  ·
                    rfl

theorem cell21_1369148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_1369148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369148 prefixEnd_1369148 := by exact prefixLift 1369148
  have htrace : WordTrace (prefixWord ++ tailWord_1369148) baseStart_1369148 baseEnd_1369148 := by
    simpa [prefixWord, tailWord_1369148, baseEnd_1369148] using wordTrace_append hprefix tailTrace_1369148
  have hstable : (prefixWord ++ tailWord_1369148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369148).length < 2 ^ (prefixWord ++ tailWord_1369148).sum := by decide
  have hdescent : baseEnd_1369148 < baseStart_1369148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369165 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1369165 : Nat := 118140960795 + 1369165 * 2 ^ 59
def prefixEnd_1369165 : Nat := 4983230072969 + 3 ^ 40 * 1369165 * 2
def baseEnd_1369165 : Nat := 312462106805884830818147

theorem tailTrace_1369165 : CollatzResearch.WordTrace tailWord_1369165 prefixEnd_1369165 312462106805884830818147 := by
  unfold tailWord_1369165
  simp only [CollatzResearch.WordTrace]
  refine ⟨49937550084756514610572949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33291700056504343073715299 49937550084756514610572949)
  ·
    refine ⟨2340822660222961622370607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49937550084756514610572949 2340822660222961622370607)
    ·
      refine ⟨3511233990334442433555911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340822660222961622370607 3511233990334442433555911)
      ·
        refine ⟨5266850985501663650333867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511233990334442433555911 5266850985501663650333867)
        ·
          refine ⟨7900276478252495475500801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266850985501663650333867 7900276478252495475500801)
          ·
            refine ⟨5925207358689371606625601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7900276478252495475500801 5925207358689371606625601)
            ·
              refine ⟨4443905519017028704969201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925207358689371606625601 4443905519017028704969201)
              ·
                refine ⟨3332929139262771528726901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4443905519017028704969201 3332929139262771528726901)
                ·
                  refine ⟨312462106805884830818147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332929139262771528726901 312462106805884830818147)
                  ·
                    rfl

theorem cell21_1369165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1369165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369165 prefixEnd_1369165 := by exact prefixLift 1369165
  have htrace : WordTrace (prefixWord ++ tailWord_1369165) baseStart_1369165 baseEnd_1369165 := by
    simpa [prefixWord, tailWord_1369165, baseEnd_1369165] using wordTrace_append hprefix tailTrace_1369165
  have hstable : (prefixWord ++ tailWord_1369165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369165).length < 2 ^ (prefixWord ++ tailWord_1369165).sum := by decide
  have hdescent : baseEnd_1369165 < baseStart_1369165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369193 : List Nat := [1, 2, 1, 1, 1, 8, 7]
def baseStart_1369193 : Nat := 118140960795 + 1369193 * 2 ^ 59
def prefixEnd_1369193 : Nat := 4983230072969 + 3 ^ 40 * 1369193 * 2
def baseEnd_1369193 : Nat := 34718721865262556039047

theorem tailTrace_1369193 : CollatzResearch.WordTrace tailWord_1369193 prefixEnd_1369193 34718721865262556039047 := by
  unfold tailWord_1369193
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938571328655075392592233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33292380885770050261728155 49938571328655075392592233)
  ·
    refine ⟨37453928496491306544444175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49938571328655075392592233 37453928496491306544444175)
    ·
      refine ⟨56180892744736959816666263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37453928496491306544444175 56180892744736959816666263)
      ·
        refine ⟨84271339117105439724999395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56180892744736959816666263 84271339117105439724999395)
        ·
          refine ⟨126407008675658159587499093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84271339117105439724999395 126407008675658159587499093)
          ·
            refine ⟨1481332132917869057666005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 126407008675658159587499093 1481332132917869057666005)
            ·
              refine ⟨34718721865262556039047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1481332132917869057666005 34718721865262556039047)
              ·
                rfl

theorem cell21_1369193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 7].length) (baseStart_1369193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369193 prefixEnd_1369193 := by exact prefixLift 1369193
  have htrace : WordTrace (prefixWord ++ tailWord_1369193) baseStart_1369193 baseEnd_1369193 := by
    simpa [prefixWord, tailWord_1369193, baseEnd_1369193] using wordTrace_append hprefix tailTrace_1369193
  have hstable : (prefixWord ++ tailWord_1369193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369193).length < 2 ^ (prefixWord ++ tailWord_1369193).sum := by decide
  have hdescent : baseEnd_1369193 < baseStart_1369193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369317 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1369317 : Nat := 118140960795 + 1369317 * 2 ^ 59
def prefixEnd_1369317 : Nat := 4983230072969 + 3 ^ 40 * 1369317 * 2
def baseEnd_1369317 : Nat := 312496795276766344284503

theorem tailTrace_1369317 : CollatzResearch.WordTrace tailWord_1369317 prefixEnd_1369317 312496795276766344284503 := by
  unfold tailWord_1369317
  simp only [CollatzResearch.WordTrace]
  refine ⟨49943093980205844570106205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33295395986803896380070803 49943093980205844570106205)
  ·
    refine ⟨18728660242577191713789827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49943093980205844570106205 18728660242577191713789827)
    ·
      refine ⟨28092990363865787570684741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18728660242577191713789827 28092990363865787570684741)
      ·
        refine ⟨5267435693224835169503389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28092990363865787570684741 5267435693224835169503389)
        ·
          refine ⟨1975288384959313188563771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5267435693224835169503389 1975288384959313188563771)
          ·
            refine ⟨2962932577438969782845657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975288384959313188563771 2962932577438969782845657)
            ·
              refine ⟨2222199433079227337134243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962932577438969782845657 2222199433079227337134243)
              ·
                refine ⟨3333299149618841005701365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222199433079227337134243 3333299149618841005701365)
                ·
                  refine ⟨312496795276766344284503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333299149618841005701365 312496795276766344284503)
                  ·
                    rfl

theorem cell21_1369317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1369317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369317 prefixEnd_1369317 := by exact prefixLift 1369317
  have htrace : WordTrace (prefixWord ++ tailWord_1369317) baseStart_1369317 baseEnd_1369317 := by
    simpa [prefixWord, tailWord_1369317, baseEnd_1369317] using wordTrace_append hprefix tailTrace_1369317
  have hstable : (prefixWord ++ tailWord_1369317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369317).length < 2 ^ (prefixWord ++ tailWord_1369317).sum := by decide
  have hdescent : baseEnd_1369317 < baseStart_1369317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369345 : List Nat := [1, 2, 4, 1, 1, 4, 1, 7]
def baseStart_1369345 : Nat := 118140960795 + 1369345 * 2 ^ 59
def prefixEnd_1369345 : Nat := 4983230072969 + 3 ^ 40 * 1369345 * 2
def baseEnd_1369345 : Nat := 104167728419414839272593

theorem tailTrace_1369345 : CollatzResearch.WordTrace tailWord_1369345 prefixEnd_1369345 104167728419414839272593 := by
  unfold tailWord_1369345
  simp only [CollatzResearch.WordTrace]
  refine ⟨49944115224104405352125489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33296076816069603568083659 49944115224104405352125489)
  ·
    refine ⟨37458086418078304014094117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49944115224104405352125489 37458086418078304014094117)
    ·
      refine ⟨7023391203389682002642647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37458086418078304014094117 7023391203389682002642647)
      ·
        refine ⟨10535086805084523003963971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7023391203389682002642647 10535086805084523003963971)
        ·
          refine ⟨15802630207626784505945957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10535086805084523003963971 15802630207626784505945957)
          ·
            refine ⟨2962993163930022094864867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15802630207626784505945957 2962993163930022094864867)
            ·
              refine ⟨4444489745895033142297301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962993163930022094864867 4444489745895033142297301)
              ·
                refine ⟨104167728419414839272593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4444489745895033142297301 104167728419414839272593)
                ·
                  rfl

theorem cell21_1369345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_1369345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369345 prefixEnd_1369345 := by exact prefixLift 1369345
  have htrace : WordTrace (prefixWord ++ tailWord_1369345) baseStart_1369345 baseEnd_1369345 := by
    simpa [prefixWord, tailWord_1369345, baseEnd_1369345] using wordTrace_append hprefix tailTrace_1369345
  have hstable : (prefixWord ++ tailWord_1369345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369345).length < 2 ^ (prefixWord ++ tailWord_1369345).sum := by decide
  have hdescent : baseEnd_1369345 < baseStart_1369345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369430 : List Nat := [5, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1369430 : Nat := 118140960795 + 1369430 * 2 ^ 59
def prefixEnd_1369430 : Nat := 4983230072969 + 3 ^ 40 * 1369430 * 2
def baseEnd_1369430 : Nat := 104174194472101086300313

theorem tailTrace_1369430 : CollatzResearch.WordTrace tailWord_1369430 prefixEnd_1369430 104174194472101086300313 := by
  unfold tailWord_1369430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121700964299779054310609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33298143619197643245979829 3121700964299779054310609)
  ·
    refine ⟨2341275723224834290732957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3121700964299779054310609 2341275723224834290732957)
    ·
      refine ⟨877978396209312859024859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2341275723224834290732957 877978396209312859024859)
      ·
        refine ⟨1316967594313969288537289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877978396209312859024859 1316967594313969288537289)
        ·
          refine ⟨987725695735476966402967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316967594313969288537289 987725695735476966402967)
          ·
            refine ⟨1481588543603215449604451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987725695735476966402967 1481588543603215449604451)
            ·
              refine ⟨2222382815404823174406677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481588543603215449604451 2222382815404823174406677)
              ·
                refine ⟨104174194472101086300313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2222382815404823174406677 104174194472101086300313)
                ·
                  rfl

theorem cell21_1369430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1369430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369430 prefixEnd_1369430 := by exact prefixLift 1369430
  have htrace : WordTrace (prefixWord ++ tailWord_1369430) baseStart_1369430 baseEnd_1369430 := by
    simpa [prefixWord, tailWord_1369430, baseEnd_1369430] using wordTrace_append hprefix tailTrace_1369430
  have hstable : (prefixWord ++ tailWord_1369430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369430).length < 2 ^ (prefixWord ++ tailWord_1369430).sum := by decide
  have hdescent : baseEnd_1369430 < baseStart_1369430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369452 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1369452 : Nat := 118140960795 + 1369452 * 2 ^ 59
def prefixEnd_1369452 : Nat := 4983230072969 + 3 ^ 40 * 1369452 * 2
def baseEnd_1369452 : Nat := 312527604116036109534227

theorem tailTrace_1369452 : CollatzResearch.WordTrace tailWord_1369452 prefixEnd_1369452 312527604116036109534227 := by
  unfold tailWord_1369452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24974008917358381313135305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33298678556477841750847073 24974008917358381313135305)
  ·
    refine ⟨18730506688018785984851479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24974008917358381313135305 18730506688018785984851479)
    ·
      refine ⟨28095760032028178977277219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18730506688018785984851479 28095760032028178977277219)
      ·
        refine ⟨42143640048042268465915829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28095760032028178977277219 42143640048042268465915829)
        ·
          refine ⟨3950966254503962668679609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42143640048042268465915829 3950966254503962668679609)
          ·
            refine ⟨2963224690877972001509707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950966254503962668679609 2963224690877972001509707)
            ·
              refine ⟨4444837036316958002264561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963224690877972001509707 4444837036316958002264561)
              ·
                refine ⟨3333627777237718501698421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4444837036316958002264561 3333627777237718501698421)
                ·
                  refine ⟨312527604116036109534227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333627777237718501698421 312527604116036109534227)
                  ·
                    rfl

theorem cell21_1369452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1369452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369452 prefixEnd_1369452 := by exact prefixLift 1369452
  have htrace : WordTrace (prefixWord ++ tailWord_1369452) baseStart_1369452 baseEnd_1369452 := by
    simpa [prefixWord, tailWord_1369452, baseEnd_1369452] using wordTrace_append hprefix tailTrace_1369452
  have hstable : (prefixWord ++ tailWord_1369452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369452).length < 2 ^ (prefixWord ++ tailWord_1369452).sum := by decide
  have hdescent : baseEnd_1369452 < baseStart_1369452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369469 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1369469 : Nat := 118140960795 + 1369469 * 2 ^ 59
def prefixEnd_1369469 : Nat := 4983230072969 + 3 ^ 40 * 1369469 * 2
def baseEnd_1369469 : Nat := 312531483747647857750859

theorem tailTrace_1369469 : CollatzResearch.WordTrace tailWord_1369469 prefixEnd_1369469 312531483747647857750859 := by
  unfold tailWord_1369469
  simp only [CollatzResearch.WordTrace]
  refine ⟨49948637875655174529639461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33299091917103449686426307 49948637875655174529639461)
  ·
    refine ⟨9365369601685345224307399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49948637875655174529639461 9365369601685345224307399)
    ·
      refine ⟨14048054402528017836461099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9365369601685345224307399 14048054402528017836461099)
      ·
        refine ⟨21072081603792026754691649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048054402528017836461099 21072081603792026754691649)
        ·
          refine ⟨15804061202844020066018737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21072081603792026754691649 15804061202844020066018737)
          ·
            refine ⟨11853045902133015049514053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15804061202844020066018737 11853045902133015049514053)
            ·
              refine ⟨2222446106649940321783885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11853045902133015049514053 2222446106649940321783885)
              ·
                refine ⟨833417289993727620668957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222446106649940321783885 833417289993727620668957)
                ·
                  refine ⟨312531483747647857750859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833417289993727620668957 312531483747647857750859)
                  ·
                    rfl

theorem cell21_1369469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1369469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369469 prefixEnd_1369469 := by exact prefixLift 1369469
  have htrace : WordTrace (prefixWord ++ tailWord_1369469) baseStart_1369469 baseEnd_1369469 := by
    simpa [prefixWord, tailWord_1369469, baseEnd_1369469] using wordTrace_append hprefix tailTrace_1369469
  have hstable : (prefixWord ++ tailWord_1369469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369469).length < 2 ^ (prefixWord ++ tailWord_1369469).sum := by decide
  have hdescent : baseEnd_1369469 < baseStart_1369469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369573 : List Nat := [1, 3, 1, 5, 1, 1, 2, 7]
def baseStart_1369573 : Nat := 118140960795 + 1369573 * 2 ^ 59
def prefixEnd_1369573 : Nat := 4983230072969 + 3 ^ 40 * 1369573 * 2
def baseEnd_1369573 : Nat := 104185072654855596005771

theorem tailTrace_1369573 : CollatzResearch.WordTrace tailWord_1369573 prefixEnd_1369573 104185072654855596005771 := by
  unfold tailWord_1369573
  simp only [CollatzResearch.WordTrace]
  refine ⟨49952431067278400291425373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33301620711518933527616915 49952431067278400291425373)
  ·
    refine ⟨18732161650229400109284515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49952431067278400291425373 18732161650229400109284515)
    ·
      refine ⟨28098242475344100163926773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18732161650229400109284515 28098242475344100163926773)
      ·
        refine ⟨2634210232063509390368135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28098242475344100163926773 2634210232063509390368135)
        ·
          refine ⟨3951315348095264085552203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634210232063509390368135 3951315348095264085552203)
          ·
            refine ⟨5926973022142896128328305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951315348095264085552203 5926973022142896128328305)
            ·
              refine ⟨4445229766607172096246229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926973022142896128328305 4445229766607172096246229)
              ·
                refine ⟨104185072654855596005771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4445229766607172096246229 104185072654855596005771)
                ·
                  rfl

theorem cell21_1369573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_1369573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369573 prefixEnd_1369573 := by exact prefixLift 1369573
  have htrace : WordTrace (prefixWord ++ tailWord_1369573) baseStart_1369573 baseEnd_1369573 := by
    simpa [prefixWord, tailWord_1369573, baseEnd_1369573] using wordTrace_append hprefix tailTrace_1369573
  have hstable : (prefixWord ++ tailWord_1369573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369573).length < 2 ^ (prefixWord ++ tailWord_1369573).sum := by decide
  have hdescent : baseEnd_1369573 < baseStart_1369573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369663 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_1369663 : Nat := 118140960795 + 1369663 * 2 ^ 59
def prefixEnd_1369663 : Nat := 4983230072969 + 3 ^ 40 * 1369663 * 2
def baseEnd_1369663 : Nat := 312575757190746631517129

theorem tailTrace_1369663 : CollatzResearch.WordTrace tailWord_1369663 prefixEnd_1369663 312575757190746631517129 := by
  unfold tailWord_1369663
  simp only [CollatzResearch.WordTrace]
  refine ⟨49955713636952345662201643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33303809091301563774801095 49955713636952345662201643)
  ·
    refine ⟨74933570455428518493302465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49955713636952345662201643 74933570455428518493302465)
    ·
      refine ⟨56200177841571388869976849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74933570455428518493302465 56200177841571388869976849)
      ·
        refine ⟨42150133381178541652482637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56200177841571388869976849 42150133381178541652482637)
        ·
          refine ⟨15806300017941953119680989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42150133381178541652482637 15806300017941953119680989)
          ·
            refine ⟨5927362506728232419880371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15806300017941953119680989 5927362506728232419880371)
            ·
              refine ⟨8891043760092348629820557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5927362506728232419880371 8891043760092348629820557)
              ·
                refine ⟨3334141410034630736182709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8891043760092348629820557 3334141410034630736182709)
                ·
                  refine ⟨312575757190746631517129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334141410034630736182709 312575757190746631517129)
                  ·
                    rfl

theorem cell21_1369663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_1369663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369663 prefixEnd_1369663 := by exact prefixLift 1369663
  have htrace : WordTrace (prefixWord ++ tailWord_1369663) baseStart_1369663 baseEnd_1369663 := by
    simpa [prefixWord, tailWord_1369663, baseEnd_1369663] using wordTrace_append hprefix tailTrace_1369663
  have hstable : (prefixWord ++ tailWord_1369663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369663).length < 2 ^ (prefixWord ++ tailWord_1369663).sum := by decide
  have hdescent : baseEnd_1369663 < baseStart_1369663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369714 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1369714 : Nat := 118140960795 + 1369714 * 2 ^ 59
def prefixEnd_1369714 : Nat := 4983230072969 + 3 ^ 40 * 1369714 * 2
def baseEnd_1369714 : Nat := 312587396085581876167025

theorem tailTrace_1369714 : CollatzResearch.WordTrace tailWord_1369714 prefixEnd_1369714 312587396085581876167025 := by
  unfold tailWord_1369714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489393439941895343077049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33305049173178387581538797 12489393439941895343077049)
  ·
    refine ⟨9367045079956421507307787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12489393439941895343077049 9367045079956421507307787)
    ·
      refine ⟨14050567619934632260961681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9367045079956421507307787 14050567619934632260961681)
      ·
        refine ⟨10537925714950974195721261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14050567619934632260961681 10537925714950974195721261)
        ·
          refine ⟨3951722143106615323395473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10537925714950974195721261 3951722143106615323395473)
          ·
            refine ⟨2963791607329961492546605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951722143106615323395473 2963791607329961492546605)
            ·
              refine ⟨1111421852748735559704977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2963791607329961492546605 1111421852748735559704977)
              ·
                refine ⟨833566389561551669778733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111421852748735559704977 833566389561551669778733)
                ·
                  refine ⟨312587396085581876167025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833566389561551669778733 312587396085581876167025)
                  ·
                    rfl

theorem cell21_1369714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1369714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369714 prefixEnd_1369714 := by exact prefixLift 1369714
  have htrace : WordTrace (prefixWord ++ tailWord_1369714) baseStart_1369714 baseEnd_1369714 := by
    simpa [prefixWord, tailWord_1369714, baseEnd_1369714] using wordTrace_append hprefix tailTrace_1369714
  have hstable : (prefixWord ++ tailWord_1369714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369714).length < 2 ^ (prefixWord ++ tailWord_1369714).sum := by decide
  have hdescent : baseEnd_1369714 < baseStart_1369714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369725 : List Nat := [1, 4, 1, 1, 4, 2, 2, 6]
def baseStart_1369725 : Nat := 118140960795 + 1369725 * 2 ^ 59
def prefixEnd_1369725 : Nat := 4983230072969 + 3 ^ 40 * 1369725 * 2
def baseEnd_1369725 : Nat := 104196635478482767161223

theorem tailTrace_1369725 : CollatzResearch.WordTrace tailWord_1369725 prefixEnd_1369725 104196635478482767161223 := by
  unfold tailWord_1369725
  simp only [CollatzResearch.WordTrace]
  refine ⟨49957974962727730250958629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33305316641818486833972419 49957974962727730250958629)
  ·
    refine ⟨9367120305511449422054743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49957974962727730250958629 9367120305511449422054743)
    ·
      refine ⟨14050680458267174133082115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9367120305511449422054743 14050680458267174133082115)
      ·
        refine ⟨21076020687400761199623173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14050680458267174133082115 21076020687400761199623173)
        ·
          refine ⟨3951753878887642724929345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21076020687400761199623173 3951753878887642724929345)
          ·
            refine ⟨2963815409165732043697009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951753878887642724929345 2963815409165732043697009)
            ·
              refine ⟨2222861556874299032772757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963815409165732043697009 2222861556874299032772757)
              ·
                refine ⟨104196635478482767161223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2222861556874299032772757 104196635478482767161223)
                ·
                  rfl

theorem cell21_1369725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_1369725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369725 prefixEnd_1369725 := by exact prefixLift 1369725
  have htrace : WordTrace (prefixWord ++ tailWord_1369725) baseStart_1369725 baseEnd_1369725 := by
    simpa [prefixWord, tailWord_1369725, baseEnd_1369725] using wordTrace_append hprefix tailTrace_1369725
  have hstable : (prefixWord ++ tailWord_1369725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369725).length < 2 ^ (prefixWord ++ tailWord_1369725).sum := by decide
  have hdescent : baseEnd_1369725 < baseStart_1369725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369753 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_1369753 : Nat := 118140960795 + 1369753 * 2 ^ 59
def prefixEnd_1369753 : Nat := 4983230072969 + 3 ^ 40 * 1369753 * 2
def baseEnd_1369753 : Nat := 312596296416926475016945

theorem tailTrace_1369753 : CollatzResearch.WordTrace tailWord_1369753 prefixEnd_1369753 312596296416926475016945 := by
  unfold tailWord_1369753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49958996206626291032977913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33305997471084194021985275 49958996206626291032977913)
  ·
    refine ⟨37469247154969718274733435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49958996206626291032977913 37469247154969718274733435)
    ·
      refine ⟨56203870732454577412100153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37469247154969718274733435 56203870732454577412100153)
      ·
        refine ⟨42152903049340933059075115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56203870732454577412100153 42152903049340933059075115)
        ·
          refine ⟨63229354574011399588612673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42152903049340933059075115 63229354574011399588612673)
          ·
            refine ⟨47422015930508549691459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63229354574011399588612673 47422015930508549691459505)
            ·
              refine ⟨35566511947881412268594629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47422015930508549691459505 35566511947881412268594629)
              ·
                refine ⟨6668720990227764800361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35566511947881412268594629 6668720990227764800361493)
                ·
                  refine ⟨312596296416926475016945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6668720990227764800361493 312596296416926475016945)
                  ·
                    rfl

theorem cell21_1369753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_1369753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369753 prefixEnd_1369753 := by exact prefixLift 1369753
  have htrace : WordTrace (prefixWord ++ tailWord_1369753) baseStart_1369753 baseEnd_1369753 := by
    simpa [prefixWord, tailWord_1369753, baseEnd_1369753] using wordTrace_append hprefix tailTrace_1369753
  have hstable : (prefixWord ++ tailWord_1369753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369753).length < 2 ^ (prefixWord ++ tailWord_1369753).sum := by decide
  have hdescent : baseEnd_1369753 < baseStart_1369753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369773 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1369773 : Nat := 118140960795 + 1369773 * 2 ^ 59
def prefixEnd_1369773 : Nat := 4983230072969 + 3 ^ 40 * 1369773 * 2
def baseEnd_1369773 : Nat := 312600860689410884683571

theorem tailTrace_1369773 : CollatzResearch.WordTrace tailWord_1369773 prefixEnd_1369773 312600860689410884683571 := by
  unfold tailWord_1369773
  simp only [CollatzResearch.WordTrace]
  refine ⟨49959725666553834448705973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33306483777702556299137315 49959725666553834448705973)
  ·
    refine ⟨4683724281239421979566185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49959725666553834448705973 4683724281239421979566185)
    ·
      refine ⟨3512793210929566484674639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4683724281239421979566185 3512793210929566484674639)
      ·
        refine ⟨5269189816394349727011959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512793210929566484674639 5269189816394349727011959)
        ·
          refine ⟨7903784724591524590517939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269189816394349727011959 7903784724591524590517939)
          ·
            refine ⟨11855677086887286885776909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903784724591524590517939 11855677086887286885776909)
            ·
              refine ⟨4445878907582732582166341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11855677086887286885776909 4445878907582732582166341)
              ·
                refine ⟨833602295171762359156189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4445878907582732582166341 833602295171762359156189)
                ·
                  refine ⟨312600860689410884683571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833602295171762359156189 312600860689410884683571)
                  ·
                    rfl

theorem cell21_1369773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1369773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369773 prefixEnd_1369773 := by exact prefixLift 1369773
  have htrace : WordTrace (prefixWord ++ tailWord_1369773) baseStart_1369773 baseEnd_1369773 := by
    simpa [prefixWord, tailWord_1369773, baseEnd_1369773] using wordTrace_append hprefix tailTrace_1369773
  have hstable : (prefixWord ++ tailWord_1369773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369773).length < 2 ^ (prefixWord ++ tailWord_1369773).sum := by decide
  have hdescent : baseEnd_1369773 < baseStart_1369773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369821 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1369821 : Nat := 118140960795 + 1369821 * 2 ^ 59
def prefixEnd_1369821 : Nat := 4983230072969 + 3 ^ 40 * 1369821 * 2
def baseEnd_1369821 : Nat := 312611814943373467883473

theorem tailTrace_1369821 : CollatzResearch.WordTrace tailWord_1369821 prefixEnd_1369821 312611814943373467883473 := by
  unfold tailWord_1369821
  simp only [CollatzResearch.WordTrace]
  refine ⟨49961476370379938646453317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33307650913586625764302211 49961476370379938646453317)
  ·
    refine ⟨9367776819446238496209997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49961476370379938646453317 9367776819446238496209997)
    ·
      refine ⟨3512916307292339436078749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9367776819446238496209997 3512916307292339436078749)
      ·
        refine ⟨1317343615234627288529531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3512916307292339436078749 1317343615234627288529531)
        ·
          refine ⟨1976015422851940932794297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317343615234627288529531 1976015422851940932794297)
          ·
            refine ⟨1482011567138955699595723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976015422851940932794297 1482011567138955699595723)
            ·
              refine ⟨2223017350708433549393585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482011567138955699595723 2223017350708433549393585)
              ·
                refine ⟨1667263013031325162045189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223017350708433549393585 1667263013031325162045189)
                ·
                  refine ⟨312611814943373467883473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667263013031325162045189 312611814943373467883473)
                  ·
                    rfl

theorem cell21_1369821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1369821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369821 prefixEnd_1369821 := by exact prefixLift 1369821
  have htrace : WordTrace (prefixWord ++ tailWord_1369821) baseStart_1369821 baseEnd_1369821 := by
    simpa [prefixWord, tailWord_1369821, baseEnd_1369821] using wordTrace_append hprefix tailTrace_1369821
  have hstable : (prefixWord ++ tailWord_1369821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369821).length < 2 ^ (prefixWord ++ tailWord_1369821).sum := by decide
  have hdescent : baseEnd_1369821 < baseStart_1369821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369832 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_1369832 : Nat := 118140960795 + 1369832 * 2 ^ 59
def prefixEnd_1369832 : Nat := 4983230072969 + 3 ^ 40 * 1369832 * 2
def baseEnd_1369832 : Nat := 312614325293239893200117

theorem tailTrace_1369832 : CollatzResearch.WordTrace tailWord_1369832 prefixEnd_1369832 312614325293239893200117 := by
  unfold tailWord_1369832
  simp only [CollatzResearch.WordTrace]
  refine ⟨24980938786670043762551875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33307918382226725016735833 24980938786670043762551875)
  ·
    refine ⟨37471408180005065643827813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24980938786670043762551875 37471408180005065643827813)
    ·
      refine ⟨7025889033750949808217715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37471408180005065643827813 7025889033750949808217715)
      ·
        refine ⟨10538833550626424712326573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025889033750949808217715 10538833550626424712326573)
        ·
          refine ⟨3952062581484909267122465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10538833550626424712326573 3952062581484909267122465)
          ·
            refine ⟨2964046936113681950341849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952062581484909267122465 2964046936113681950341849)
            ·
              refine ⟨2223035202085261462756387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964046936113681950341849 2223035202085261462756387)
              ·
                refine ⟨3334552803127892194134581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223035202085261462756387 3334552803127892194134581)
                ·
                  refine ⟨312614325293239893200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334552803127892194134581 312614325293239893200117)
                  ·
                    rfl

theorem cell21_1369832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_1369832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369832 prefixEnd_1369832 := by exact prefixLift 1369832
  have htrace : WordTrace (prefixWord ++ tailWord_1369832) baseStart_1369832 baseEnd_1369832 := by
    simpa [prefixWord, tailWord_1369832, baseEnd_1369832] using wordTrace_append hprefix tailTrace_1369832
  have hstable : (prefixWord ++ tailWord_1369832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369832).length < 2 ^ (prefixWord ++ tailWord_1369832).sum := by decide
  have hdescent : baseEnd_1369832 < baseStart_1369832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369869 : List Nat := [1, 7, 2, 1, 2, 1, 7]
def baseStart_1369869 : Nat := 118140960795 + 1369869 * 2 ^ 59
def prefixEnd_1369869 : Nat := 4983230072969 + 3 ^ 40 * 1369869 * 2
def baseEnd_1369869 : Nat := 34735863244148450120375

theorem tailTrace_1369869 : CollatzResearch.WordTrace tailWord_1369869 prefixEnd_1369869 34735863244148450120375 := by
  unfold tailWord_1369869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49963227074206042844200661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33308818049470695229467107 49963227074206042844200661)
  ·
    refine ⟨1171013134551704129160953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49963227074206042844200661 1171013134551704129160953)
    ·
      refine ⟨878259850913778096870715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1171013134551704129160953 878259850913778096870715)
      ·
        refine ⟨1317389776370667145306073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878259850913778096870715 1317389776370667145306073)
        ·
          refine ⟨988042332278000358979555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1317389776370667145306073 988042332278000358979555)
          ·
            refine ⟨1482063498417000538469333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988042332278000358979555 1482063498417000538469333)
            ·
              refine ⟨34735863244148450120375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1482063498417000538469333 34735863244148450120375)
              ·
                rfl

theorem cell21_1369869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 7].length) (baseStart_1369869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369869 prefixEnd_1369869 := by exact prefixLift 1369869
  have htrace : WordTrace (prefixWord ++ tailWord_1369869) baseStart_1369869 baseEnd_1369869 := by
    simpa [prefixWord, tailWord_1369869, baseEnd_1369869] using wordTrace_append hprefix tailTrace_1369869
  have hstable : (prefixWord ++ tailWord_1369869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369869).length < 2 ^ (prefixWord ++ tailWord_1369869).sum := by decide
  have hdescent : baseEnd_1369869 < baseStart_1369869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369891 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_1369891 : Nat := 118140960795 + 1369891 * 2 ^ 59
def prefixEnd_1369891 : Nat := 4983230072969 + 3 ^ 40 * 1369891 * 2
def baseEnd_1369891 : Nat := 312627789897068901716663

theorem tailTrace_1369891 : CollatzResearch.WordTrace tailWord_1369891 prefixEnd_1369891 312627789897068901716663 := by
  unfold tailWord_1369891
  simp only [CollatzResearch.WordTrace]
  refine ⟨49964029480126340601501527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33309352986750893734334351 49964029480126340601501527)
  ·
    refine ⟨74946044220189510902252291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49964029480126340601501527 74946044220189510902252291)
    ·
      refine ⟨112419066330284266353378437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74946044220189510902252291 112419066330284266353378437)
      ·
        refine ⟨21078574936928299941258457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112419066330284266353378437 21078574936928299941258457)
        ·
          refine ⟨15808931202696224955943843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21078574936928299941258457 15808931202696224955943843)
          ·
            refine ⟨23713396804044337433915765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808931202696224955943843 23713396804044337433915765)
            ·
              refine ⟨2223130950379156634429603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23713396804044337433915765 2223130950379156634429603)
              ·
                refine ⟨3334696425568734951644405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223130950379156634429603 3334696425568734951644405)
                ·
                  refine ⟨312627789897068901716663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334696425568734951644405 312627789897068901716663)
                  ·
                    rfl

theorem cell21_1369891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_1369891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369891 prefixEnd_1369891 := by exact prefixLift 1369891
  have htrace : WordTrace (prefixWord ++ tailWord_1369891) baseStart_1369891 baseEnd_1369891 := by
    simpa [prefixWord, tailWord_1369891, baseEnd_1369891] using wordTrace_append hprefix tailTrace_1369891
  have hstable : (prefixWord ++ tailWord_1369891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369891).length < 2 ^ (prefixWord ++ tailWord_1369891).sum := by decide
  have hdescent : baseEnd_1369891 < baseStart_1369891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369981 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1369981 : Nat := 118140960795 + 1369981 * 2 ^ 59
def prefixEnd_1369981 : Nat := 4983230072969 + 3 ^ 40 * 1369981 * 2
def baseEnd_1369981 : Nat := 312648329123248745216479

theorem tailTrace_1369981 : CollatzResearch.WordTrace tailWord_1369981 prefixEnd_1369981 312648329123248745216479 := by
  unfold tailWord_1369981
  simp only [CollatzResearch.WordTrace]
  refine ⟨49967312049800285972277797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33311541366533523981518531 49967312049800285972277797)
  ·
    refine ⟨9368871009337553619802087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49967312049800285972277797 9368871009337553619802087)
    ·
      refine ⟨14053306514006330429703131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9368871009337553619802087 14053306514006330429703131)
      ·
        refine ⟨21079959771009495644554697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14053306514006330429703131 21079959771009495644554697)
        ·
          refine ⟨15809969828257121733416023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21079959771009495644554697 15809969828257121733416023)
          ·
            refine ⟨23714954742385682600124035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15809969828257121733416023 23714954742385682600124035)
            ·
              refine ⟨35572432113578523900186053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23714954742385682600124035 35572432113578523900186053)
              ·
                refine ⟨6669831021295973231284885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35572432113578523900186053 6669831021295973231284885)
                ·
                  refine ⟨312648329123248745216479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6669831021295973231284885 312648329123248745216479)
                  ·
                    rfl

theorem cell21_1369981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1369981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369981 prefixEnd_1369981 := by exact prefixLift 1369981
  have htrace : WordTrace (prefixWord ++ tailWord_1369981) baseStart_1369981 baseEnd_1369981 := by
    simpa [prefixWord, tailWord_1369981, baseEnd_1369981] using wordTrace_append hprefix tailTrace_1369981
  have hstable : (prefixWord ++ tailWord_1369981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369981).length < 2 ^ (prefixWord ++ tailWord_1369981).sum := by decide
  have hdescent : baseEnd_1369981 < baseStart_1369981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369984 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_1369984 : Nat := 118140960795 + 1369984 * 2 ^ 59
def prefixEnd_1369984 : Nat := 4983230072969 + 3 ^ 40 * 1369984 * 2
def baseEnd_1369984 : Nat := 312649013764121406666473

theorem tailTrace_1369984 : CollatzResearch.WordTrace tailWord_1369984 prefixEnd_1369984 312649013764121406666473 := by
  unfold tailWord_1369984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24983710734394708742318503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33311614312526278323091337 24983710734394708742318503)
  ·
    refine ⟨37475566101592063113477755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24983710734394708742318503 37475566101592063113477755)
    ·
      refine ⟨56213349152388094670216633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37475566101592063113477755 56213349152388094670216633)
      ·
        refine ⟨42160011864291071002662475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56213349152388094670216633 42160011864291071002662475)
        ·
          refine ⟨63240017796436606503993713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42160011864291071002662475 63240017796436606503993713)
          ·
            refine ⟨47430013347327454877995285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63240017796436606503993713 47430013347327454877995285)
            ·
              refine ⟨2223281875655974447406029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47430013347327454877995285 2223281875655974447406029)
              ·
                refine ⟨833730703370990417777261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2223281875655974447406029 833730703370990417777261)
                ·
                  refine ⟨312649013764121406666473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833730703370990417777261 312649013764121406666473)
                  ·
                    rfl

theorem cell21_1369984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_1369984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369984 prefixEnd_1369984 := by exact prefixLift 1369984
  have htrace : WordTrace (prefixWord ++ tailWord_1369984) baseStart_1369984 baseEnd_1369984 := by
    simpa [prefixWord, tailWord_1369984, baseEnd_1369984] using wordTrace_append hprefix tailTrace_1369984
  have hstable : (prefixWord ++ tailWord_1369984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369984).length < 2 ^ (prefixWord ++ tailWord_1369984).sum := by decide
  have hdescent : baseEnd_1369984 < baseStart_1369984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370060 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1370060 : Nat := 118140960795 + 1370060 * 2 ^ 59
def prefixEnd_1370060 : Nat := 4983230072969 + 3 ^ 40 * 1370060 * 2
def baseEnd_1370060 : Nat := 312666357999562163399651

theorem tailTrace_1370060 : CollatzResearch.WordTrace tailWord_1370060 prefixEnd_1370060 312666357999562163399651 := by
  unfold tailWord_1370060
  simp only [CollatzResearch.WordTrace]
  refine ⟨24985096708257041232201817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33313462277676054976269089 24985096708257041232201817)
  ·
    refine ⟨18738822531192780924151363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24985096708257041232201817 18738822531192780924151363)
    ·
      refine ⟨28108233796789171386227045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18738822531192780924151363 28108233796789171386227045)
      ·
        refine ⟨5270293836897969634917571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28108233796789171386227045 5270293836897969634917571)
        ·
          refine ⟨7905440755346954452376357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270293836897969634917571 7905440755346954452376357)
          ·
            refine ⟨1482270141627553959820567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7905440755346954452376357 1482270141627553959820567)
            ·
              refine ⟨2223405212441330939730851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482270141627553959820567 2223405212441330939730851)
              ·
                refine ⟨3335107818661996409596277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223405212441330939730851 3335107818661996409596277)
                ·
                  refine ⟨312666357999562163399651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335107818661996409596277 312666357999562163399651)
                  ·
                    rfl

theorem cell21_1370060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1370060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370060 prefixEnd_1370060 := by exact prefixLift 1370060
  have htrace : WordTrace (prefixWord ++ tailWord_1370060) baseStart_1370060 baseEnd_1370060 := by
    simpa [prefixWord, tailWord_1370060, baseEnd_1370060] using wordTrace_append hprefix tailTrace_1370060
  have hstable : (prefixWord ++ tailWord_1370060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370060).length < 2 ^ (prefixWord ++ tailWord_1370060).sum := by decide
  have hdescent : baseEnd_1370060 < baseStart_1370060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370122 : List Nat := [3, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1370122 : Nat := 118140960795 + 1370122 * 2 ^ 59
def prefixEnd_1370122 : Nat := 4983230072969 + 3 ^ 40 * 1370122 * 2
def baseEnd_1370122 : Nat := 104226835748087944455397

theorem tailTrace_1370122 : CollatzResearch.WordTrace tailWord_1370122 prefixEnd_1370122 104226835748087944455397 := by
  unfold tailWord_1370122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493113685572366763290155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33314969828192978035440413 12493113685572366763290155)
  ·
    refine ⟨18739670528358550144935233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12493113685572366763290155 18739670528358550144935233)
    ·
      refine ⟨14054752896268912608701425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18739670528358550144935233 14054752896268912608701425)
      ·
        refine ⟨10541064672201684456526069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14054752896268912608701425 10541064672201684456526069)
        ·
          refine ⟨988224813018907917799319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10541064672201684456526069 988224813018907917799319)
          ·
            refine ⟨1482337219528361876698979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988224813018907917799319 1482337219528361876698979)
            ·
              refine ⟨2223505829292542815048469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482337219528361876698979 2223505829292542815048469)
              ·
                refine ⟨104226835748087944455397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2223505829292542815048469 104226835748087944455397)
                ·
                  rfl

theorem cell21_1370122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1370122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370122 prefixEnd_1370122 := by exact prefixLift 1370122
  have htrace : WordTrace (prefixWord ++ tailWord_1370122) baseStart_1370122 baseEnd_1370122 := by
    simpa [prefixWord, tailWord_1370122, baseEnd_1370122] using wordTrace_append hprefix tailTrace_1370122
  have hstable : (prefixWord ++ tailWord_1370122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370122).length < 2 ^ (prefixWord ++ tailWord_1370122).sum := by decide
  have hdescent : baseEnd_1370122 < baseStart_1370122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370198 : List Nat := [5, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1370198 : Nat := 118140960795 + 1370198 * 2 ^ 59
def prefixEnd_1370198 : Nat := 4983230072969 + 3 ^ 40 * 1370198 * 2
def baseEnd_1370198 : Nat := 104232617159901530033123

theorem tailTrace_1370198 : CollatzResearch.WordTrace tailWord_1370198 prefixEnd_1370198 104232617159901530033123 := by
  unfold tailWord_1370198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123451668125883252057953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33316817793342754688618165 3123451668125883252057953)
  ·
    refine ⟨2342588751094412439043465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3123451668125883252057953 2342588751094412439043465)
    ·
      refine ⟨1756941563320809329282599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2342588751094412439043465 1756941563320809329282599)
      ·
        refine ⟨2635412344981213993923899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1756941563320809329282599 2635412344981213993923899)
        ·
          refine ⟨3953118517471820990885849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635412344981213993923899 3953118517471820990885849)
          ·
            refine ⟨2964838888103865743164387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953118517471820990885849 2964838888103865743164387)
            ·
              refine ⟨4447258332155798614746581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964838888103865743164387 4447258332155798614746581)
              ·
                refine ⟨104232617159901530033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4447258332155798614746581 104232617159901530033123)
                ·
                  rfl

theorem cell21_1370198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1370198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370198 prefixEnd_1370198 := by exact prefixLift 1370198
  have htrace : WordTrace (prefixWord ++ tailWord_1370198) baseStart_1370198 baseEnd_1370198 := by
    simpa [prefixWord, tailWord_1370198, baseEnd_1370198] using wordTrace_append hprefix tailTrace_1370198
  have hstable : (prefixWord ++ tailWord_1370198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370198).length < 2 ^ (prefixWord ++ tailWord_1370198).sum := by decide
  have hdescent : baseEnd_1370198 < baseStart_1370198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370212 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1370212 : Nat := 118140960795 + 1370212 * 2 ^ 59
def prefixEnd_1370212 : Nat := 4983230072969 + 3 ^ 40 * 1370212 * 2
def baseEnd_1370212 : Nat := 312701046470443676866007

theorem tailTrace_1370212 : CollatzResearch.WordTrace tailWord_1370212 prefixEnd_1370212 312701046470443676866007 := by
  unfold tailWord_1370212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24987868655981706211968445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33317158207975608282624593 24987868655981706211968445)
  ·
    refine ⟨9370450745993139829488167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24987868655981706211968445 9370450745993139829488167)
    ·
      refine ⟨14055676118989709744232251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370450745993139829488167 14055676118989709744232251)
      ·
        refine ⟨21083514178484564616348377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055676118989709744232251 21083514178484564616348377)
        ·
          refine ⟨15812635633863423462261283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21083514178484564616348377 15812635633863423462261283)
          ·
            refine ⟨23718953450795135193391925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15812635633863423462261283 23718953450795135193391925)
            ·
              refine ⟨2223651886012043924380493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23718953450795135193391925 2223651886012043924380493)
              ·
                refine ⟨833869457254516471642685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2223651886012043924380493 833869457254516471642685)
                ·
                  refine ⟨312701046470443676866007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833869457254516471642685 312701046470443676866007)
                  ·
                    rfl

theorem cell21_1370212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1370212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370212 prefixEnd_1370212 := by exact prefixLift 1370212
  have htrace : WordTrace (prefixWord ++ tailWord_1370212) baseStart_1370212 baseEnd_1370212 := by
    simpa [prefixWord, tailWord_1370212, baseEnd_1370212] using wordTrace_append hprefix tailTrace_1370212
  have hstable : (prefixWord ++ tailWord_1370212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370212).length < 2 ^ (prefixWord ++ tailWord_1370212).sum := by decide
  have hdescent : baseEnd_1370212 < baseStart_1370212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370223 : List Nat := [1, 1, 2, 1, 3, 4, 9]
def baseStart_1370223 : Nat := 118140960795 + 1370223 * 2 ^ 59
def prefixEnd_1370223 : Nat := 4983230072969 + 3 ^ 40 * 1370223 * 2
def baseEnd_1370223 : Nat := 34744839646701122464739

theorem tailTrace_1370223 : CollatzResearch.WordTrace tailWord_1370223 prefixEnd_1370223 34744839646701122464739 := by
  unfold tailWord_1370223
  simp only [CollatzResearch.WordTrace]
  refine ⟨49976138514923561302587323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33317425676615707535058215 49976138514923561302587323)
  ·
    refine ⟨74964207772385341953880985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49976138514923561302587323 74964207772385341953880985)
    ·
      refine ⟨56223155829289006465410739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74964207772385341953880985 56223155829289006465410739)
      ·
        refine ⟨84334733743933509698116109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56223155829289006465410739 84334733743933509698116109)
        ·
          refine ⟨31625525153975066136793541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84334733743933509698116109 31625525153975066136793541)
          ·
            refine ⟨5929785966370324900648789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31625525153975066136793541 5929785966370324900648789)
            ·
              refine ⟨34744839646701122464739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5929785966370324900648789 34744839646701122464739)
              ·
                rfl

theorem cell21_1370223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_1370223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370223 prefixEnd_1370223 := by exact prefixLift 1370223
  have htrace : WordTrace (prefixWord ++ tailWord_1370223) baseStart_1370223 baseEnd_1370223 := by
    simpa [prefixWord, tailWord_1370223, baseEnd_1370223] using wordTrace_append hprefix tailTrace_1370223
  have hstable : (prefixWord ++ tailWord_1370223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370223).length < 2 ^ (prefixWord ++ tailWord_1370223).sum := by decide
  have hdescent : baseEnd_1370223 < baseStart_1370223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370243 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 4]
def baseStart_1370243 : Nat := 118140960795 + 1370243 * 2 ^ 59
def prefixEnd_1370243 : Nat := 4983230072969 + 3 ^ 40 * 1370243 * 2
def baseEnd_1370243 : Nat := 312708121092794511849277

theorem tailTrace_1370243 : CollatzResearch.WordTrace tailWord_1370243 prefixEnd_1370243 312708121092794511849277 := by
  unfold tailWord_1370243
  simp only [CollatzResearch.WordTrace]
  refine ⟨49976867974851104718315383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33317911983234069812210255 49976867974851104718315383)
  ·
    refine ⟨74965301962276657077473075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49976867974851104718315383 74965301962276657077473075)
    ·
      refine ⟨112447952943414985616209613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74965301962276657077473075 112447952943414985616209613)
      ·
        refine ⟨42167982353780619606078605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112447952943414985616209613 42167982353780619606078605)
        ·
          refine ⟨15812993382667732352279477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42167982353780619606078605 15812993382667732352279477)
          ·
            refine ⟨1482468129625099908026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15812993382667732352279477 1482468129625099908026201)
            ·
              refine ⟨1111851097218824931019651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482468129625099908026201 1111851097218824931019651)
              ·
                refine ⟨1667776645828237396529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111851097218824931019651 1667776645828237396529477)
                ·
                  refine ⟨312708121092794511849277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667776645828237396529477 312708121092794511849277)
                  ·
                    rfl

theorem cell21_1370243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_1370243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370243 prefixEnd_1370243 := by exact prefixLift 1370243
  have htrace : WordTrace (prefixWord ++ tailWord_1370243) baseStart_1370243 baseEnd_1370243 := by
    simpa [prefixWord, tailWord_1370243, baseEnd_1370243] using wordTrace_append hprefix tailTrace_1370243
  have hstable : (prefixWord ++ tailWord_1370243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370243).length < 2 ^ (prefixWord ++ tailWord_1370243).sum := by decide
  have hdescent : baseEnd_1370243 < baseStart_1370243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370347 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 3]
def baseStart_1370347 : Nat := 118140960795 + 1370347 * 2 ^ 59
def prefixEnd_1370347 : Nat := 4983230072969 + 3 ^ 40 * 1370347 * 2
def baseEnd_1370347 : Nat := 312731855309713442115731

theorem tailTrace_1370347 : CollatzResearch.WordTrace tailWord_1370347 prefixEnd_1370347 312731855309713442115731 := by
  unfold tailWord_1370347
  simp only [CollatzResearch.WordTrace]
  refine ⟨49980661166474330480101295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33320440777649553653400863 49980661166474330480101295)
  ·
    refine ⟨74970991749711495720151943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49980661166474330480101295 74970991749711495720151943)
    ·
      refine ⟨112456487624567243580227915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74970991749711495720151943 112456487624567243580227915)
      ·
        refine ⟨168684731436850865370341873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112456487624567243580227915 168684731436850865370341873)
        ·
          refine ⟨126513548577638149027756405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168684731436850865370341873 126513548577638149027756405)
          ·
            refine ⟨11860645179153576471352163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126513548577638149027756405 11860645179153576471352163)
            ·
              refine ⟨17790967768730364707028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11860645179153576471352163 17790967768730364707028245)
              ·
                refine ⟨833951614159235845641949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17790967768730364707028245 833951614159235845641949)
                ·
                  refine ⟨312731855309713442115731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833951614159235845641949 312731855309713442115731)
                  ·
                    rfl

theorem cell21_1370347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].length) (baseStart_1370347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370347 prefixEnd_1370347 := by exact prefixLift 1370347
  have htrace : WordTrace (prefixWord ++ tailWord_1370347) baseStart_1370347 baseEnd_1370347 := by
    simpa [prefixWord, tailWord_1370347, baseEnd_1370347] using wordTrace_append hprefix tailTrace_1370347
  have hstable : (prefixWord ++ tailWord_1370347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370347).length < 2 ^ (prefixWord ++ tailWord_1370347).sum := by decide
  have hdescent : baseEnd_1370347 < baseStart_1370347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370482 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1370482 : Nat := 118140960795 + 1370482 * 2 ^ 59
def prefixEnd_1370482 : Nat := 4983230072969 + 3 ^ 40 * 1370482 * 2
def baseEnd_1370482 : Nat := 312762664148983207365455

theorem tailTrace_1370482 : CollatzResearch.WordTrace tailWord_1370482 prefixEnd_1370482 312762664148983207365455 := by
  unfold tailWord_1370482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496396255246312134066425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33323723347323499024177133 12496396255246312134066425)
  ·
    refine ⟨9372297191434734100549819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12496396255246312134066425 9372297191434734100549819)
    ·
      refine ⟨14058445787152101150824729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9372297191434734100549819 14058445787152101150824729)
      ·
        refine ⟨10543834340364075863118547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14058445787152101150824729 10543834340364075863118547)
        ·
          refine ⟨15815751510546113794677821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543834340364075863118547 15815751510546113794677821)
          ·
            refine ⟨5930906816454792673004183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15815751510546113794677821 5930906816454792673004183)
            ·
              refine ⟨8896360224682189009506275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930906816454792673004183 8896360224682189009506275)
              ·
                refine ⟨13344540337023283514259413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896360224682189009506275 13344540337023283514259413)
                ·
                  refine ⟨312762664148983207365455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13344540337023283514259413 312762664148983207365455)
                  ·
                    rfl

theorem cell21_1370482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1370482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370482 prefixEnd_1370482 := by exact prefixLift 1370482
  have htrace : WordTrace (prefixWord ++ tailWord_1370482) baseStart_1370482 baseEnd_1370482 := by
    simpa [prefixWord, tailWord_1370482, baseEnd_1370482] using wordTrace_append hprefix tailTrace_1370482
  have hstable : (prefixWord ++ tailWord_1370482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370482).length < 2 ^ (prefixWord ++ tailWord_1370482).sum := by decide
  have hdescent : baseEnd_1370482 < baseStart_1370482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370485 : List Nat := [1, 3, 4, 1, 2, 2, 3, 5]
def baseStart_1370485 : Nat := 118140960795 + 1370485 * 2 ^ 59
def prefixEnd_1370485 : Nat := 4983230072969 + 3 ^ 40 * 1370485 * 2
def baseEnd_1370485 : Nat := 104254449596618622938483

theorem tailTrace_1370485 : CollatzResearch.WordTrace tailWord_1370485 prefixEnd_1370485 104254449596618622938483 := by
  unfold tailWord_1370485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985694439974380048624909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33323796293316253365749939 49985694439974380048624909)
  ·
    refine ⟨18744635414990392518234341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49985694439974380048624909 18744635414990392518234341)
    ·
      refine ⟨3514619140310698597168939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18744635414990392518234341 3514619140310698597168939)
      ·
        refine ⟨5271928710466047895753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514619140310698597168939 5271928710466047895753409)
        ·
          refine ⟨3953946532849535921815057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5271928710466047895753409 3953946532849535921815057)
          ·
            refine ⟨2965459899637151941361293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953946532849535921815057 2965459899637151941361293)
            ·
              refine ⟨1112047462363931978010485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2965459899637151941361293 1112047462363931978010485)
              ·
                refine ⟨104254449596618622938483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1112047462363931978010485 104254449596618622938483)
                ·
                  rfl

theorem cell21_1370485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].length) (baseStart_1370485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370485 prefixEnd_1370485 := by exact prefixLift 1370485
  have htrace : WordTrace (prefixWord ++ tailWord_1370485) baseStart_1370485 baseEnd_1370485 := by
    simpa [prefixWord, tailWord_1370485, baseEnd_1370485] using wordTrace_append hprefix tailTrace_1370485
  have hstable : (prefixWord ++ tailWord_1370485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370485).length < 2 ^ (prefixWord ++ tailWord_1370485).sum := by decide
  have hdescent : baseEnd_1370485 < baseStart_1370485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370516 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1370516 : Nat := 118140960795 + 1370516 * 2 ^ 59
def prefixEnd_1370516 : Nat := 4983230072969 + 3 ^ 40 * 1370516 * 2
def baseEnd_1370516 : Nat := 312770423412206703798719

theorem tailTrace_1370516 : CollatzResearch.WordTrace tailWord_1370516 prefixEnd_1370516 312770423412206703798719 := by
  unfold tailWord_1370516
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993412551431036171501701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33324550068574714895335601 24993412551431036171501701)
  ·
    refine ⟨4686264853393319282156569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24993412551431036171501701 4686264853393319282156569)
    ·
      refine ⟨3514698640044989461617427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4686264853393319282156569 3514698640044989461617427)
      ·
        refine ⟨5272047960067484192426141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514698640044989461617427 5272047960067484192426141)
        ·
          refine ⟨1977017985025306572159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5272047960067484192426141 1977017985025306572159803)
          ·
            refine ⟨2965526977537959858239705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977017985025306572159803 2965526977537959858239705)
            ·
              refine ⟨2224145233153469893679779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965526977537959858239705 2224145233153469893679779)
              ·
                refine ⟨3336217849730204840519669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224145233153469893679779 3336217849730204840519669)
                ·
                  refine ⟨312770423412206703798719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3336217849730204840519669 312770423412206703798719)
                  ·
                    rfl

theorem cell21_1370516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1370516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370516 prefixEnd_1370516 := by exact prefixLift 1370516
  have htrace : WordTrace (prefixWord ++ tailWord_1370516) baseStart_1370516 baseEnd_1370516 := by
    simpa [prefixWord, tailWord_1370516, baseEnd_1370516] using wordTrace_append hprefix tailTrace_1370516
  have hstable : (prefixWord ++ tailWord_1370516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370516).length < 2 ^ (prefixWord ++ tailWord_1370516).sum := by decide
  have hdescent : baseEnd_1370516 < baseStart_1370516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370527 : List Nat := [1, 1, 2, 5, 1, 1, 2, 8]
def baseStart_1370527 : Nat := 118140960795 + 1370527 * 2 ^ 59
def prefixEnd_1370527 : Nat := 4983230072969 + 3 ^ 40 * 1370527 * 2
def baseEnd_1370527 : Nat := 104257644587357709705121

theorem tailTrace_1370527 : CollatzResearch.WordTrace tailWord_1370527 prefixEnd_1370527 104257644587357709705121 := by
  unfold tailWord_1370527
  simp only [CollatzResearch.WordTrace]
  refine ⟨49987226305822221221653835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33324817537214814147769223 49987226305822221221653835)
  ·
    refine ⟨74980839458733331832480753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49987226305822221221653835 74980839458733331832480753)
    ·
      refine ⟨56235629594049998874360565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74980839458733331832480753 56235629594049998874360565)
      ·
        refine ⟨5272090274442187394471303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56235629594049998874360565 5272090274442187394471303)
        ·
          refine ⟨7908135411663281091706955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5272090274442187394471303 7908135411663281091706955)
          ·
            refine ⟨11862203117494921637560433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908135411663281091706955 11862203117494921637560433)
            ·
              refine ⟨8896652338121191228170325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11862203117494921637560433 8896652338121191228170325)
              ·
                refine ⟨104257644587357709705121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8896652338121191228170325 104257644587357709705121)
                ·
                  rfl

theorem cell21_1370527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_1370527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370527 prefixEnd_1370527 := by exact prefixLift 1370527
  have htrace : WordTrace (prefixWord ++ tailWord_1370527) baseStart_1370527 baseEnd_1370527 := by
    simpa [prefixWord, tailWord_1370527, baseEnd_1370527] using wordTrace_append hprefix tailTrace_1370527
  have hstable : (prefixWord ++ tailWord_1370527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370527).length < 2 ^ (prefixWord ++ tailWord_1370527).sum := by decide
  have hdescent : baseEnd_1370527 < baseStart_1370527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370558 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1370558 : Nat := 118140960795 + 1370558 * 2 ^ 59
def prefixEnd_1370558 : Nat := 4983230072969 + 3 ^ 40 * 1370558 * 2
def baseEnd_1370558 : Nat := 312780008384423964098633

theorem tailTrace_1370558 : CollatzResearch.WordTrace tailWord_1370558 prefixEnd_1370558 312780008384423964098633 := by
  unfold tailWord_1370558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248544621088739189504041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33325571312473275677354885 6248544621088739189504041)
  ·
    refine ⟨4686408465816554392128031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6248544621088739189504041 4686408465816554392128031)
    ·
      refine ⟨7029612698724831588192047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686408465816554392128031 7029612698724831588192047)
      ·
        refine ⟨10544419048087247382288071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029612698724831588192047 10544419048087247382288071)
        ·
          refine ⟨15816628572130871073432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544419048087247382288071 15816628572130871073432107)
          ·
            refine ⟨23724942858196306610148161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816628572130871073432107 23724942858196306610148161)
            ·
              refine ⟨17793707143647229957611121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23724942858196306610148161 17793707143647229957611121)
              ·
                refine ⟨13345280357735422468208341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17793707143647229957611121 13345280357735422468208341)
                ·
                  refine ⟨312780008384423964098633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13345280357735422468208341 312780008384423964098633)
                  ·
                    rfl

theorem cell21_1370558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1370558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370558 prefixEnd_1370558 := by exact prefixLift 1370558
  have htrace : WordTrace (prefixWord ++ tailWord_1370558) baseStart_1370558 baseEnd_1370558 := by
    simpa [prefixWord, tailWord_1370558, baseEnd_1370558] using wordTrace_append hprefix tailTrace_1370558
  have hstable : (prefixWord ++ tailWord_1370558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370558).length < 2 ^ (prefixWord ++ tailWord_1370558).sum := by decide
  have hdescent : baseEnd_1370558 < baseStart_1370558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370634 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1370634 : Nat := 118140960795 + 1370634 * 2 ^ 59
def prefixEnd_1370634 : Nat := 4983230072969 + 3 ^ 40 * 1370634 * 2
def baseEnd_1370634 : Nat := 312797352619864720831811

theorem tailTrace_1370634 : CollatzResearch.WordTrace tailWord_1370634 prefixEnd_1370634 312797352619864720831811 := by
  unfold tailWord_1370634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497782229108644623949739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33327419277623052330532637 12497782229108644623949739)
  ·
    refine ⟨18746673343662966935924609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12497782229108644623949739 18746673343662966935924609)
    ·
      refine ⟨14060005007747225201943457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18746673343662966935924609 14060005007747225201943457)
      ·
        refine ⟨10545003755810418901457593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060005007747225201943457 10545003755810418901457593)
        ·
          refine ⟨7908752816857814176093195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545003755810418901457593 7908752816857814176093195)
          ·
            refine ⟨11863129225286721264139793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908752816857814176093195 11863129225286721264139793)
            ·
              refine ⟨8897346918965040948104845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11863129225286721264139793 8897346918965040948104845)
              ·
                refine ⟨3336505094611890355539317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8897346918965040948104845 3336505094611890355539317)
                ·
                  refine ⟨312797352619864720831811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3336505094611890355539317 312797352619864720831811)
                  ·
                    rfl

theorem cell21_1370634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1370634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370634 prefixEnd_1370634 := by exact prefixLift 1370634
  have htrace : WordTrace (prefixWord ++ tailWord_1370634) baseStart_1370634 baseEnd_1370634 := by
    simpa [prefixWord, tailWord_1370634, baseEnd_1370634] using wordTrace_append hprefix tailTrace_1370634
  have hstable : (prefixWord ++ tailWord_1370634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370634).length < 2 ^ (prefixWord ++ tailWord_1370634).sum := by decide
  have hdescent : baseEnd_1370634 < baseStart_1370634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370682 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1370682 : Nat := 118140960795 + 1370682 * 2 ^ 59
def prefixEnd_1370682 : Nat := 4983230072969 + 3 ^ 40 * 1370682 * 2
def baseEnd_1370682 : Nat := 312808306873827304031713

theorem tailTrace_1370682 : CollatzResearch.WordTrace tailWord_1370682 prefixEnd_1370682 312808306873827304031713 := by
  unfold tailWord_1370682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12498219905065170673386575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33328586413507121795697533 12498219905065170673386575)
  ·
    refine ⟨18747329857597756010079863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12498219905065170673386575 18747329857597756010079863)
    ·
      refine ⟨28120994786396634015119795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18747329857597756010079863 28120994786396634015119795)
      ·
        refine ⟨42181492179594951022679693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28120994786396634015119795 42181492179594951022679693)
        ·
          refine ⟨15818059567348106633504885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42181492179594951022679693 15818059567348106633504885)
          ·
            refine ⟨1482943084438884996891083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15818059567348106633504885 1482943084438884996891083)
            ·
              refine ⟨2224414626658327495336625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482943084438884996891083 2224414626658327495336625)
              ·
                refine ⟨1668310969993745621502469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224414626658327495336625 1668310969993745621502469)
                ·
                  refine ⟨312808306873827304031713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668310969993745621502469 312808306873827304031713)
                  ·
                    rfl

theorem cell21_1370682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1370682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370682 prefixEnd_1370682 := by exact prefixLift 1370682
  have htrace : WordTrace (prefixWord ++ tailWord_1370682) baseStart_1370682 baseEnd_1370682 := by
    simpa [prefixWord, tailWord_1370682, baseEnd_1370682] using wordTrace_append hprefix tailTrace_1370682
  have hstable : (prefixWord ++ tailWord_1370682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370682).length < 2 ^ (prefixWord ++ tailWord_1370682).sum := by decide
  have hdescent : baseEnd_1370682 < baseStart_1370682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370724 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1370724 : Nat := 118140960795 + 1370724 * 2 ^ 59
def prefixEnd_1370724 : Nat := 4983230072969 + 3 ^ 40 * 1370724 * 2
def baseEnd_1370724 : Nat := 312817891846044564331627

theorem tailTrace_1370724 : CollatzResearch.WordTrace tailWord_1370724 prefixEnd_1370724 312817891846044564331627 := by
  unfold tailWord_1370724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997205743054261933287613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33329607657405682577716817 24997205743054261933287613)
  ·
    refine ⟨9373952153645348224982855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24997205743054261933287613 9373952153645348224982855)
    ·
      refine ⟨14060928230468022337474283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373952153645348224982855 14060928230468022337474283)
      ·
        refine ⟨21091392345702033506211425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14060928230468022337474283 21091392345702033506211425)
        ·
          refine ⟨15818544259276525129658569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21091392345702033506211425 15818544259276525129658569)
          ·
            refine ⟨11863908194457393847243927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15818544259276525129658569 11863908194457393847243927)
            ·
              refine ⟨17795862291686090770865891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863908194457393847243927 17795862291686090770865891)
              ·
                refine ⟨26693793437529136156298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17795862291686090770865891 26693793437529136156298837)
                ·
                  refine ⟨312817891846044564331627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26693793437529136156298837 312817891846044564331627)
                  ·
                    rfl

theorem cell21_1370724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1370724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370724 prefixEnd_1370724 := by exact prefixLift 1370724
  have htrace : WordTrace (prefixWord ++ tailWord_1370724) baseStart_1370724 baseEnd_1370724 := by
    simpa [prefixWord, tailWord_1370724, baseEnd_1370724] using wordTrace_append hprefix tailTrace_1370724
  have hstable : (prefixWord ++ tailWord_1370724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370724).length < 2 ^ (prefixWord ++ tailWord_1370724).sum := by decide
  have hdescent : baseEnd_1370724 < baseStart_1370724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370772 : List Nat := [2, 4, 2, 2, 1, 1, 2, 7]
def baseStart_1370772 : Nat := 118140960795 + 1370772 * 2 ^ 59
def prefixEnd_1370772 : Nat := 4983230072969 + 3 ^ 40 * 1370772 * 2
def baseEnd_1370772 : Nat := 104276282033335715843843

theorem tailTrace_1370772 : CollatzResearch.WordTrace tailWord_1370772 prefixEnd_1370772 104276282033335715843843 := by
  unfold tailWord_1370772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24998081094967314032161285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33330774793289752042881713 24998081094967314032161285)
  ·
    refine ⟨4687140205306371381030241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24998081094967314032161285 4687140205306371381030241)
    ·
      refine ⟨3515355153979778535772681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4687140205306371381030241 3515355153979778535772681)
      ·
        refine ⟨2636516365484833901829511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515355153979778535772681 2636516365484833901829511)
        ·
          refine ⟨3954774548227250852744267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636516365484833901829511 3954774548227250852744267)
          ·
            refine ⟨5932161822340876279116401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954774548227250852744267 5932161822340876279116401)
            ·
              refine ⟨4449121366755657209337301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5932161822340876279116401 4449121366755657209337301)
              ·
                refine ⟨104276282033335715843843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4449121366755657209337301 104276282033335715843843)
                ·
                  rfl

theorem cell21_1370772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_1370772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370772 prefixEnd_1370772 := by exact prefixLift 1370772
  have htrace : WordTrace (prefixWord ++ tailWord_1370772) baseStart_1370772 baseEnd_1370772 := by
    simpa [prefixWord, tailWord_1370772, baseEnd_1370772] using wordTrace_append hprefix tailTrace_1370772
  have hstable : (prefixWord ++ tailWord_1370772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370772).length < 2 ^ (prefixWord ++ tailWord_1370772).sum := by decide
  have hdescent : baseEnd_1370772 < baseStart_1370772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370803 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 3]
def baseStart_1370803 : Nat := 118140960795 + 1370803 * 2 ^ 59
def prefixEnd_1370803 : Nat := 4983230072969 + 3 ^ 40 * 1370803 * 2
def baseEnd_1370803 : Nat := 312835920722357982514799

theorem tailTrace_1370803 : CollatzResearch.WordTrace tailWord_1370803 prefixEnd_1370803 312835920722357982514799 := by
  unfold tailWord_1370803
  simp only [CollatzResearch.WordTrace]
  refine ⟨49997292852822320358701063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33331528568548213572467375 49997292852822320358701063)
  ·
    refine ⟨74995939279233480538051595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49997292852822320358701063 74995939279233480538051595)
    ·
      refine ⟨112493908918850220807077393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74995939279233480538051595 112493908918850220807077393)
      ·
        refine ⟨84370431689137665605308045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112493908918850220807077393 84370431689137665605308045)
        ·
          refine ⟨31638911883426624601990517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84370431689137665605308045 31638911883426624601990517)
          ·
            refine ⟨2966147989071246056436611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31638911883426624601990517 2966147989071246056436611)
            ·
              refine ⟨4449221983606869084654917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966147989071246056436611 4449221983606869084654917)
              ·
                refine ⟨834229121926287953372797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4449221983606869084654917 834229121926287953372797)
                ·
                  refine ⟨312835920722357982514799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834229121926287953372797 312835920722357982514799)
                  ·
                    rfl

theorem cell21_1370803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].length) (baseStart_1370803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370803 prefixEnd_1370803 := by exact prefixLift 1370803
  have htrace : WordTrace (prefixWord ++ tailWord_1370803) baseStart_1370803 baseEnd_1370803 := by
    simpa [prefixWord, tailWord_1370803, baseEnd_1370803] using wordTrace_append hprefix tailTrace_1370803
  have hstable : (prefixWord ++ tailWord_1370803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370803).length < 2 ^ (prefixWord ++ tailWord_1370803).sum := by decide
  have hdescent : baseEnd_1370803 < baseStart_1370803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370806 : List Nat := [5, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1370806 : Nat := 118140960795 + 1370806 * 2 ^ 59
def prefixEnd_1370806 : Nat := 4983230072969 + 3 ^ 40 * 1370806 * 2
def baseEnd_1370806 : Nat := 104278868454410214654931

theorem tailTrace_1370806 : CollatzResearch.WordTrace tailWord_1370806 prefixEnd_1370806 104278868454410214654931 := by
  unfold tailWord_1370806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124837641988215741941267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33331601514540967914040181 3124837641988215741941267)
  ·
    refine ⟨4687256462982323612911901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3124837641988215741941267 4687256462982323612911901)
    ·
      refine ⟨1757721173618371354841963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4687256462982323612911901 1757721173618371354841963)
      ·
        refine ⟨2636581760427557032262945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757721173618371354841963 2636581760427557032262945)
        ·
          refine ⟨1977436320320667774197209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2636581760427557032262945 1977436320320667774197209)
          ·
            refine ⟨1483077240240500830647907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1977436320320667774197209 1483077240240500830647907)
            ·
              refine ⟨2224615860360751245971861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483077240240500830647907 2224615860360751245971861)
              ·
                refine ⟨104278868454410214654931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2224615860360751245971861 104278868454410214654931)
                ·
                  rfl

theorem cell21_1370806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1370806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370806 prefixEnd_1370806 := by exact prefixLift 1370806
  have htrace : WordTrace (prefixWord ++ tailWord_1370806) baseStart_1370806 baseEnd_1370806 := by
    simpa [prefixWord, tailWord_1370806, baseEnd_1370806] using wordTrace_append hprefix tailTrace_1370806
  have hstable : (prefixWord ++ tailWord_1370806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370806).length < 2 ^ (prefixWord ++ tailWord_1370806).sum := by decide
  have hdescent : baseEnd_1370806 < baseStart_1370806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370837 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 3]
def baseStart_1370837 : Nat := 118140960795 + 1370837 * 2 ^ 59
def prefixEnd_1370837 : Nat := 4983230072969 + 3 ^ 40 * 1370837 * 2
def baseEnd_1370837 : Nat := 312843679985581478948063

theorem tailTrace_1370837 : CollatzResearch.WordTrace tailWord_1370837 prefixEnd_1370837 312843679985581478948063 := by
  unfold tailWord_1370837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49998532934699144165438765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33332355289799429443625843 49998532934699144165438765)
  ·
    refine ⟨18749449850512179062039537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49998532934699144165438765 18749449850512179062039537)
    ·
      refine ⟨14062087387884134296529653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18749449850512179062039537 14062087387884134296529653)
      ·
        refine ⟨1318320692614137590299655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14062087387884134296529653 1318320692614137590299655)
        ·
          refine ⟨1977481038921206385449483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318320692614137590299655 1977481038921206385449483)
          ·
            refine ⟨2966221558381809578174225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977481038921206385449483 2966221558381809578174225)
            ·
              refine ⟨2224666168786357183630669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966221558381809578174225 2224666168786357183630669)
              ·
                refine ⟨834249813294883943861501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2224666168786357183630669 834249813294883943861501)
                ·
                  refine ⟨312843679985581478948063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834249813294883943861501 312843679985581478948063)
                  ·
                    rfl

theorem cell21_1370837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_1370837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370837 prefixEnd_1370837 := by exact prefixLift 1370837
  have htrace : WordTrace (prefixWord ++ tailWord_1370837) baseStart_1370837 baseEnd_1370837 := by
    simpa [prefixWord, tailWord_1370837, baseEnd_1370837] using wordTrace_append hprefix tailTrace_1370837
  have hstable : (prefixWord ++ tailWord_1370837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370837).length < 2 ^ (prefixWord ++ tailWord_1370837).sum := by decide
  have hdescent : baseEnd_1370837 < baseStart_1370837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370862 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1370862 : Nat := 118140960795 + 1370862 * 2 ^ 59
def prefixEnd_1370862 : Nat := 4983230072969 + 3 ^ 40 * 1370862 * 2
def baseEnd_1370862 : Nat := 312849385326186991031345

theorem tailTrace_1370862 : CollatzResearch.WordTrace tailWord_1370862 prefixEnd_1370862 312849385326186991031345 := by
  unfold tailWord_1370862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249930594951071679387355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33332963173072382290065893 6249930594951071679387355)
  ·
    refine ⟨9374895892426607519081033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6249930594951071679387355 9374895892426607519081033)
    ·
      refine ⟨7031171919319955639310775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9374895892426607519081033 7031171919319955639310775)
      ·
        refine ⟨10546757878979933458966163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031171919319955639310775 10546757878979933458966163)
        ·
          refine ⟨15820136818469900188449245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546757878979933458966163 15820136818469900188449245)
          ·
            refine ⟨5932551306926212570668467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15820136818469900188449245 5932551306926212570668467)
            ·
              refine ⟨8898826960389318856002701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932551306926212570668467 8898826960389318856002701)
              ·
                refine ⟨3337060110145994571001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8898826960389318856002701 3337060110145994571001013)
                ·
                  refine ⟨312849385326186991031345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3337060110145994571001013 312849385326186991031345)
                  ·
                    rfl

theorem cell21_1370862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1370862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370862 prefixEnd_1370862 := by exact prefixLift 1370862
  have htrace : WordTrace (prefixWord ++ tailWord_1370862) baseStart_1370862 baseEnd_1370862 := by
    simpa [prefixWord, tailWord_1370862, baseEnd_1370862] using wordTrace_append hprefix tailTrace_1370862
  have hstable : (prefixWord ++ tailWord_1370862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370862).length < 2 ^ (prefixWord ++ tailWord_1370862).sum := by decide
  have hdescent : baseEnd_1370862 < baseStart_1370862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370969 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_1370969 : Nat := 118140960795 + 1370969 * 2 ^ 59
def prefixEnd_1370969 : Nat := 4983230072969 + 3 ^ 40 * 1370969 * 2
def baseEnd_1370969 : Nat := 312873804183978582747793

theorem tailTrace_1370969 : CollatzResearch.WordTrace tailWord_1370969 prefixEnd_1370969 312873804183978582747793 := by
  unfold tailWord_1370969
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003347370220930709243961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33335564913480620472829307 50003347370220930709243961)
  ·
    refine ⟨37502510527665698031932971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50003347370220930709243961 37502510527665698031932971)
    ·
      refine ⟨56253765791498547047899457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37502510527665698031932971 56253765791498547047899457)
      ·
        refine ⟨42190324343623910285924593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56253765791498547047899457 42190324343623910285924593)
        ·
          refine ⟨31642743257717932714443445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42190324343623910285924593 31642743257717932714443445)
          ·
            refine ⟨2966507180411056191979073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31642743257717932714443445 2966507180411056191979073)
            ·
              refine ⟨2224880385308292143984305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966507180411056191979073 2224880385308292143984305)
              ·
                refine ⟨1668660288981219107988229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224880385308292143984305 1668660288981219107988229)
                ·
                  refine ⟨312873804183978582747793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668660288981219107988229 312873804183978582747793)
                  ·
                    rfl

theorem cell21_1370969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_1370969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370969 prefixEnd_1370969 := by exact prefixLift 1370969
  have htrace : WordTrace (prefixWord ++ tailWord_1370969) baseStart_1370969 baseEnd_1370969 := by
    simpa [prefixWord, tailWord_1370969, baseEnd_1370969] using wordTrace_append hprefix tailTrace_1370969
  have hstable : (prefixWord ++ tailWord_1370969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370969).length < 2 ^ (prefixWord ++ tailWord_1370969).sum := by decide
  have hdescent : baseEnd_1370969 < baseStart_1370969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370972 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1370972 : Nat := 118140960795 + 1370972 * 2 ^ 59
def prefixEnd_1370972 : Nat := 4983230072969 + 3 ^ 40 * 1370972 * 2
def baseEnd_1370972 : Nat := 312874488824851244197787

theorem tailTrace_1370972 : CollatzResearch.WordTrace tailWord_1370972 prefixEnd_1370972 312874488824851244197787 := by
  unfold tailWord_1370972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25001728394605031110801585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33335637859473374814402113 25001728394605031110801585)
  ·
    refine ⟨18751296295953773333101189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25001728394605031110801585 18751296295953773333101189)
    ·
      refine ⟨3515868055491332499956473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18751296295953773333101189 3515868055491332499956473)
      ·
        refine ⟨2636901041618499374967355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515868055491332499956473 2636901041618499374967355)
        ·
          refine ⟨3955351562427749062451033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636901041618499374967355 3955351562427749062451033)
          ·
            refine ⟨2966513671820811796838275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955351562427749062451033 2966513671820811796838275)
            ·
              refine ⟨4449770507731217695257413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966513671820811796838275 4449770507731217695257413)
              ·
                refine ⟨834331970199603317860765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4449770507731217695257413 834331970199603317860765)
                ·
                  refine ⟨312874488824851244197787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834331970199603317860765 312874488824851244197787)
                  ·
                    rfl

theorem cell21_1370972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1370972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370972 prefixEnd_1370972 := by exact prefixLift 1370972
  have htrace : WordTrace (prefixWord ++ tailWord_1370972) baseStart_1370972 baseEnd_1370972 := by
    simpa [prefixWord, tailWord_1370972, baseEnd_1370972] using wordTrace_append hprefix tailTrace_1370972
  have hstable : (prefixWord ++ tailWord_1370972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370972).length < 2 ^ (prefixWord ++ tailWord_1370972).sum := by decide
  have hdescent : baseEnd_1370972 < baseStart_1370972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370983 : List Nat := [1, 1, 5, 1, 2, 2, 3, 6]
def baseStart_1370983 : Nat := 118140960795 + 1370983 * 2 ^ 59
def prefixEnd_1370983 : Nat := 4983230072969 + 3 ^ 40 * 1370983 * 2
def baseEnd_1370983 : Nat := 104292333058239223171477

theorem tailTrace_1370983 : CollatzResearch.WordTrace tailWord_1370983 prefixEnd_1370983 104292333058239223171477 := by
  unfold tailWord_1370983
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003857992170211100253603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33335905328113474066835735 50003857992170211100253603)
  ·
    refine ⟨75005786988255316650380405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50003857992170211100253603 75005786988255316650380405)
    ·
      refine ⟨7031792530148935935973163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75005786988255316650380405 7031792530148935935973163)
      ·
        refine ⟨10547688795223403903959745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031792530148935935973163 10547688795223403903959745)
        ·
          refine ⟨7910766596417552927969809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10547688795223403903959745 7910766596417552927969809)
          ·
            refine ⟨5933074947313164695977357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7910766596417552927969809 5933074947313164695977357)
            ·
              refine ⟨2224903105242436760991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5933074947313164695977357 2224903105242436760991509)
              ·
                refine ⟨104292333058239223171477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2224903105242436760991509 104292333058239223171477)
                ·
                  rfl

theorem cell21_1370983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_1370983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1370983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1370983 prefixEnd_1370983 := by exact prefixLift 1370983
  have htrace : WordTrace (prefixWord ++ tailWord_1370983) baseStart_1370983 baseEnd_1370983 := by
    simpa [prefixWord, tailWord_1370983, baseEnd_1370983] using wordTrace_append hprefix tailTrace_1370983
  have hstable : (prefixWord ++ tailWord_1370983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370983).length < 2 ^ (prefixWord ++ tailWord_1370983).sum := by decide
  have hdescent : baseEnd_1370983 < baseStart_1370983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371197 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1371197 : Nat := 118140960795 + 1371197 * 2 ^ 59
def prefixEnd_1371197 : Nat := 4983230072969 + 3 ^ 40 * 1371197 * 2
def baseEnd_1371197 : Nat := 312925836890300852947327

theorem tailTrace_1371197 : CollatzResearch.WordTrace tailWord_1371197 prefixEnd_1371197 312925836890300852947327 := by
  unfold tailWord_1371197
  simp only [CollatzResearch.WordTrace]
  refine ⟨50011663213394925648543845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33341108808929950432362563 50011663213394925648543845)
  ·
    refine ⟨9377186852511548559101971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50011663213394925648543845 9377186852511548559101971)
    ·
      refine ⟨14065780278767322838652957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9377186852511548559101971 14065780278767322838652957)
      ·
        refine ⟨5274667604537746064494859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14065780278767322838652957 5274667604537746064494859)
        ·
          refine ⟨7912001406806619096742289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274667604537746064494859 7912001406806619096742289)
          ·
            refine ⟨5934001055104964322556717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7912001406806619096742289 5934001055104964322556717)
            ·
              refine ⟨2225250395664361620958769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5934001055104964322556717 2225250395664361620958769)
              ·
                refine ⟨1668937796748271215719077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225250395664361620958769 1668937796748271215719077)
                ·
                  refine ⟨312925836890300852947327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668937796748271215719077 312925836890300852947327)
                  ·
                    rfl

theorem cell21_1371197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1371197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371197 prefixEnd_1371197 := by exact prefixLift 1371197
  have htrace : WordTrace (prefixWord ++ tailWord_1371197) baseStart_1371197 baseEnd_1371197 := by
    simpa [prefixWord, tailWord_1371197, baseEnd_1371197] using wordTrace_append hprefix tailTrace_1371197
  have hstable : (prefixWord ++ tailWord_1371197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371197).length < 2 ^ (prefixWord ++ tailWord_1371197).sum := by decide
  have hdescent : baseEnd_1371197 < baseStart_1371197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371262 : List Nat := [4, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1371262 : Nat := 118140960795 + 1371262 * 2 ^ 59
def prefixEnd_1371262 : Nat := 4983230072969 + 3 ^ 40 * 1371262 * 2
def baseEnd_1371262 : Nat := 104313556925291728121287

theorem tailTrace_1371262 : CollatzResearch.WordTrace tailWord_1371262 prefixEnd_1371262 104313556925291728121287 := by
  unfold tailWord_1371262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251754244769930218707505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33342689305439627833106693 6251754244769930218707505)
  ·
    refine ⟨4688815683577447664030629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6251754244769930218707505 4688815683577447664030629)
    ·
      refine ⟨879152940670771437005743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4688815683577447664030629 879152940670771437005743)
      ·
        refine ⟨1318729411006157155508615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879152940670771437005743 1318729411006157155508615)
        ·
          refine ⟨1978094116509235733262923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318729411006157155508615 1978094116509235733262923)
          ·
            refine ⟨2967141174763853599894385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978094116509235733262923 2967141174763853599894385)
            ·
              refine ⟨2225355881072890199920789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967141174763853599894385 2225355881072890199920789)
              ·
                refine ⟨104313556925291728121287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2225355881072890199920789 104313556925291728121287)
                ·
                  rfl

theorem cell21_1371262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1371262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371262 prefixEnd_1371262 := by exact prefixLift 1371262
  have htrace : WordTrace (prefixWord ++ tailWord_1371262) baseStart_1371262 baseEnd_1371262 := by
    simpa [prefixWord, tailWord_1371262, baseEnd_1371262] using wordTrace_append hprefix tailTrace_1371262
  have hstable : (prefixWord ++ tailWord_1371262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371262).length < 2 ^ (prefixWord ++ tailWord_1371262).sum := by decide
  have hdescent : baseEnd_1371262 < baseStart_1371262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371273 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 4]
def baseStart_1371273 : Nat := 118140960795 + 1371273 * 2 ^ 59
def prefixEnd_1371273 : Nat := 4983230072969 + 3 ^ 40 * 1371273 * 2
def baseEnd_1371273 : Nat := 312943181125741609680505

theorem tailTrace_1371273 : CollatzResearch.WordTrace tailWord_1371273 prefixEnd_1371273 312943181125741609680505 := by
  unfold tailWord_1371273
  simp only [CollatzResearch.WordTrace]
  refine ⟨50014435161119590628310473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33342956774079727085540315 50014435161119590628310473)
  ·
    refine ⟨37510826370839692971232855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50014435161119590628310473 37510826370839692971232855)
    ·
      refine ⟨56266239556259539456849283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37510826370839692971232855 56266239556259539456849283)
      ·
        refine ⟨84399359334389309185273925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56266239556259539456849283 84399359334389309185273925)
        ·
          refine ⟨15824879875197995472238861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84399359334389309185273925 15824879875197995472238861)
          ·
            refine ⟨5934329953199248302089573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15824879875197995472238861 5934329953199248302089573)
            ·
              refine ⟨1112686866224859056641795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5934329953199248302089573 1112686866224859056641795)
              ·
                refine ⟨1669030299337288584962693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112686866224859056641795 1669030299337288584962693)
                ·
                  refine ⟨312943181125741609680505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669030299337288584962693 312943181125741609680505)
                  ·
                    rfl

theorem cell21_1371273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_1371273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371273 prefixEnd_1371273 := by exact prefixLift 1371273
  have htrace : WordTrace (prefixWord ++ tailWord_1371273) baseStart_1371273 baseEnd_1371273 := by
    simpa [prefixWord, tailWord_1371273, baseEnd_1371273] using wordTrace_append hprefix tailTrace_1371273
  have hstable : (prefixWord ++ tailWord_1371273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371273).length < 2 ^ (prefixWord ++ tailWord_1371273).sum := by decide
  have hdescent : baseEnd_1371273 < baseStart_1371273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371315 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_1371315 : Nat := 118140960795 + 1371315 * 2 ^ 59
def prefixEnd_1371315 : Nat := 4983230072969 + 3 ^ 40 * 1371315 * 2
def baseEnd_1371315 : Nat := 312952766097958869980419

theorem tailTrace_1371315 : CollatzResearch.WordTrace tailWord_1371315 prefixEnd_1371315 312952766097958869980419 := by
  unfold tailWord_1371315
  simp only [CollatzResearch.WordTrace]
  refine ⟨50015967026967431801339399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33343978017978287867559599 50015967026967431801339399)
  ·
    refine ⟨75023950540451147702009099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50015967026967431801339399 75023950540451147702009099)
    ·
      refine ⟨112535925810676721553013649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75023950540451147702009099 112535925810676721553013649)
      ·
        refine ⟨84401944358007541164760237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112535925810676721553013649 84401944358007541164760237)
        ·
          refine ⟨31650729134252827936785089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84401944358007541164760237 31650729134252827936785089)
          ·
            refine ⟨23738046850689620952588817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31650729134252827936785089 23738046850689620952588817)
            ·
              refine ⟨17803535138017215714441613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23738046850689620952588817 17803535138017215714441613)
              ·
                refine ⟨6676325676756455892915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17803535138017215714441613 6676325676756455892915605)
                ·
                  refine ⟨312952766097958869980419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6676325676756455892915605 312952766097958869980419)
                  ·
                    rfl

theorem cell21_1371315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_1371315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371315 prefixEnd_1371315 := by exact prefixLift 1371315
  have htrace : WordTrace (prefixWord ++ tailWord_1371315) baseStart_1371315 baseEnd_1371315 := by
    simpa [prefixWord, tailWord_1371315, baseEnd_1371315] using wordTrace_append hprefix tailTrace_1371315
  have hstable : (prefixWord ++ tailWord_1371315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371315).length < 2 ^ (prefixWord ++ tailWord_1371315).sum := by decide
  have hdescent : baseEnd_1371315 < baseStart_1371315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371442 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1371442 : Nat := 118140960795 + 1371442 * 2 ^ 59
def prefixEnd_1371442 : Nat := 4983230072969 + 3 ^ 40 * 1371442 * 2
def baseEnd_1371442 : Nat := 312981749228234871363493

theorem tailTrace_1371442 : CollatzResearch.WordTrace tailWord_1371442 prefixEnd_1371442 312981749228234871363493 := by
  unfold tailWord_1371442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505149774376833122803145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33347066065004888327475053 12505149774376833122803145)
  ·
    refine ⟨9378862330782624842102359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12505149774376833122803145 9378862330782624842102359)
    ·
      refine ⟨14068293496173937263153539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9378862330782624842102359 14068293496173937263153539)
      ·
        refine ⟨21102440244260905894730309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14068293496173937263153539 21102440244260905894730309)
        ·
          refine ⟨3956707545798919855261933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21102440244260905894730309 3956707545798919855261933)
          ·
            refine ⟨1483765329674594945723225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3956707545798919855261933 1483765329674594945723225)
            ·
              refine ⟨1112823997255946209292419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483765329674594945723225 1112823997255946209292419)
              ·
                refine ⟨1669235995883919313938629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112823997255946209292419 1669235995883919313938629)
                ·
                  refine ⟨312981749228234871363493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669235995883919313938629 312981749228234871363493)
                  ·
                    rfl

theorem cell21_1371442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1371442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371442 prefixEnd_1371442 := by exact prefixLift 1371442
  have htrace : WordTrace (prefixWord ++ tailWord_1371442) baseStart_1371442 baseEnd_1371442 := by
    simpa [prefixWord, tailWord_1371442, baseEnd_1371442] using wordTrace_append hprefix tailTrace_1371442
  have hstable : (prefixWord ++ tailWord_1371442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371442).length < 2 ^ (prefixWord ++ tailWord_1371442).sum := by decide
  have hdescent : baseEnd_1371442 < baseStart_1371442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371470 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_1371470 : Nat := 118140960795 + 1371470 * 2 ^ 59
def prefixEnd_1371470 : Nat := 4983230072969 + 3 ^ 40 * 1371470 * 2
def baseEnd_1371470 : Nat := 312988139209713044896769

theorem tailTrace_1371470 : CollatzResearch.WordTrace tailWord_1371470 prefixEnd_1371470 312988139209713044896769 := by
  unfold tailWord_1371470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252702542675736659153983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33347746894270595515487909 6252702542675736659153983)
  ·
    refine ⟨9379053814013604988730975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252702542675736659153983 9379053814013604988730975)
    ·
      refine ⟨14068580721020407483096463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379053814013604988730975 14068580721020407483096463)
      ·
        refine ⟨21102871081530611224644695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14068580721020407483096463 21102871081530611224644695)
        ·
          refine ⟨31654306622295916836967043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21102871081530611224644695 31654306622295916836967043)
          ·
            refine ⟨47481459933443875255450565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31654306622295916836967043 47481459933443875255450565)
            ·
              refine ⟨8902773737520726610396981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47481459933443875255450565 8902773737520726610396981)
              ·
                refine ⟨834635037892568119724717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8902773737520726610396981 834635037892568119724717)
                ·
                  refine ⟨312988139209713044896769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834635037892568119724717 312988139209713044896769)
                  ·
                    rfl

theorem cell21_1371470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_1371470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371470 prefixEnd_1371470 := by exact prefixLift 1371470
  have htrace : WordTrace (prefixWord ++ tailWord_1371470) baseStart_1371470 baseEnd_1371470 := by
    simpa [prefixWord, tailWord_1371470, baseEnd_1371470] using wordTrace_append hprefix tailTrace_1371470
  have hstable : (prefixWord ++ tailWord_1371470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371470).length < 2 ^ (prefixWord ++ tailWord_1371470).sum := by decide
  have hdescent : baseEnd_1371470 < baseStart_1371470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371546 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_1371546 : Nat := 118140960795 + 1371546 * 2 ^ 59
def prefixEnd_1371546 : Nat := 4983230072969 + 3 ^ 40 * 1371546 * 2
def baseEnd_1371546 : Nat := 313005483445153801629947

theorem tailTrace_1371546 : CollatzResearch.WordTrace tailWord_1371546 prefixEnd_1371546 313005483445153801629947 := by
  unfold tailWord_1371546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506098072282639563249623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33349594859420372168665661 12506098072282639563249623)
  ·
    refine ⟨18759147108423959344874435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12506098072282639563249623 18759147108423959344874435)
    ·
      refine ⟨28138720662635939017311653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18759147108423959344874435 28138720662635939017311653)
      ·
        refine ⟨5276010124244238565745935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28138720662635939017311653 5276010124244238565745935)
        ·
          refine ⟨7914015186366357848618903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276010124244238565745935 7914015186366357848618903)
          ·
            refine ⟨11871022779549536772928355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914015186366357848618903 11871022779549536772928355)
            ·
              refine ⟨17806534169324305159392533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871022779549536772928355 17806534169324305159392533)
              ·
                refine ⟨834681289187076804346525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17806534169324305159392533 834681289187076804346525)
                ·
                  refine ⟨313005483445153801629947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834681289187076804346525 313005483445153801629947)
                  ·
                    rfl

theorem cell21_1371546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_1371546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371546 prefixEnd_1371546 := by exact prefixLift 1371546
  have htrace : WordTrace (prefixWord ++ tailWord_1371546) baseStart_1371546 baseEnd_1371546 := by
    simpa [prefixWord, tailWord_1371546, baseEnd_1371546] using wordTrace_append hprefix tailTrace_1371546
  have hstable : (prefixWord ++ tailWord_1371546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371546).length < 2 ^ (prefixWord ++ tailWord_1371546).sum := by decide
  have hdescent : baseEnd_1371546 < baseStart_1371546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371580 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1371580 : Nat := 118140960795 + 1371580 * 2 ^ 59
def prefixEnd_1371580 : Nat := 4983230072969 + 3 ^ 40 * 1371580 * 2
def baseEnd_1371580 : Nat := 313013242708377298063211

theorem tailTrace_1371580 : CollatzResearch.WordTrace tailWord_1371580 prefixEnd_1371580 313013242708377298063211 := by
  unfold tailWord_1371580
  simp only [CollatzResearch.WordTrace]
  refine ⟨25012816185503691029868097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33350421580671588039824129 25012816185503691029868097)
  ·
    refine ⟨18759612139127768272401073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25012816185503691029868097 18759612139127768272401073)
    ·
      refine ⟨14069709104345826204300805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18759612139127768272401073 14069709104345826204300805)
      ·
        refine ⟨2638070457064842413306401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14069709104345826204300805 2638070457064842413306401)
        ·
          refine ⟨1978552842798631809979801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638070457064842413306401 1978552842798631809979801)
          ·
            refine ⟨1483914632098973857484851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978552842798631809979801 1483914632098973857484851)
            ·
              refine ⟨2225871948148460786227277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483914632098973857484851 2225871948148460786227277)
              ·
                refine ⟨834701980555672794835229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2225871948148460786227277 834701980555672794835229)
                ·
                  refine ⟨313013242708377298063211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834701980555672794835229 313013242708377298063211)
                  ·
                    rfl

theorem cell21_1371580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1371580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371580 prefixEnd_1371580 := by exact prefixLift 1371580
  have htrace : WordTrace (prefixWord ++ tailWord_1371580) baseStart_1371580 baseEnd_1371580 := by
    simpa [prefixWord, tailWord_1371580, baseEnd_1371580] using wordTrace_append hprefix tailTrace_1371580
  have hstable : (prefixWord ++ tailWord_1371580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371580).length < 2 ^ (prefixWord ++ tailWord_1371580).sum := by decide
  have hdescent : baseEnd_1371580 < baseStart_1371580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371681 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_1371681 : Nat := 118140960795 + 1371681 * 2 ^ 59
def prefixEnd_1371681 : Nat := 4983230072969 + 3 ^ 40 * 1371681 * 2
def baseEnd_1371681 : Nat := 313036292284423566879671

theorem tailTrace_1371681 : CollatzResearch.WordTrace tailWord_1371681 prefixEnd_1371681 313036292284423566879671 := by
  unfold tailWord_1371681
  simp only [CollatzResearch.WordTrace]
  refine ⟨50029316143641476309162897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33352877429094317539441931 50029316143641476309162897)
  ·
    refine ⟨37521987107731107231872173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50029316143641476309162897 37521987107731107231872173)
    ·
      refine ⟨14070745165399165211952065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37521987107731107231872173 14070745165399165211952065)
      ·
        refine ⟨10553058874049373908964049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14070745165399165211952065 10553058874049373908964049)
        ·
          refine ⟨7914794155537030431723037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10553058874049373908964049 7914794155537030431723037)
          ·
            refine ⟨2968047808326386411896139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7914794155537030431723037 2968047808326386411896139)
            ·
              refine ⟨4452071712489579617844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968047808326386411896139 4452071712489579617844209)
              ·
                refine ⟨3339053784367184713383157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452071712489579617844209 3339053784367184713383157)
                ·
                  refine ⟨313036292284423566879671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3339053784367184713383157 313036292284423566879671)
                  ·
                    rfl

theorem cell21_1371681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_1371681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371681 prefixEnd_1371681 := by exact prefixLift 1371681
  have htrace : WordTrace (prefixWord ++ tailWord_1371681) baseStart_1371681 baseEnd_1371681 := by
    simpa [prefixWord, tailWord_1371681, baseEnd_1371681] using wordTrace_append hprefix tailTrace_1371681
  have hstable : (prefixWord ++ tailWord_1371681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371681).length < 2 ^ (prefixWord ++ tailWord_1371681).sum := by decide
  have hdescent : baseEnd_1371681 < baseStart_1371681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371771 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_1371771 : Nat := 118140960795 + 1371771 * 2 ^ 59
def prefixEnd_1371771 : Nat := 4983230072969 + 3 ^ 40 * 1371771 * 2
def baseEnd_1371771 : Nat := 313056831510603410379487

theorem tailTrace_1371771 : CollatzResearch.WordTrace tailWord_1371771 prefixEnd_1371771 313056831510603410379487 := by
  unfold tailWord_1371771
  simp only [CollatzResearch.WordTrace]
  refine ⟨50032598713315421679939167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33355065808876947786626111 50032598713315421679939167)
  ·
    refine ⟨75048898069973132519908751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50032598713315421679939167 75048898069973132519908751)
    ·
      refine ⟨112573347104959698779863127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75048898069973132519908751 112573347104959698779863127)
      ·
        refine ⟨168860020657439548169794691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112573347104959698779863127 168860020657439548169794691)
        ·
          refine ⟨253290030986159322254692037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168860020657439548169794691 253290030986159322254692037)
          ·
            refine ⟨47491880809904872922754757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253290030986159322254692037 47491880809904872922754757)
            ·
              refine ⟨8904727651857163673016517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47491880809904872922754757 8904727651857163673016517)
              ·
                refine ⟨1669636434723218188690597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8904727651857163673016517 1669636434723218188690597)
                ·
                  refine ⟨313056831510603410379487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669636434723218188690597 313056831510603410379487)
                  ·
                    rfl

theorem cell21_1371771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_1371771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371771 prefixEnd_1371771 := by exact prefixLift 1371771
  have htrace : WordTrace (prefixWord ++ tailWord_1371771) baseStart_1371771 baseEnd_1371771 := by
    simpa [prefixWord, tailWord_1371771, baseEnd_1371771] using wordTrace_append hprefix tailTrace_1371771
  have hstable : (prefixWord ++ tailWord_1371771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371771).length < 2 ^ (prefixWord ++ tailWord_1371771).sum := by decide
  have hdescent : baseEnd_1371771 < baseStart_1371771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371785 : List Nat := [1, 2, 1, 1, 4, 1, 3, 8]
def baseStart_1371785 : Nat := 118140960795 + 1371785 * 2 ^ 59
def prefixEnd_1371785 : Nat := 4983230072969 + 3 ^ 40 * 1371785 * 2
def baseEnd_1371785 : Nat := 104353342167114165715375

theorem tailTrace_1371785 : CollatzResearch.WordTrace tailWord_1371785 prefixEnd_1371785 104353342167114165715375 := by
  unfold tailWord_1371785
  simp only [CollatzResearch.WordTrace]
  refine ⟨50033109335264702070948809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33355406223509801380632539 50033109335264702070948809)
  ·
    refine ⟨37524832001448526553211607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50033109335264702070948809 37524832001448526553211607)
    ·
      refine ⟨56287248002172789829817411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37524832001448526553211607 56287248002172789829817411)
      ·
        refine ⟨84430872003259184744726117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56287248002172789829817411 84430872003259184744726117)
        ·
          refine ⟨15830788500611097139636147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84430872003259184744726117 15830788500611097139636147)
          ·
            refine ⟨23746182750916645709454221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15830788500611097139636147 23746182750916645709454221)
            ·
              refine ⟨8904818531593742141045333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23746182750916645709454221 8904818531593742141045333)
              ·
                refine ⟨104353342167114165715375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8904818531593742141045333 104353342167114165715375)
                ·
                  rfl

theorem cell21_1371785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_1371785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371785 prefixEnd_1371785 := by exact prefixLift 1371785
  have htrace : WordTrace (prefixWord ++ tailWord_1371785) baseStart_1371785 baseEnd_1371785 := by
    simpa [prefixWord, tailWord_1371785, baseEnd_1371785] using wordTrace_append hprefix tailTrace_1371785
  have hstable : (prefixWord ++ tailWord_1371785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371785).length < 2 ^ (prefixWord ++ tailWord_1371785).sum := by decide
  have hdescent : baseEnd_1371785 < baseStart_1371785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371822 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1371822 : Nat := 118140960795 + 1371822 * 2 ^ 59
def prefixEnd_1371822 : Nat := 4983230072969 + 3 ^ 40 * 1371822 * 2
def baseEnd_1371822 : Nat := 313068470405438655029383

theorem tailTrace_1371822 : CollatzResearch.WordTrace tailWord_1371822 prefixEnd_1371822 313068470405438655029383 := by
  unfold tailWord_1371822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254307354516332173755715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33356305890753771593363813 6254307354516332173755715)
  ·
    refine ⟨9381461031774498260633573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254307354516332173755715 9381461031774498260633573)
    ·
      refine ⟨1759023943457718423868795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9381461031774498260633573 1759023943457718423868795)
      ·
        refine ⟨2638535915186577635803193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759023943457718423868795 2638535915186577635803193)
        ·
          refine ⟨1978901936389933226852395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638535915186577635803193 1978901936389933226852395)
          ·
            refine ⟨2968352904584899840278593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978901936389933226852395 2968352904584899840278593)
            ·
              refine ⟨2226264678438674880208945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968352904584899840278593 2226264678438674880208945)
              ·
                refine ⟨1669698508829006160156709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226264678438674880208945 1669698508829006160156709)
                ·
                  refine ⟨313068470405438655029383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669698508829006160156709 313068470405438655029383)
                  ·
                    rfl

theorem cell21_1371822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1371822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371822 prefixEnd_1371822 := by exact prefixLift 1371822
  have htrace : WordTrace (prefixWord ++ tailWord_1371822) baseStart_1371822 baseEnd_1371822 := by
    simpa [prefixWord, tailWord_1371822, baseEnd_1371822] using wordTrace_append hprefix tailTrace_1371822
  have hstable : (prefixWord ++ tailWord_1371822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371822).length < 2 ^ (prefixWord ++ tailWord_1371822).sum := by decide
  have hdescent : baseEnd_1371822 < baseStart_1371822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371847 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_1371847 : Nat := 118140960795 + 1371847 * 2 ^ 59
def prefixEnd_1371847 : Nat := 4983230072969 + 3 ^ 40 * 1371847 * 2
def baseEnd_1371847 : Nat := 313074175746044167112665

theorem tailTrace_1371847 : CollatzResearch.WordTrace tailWord_1371847 prefixEnd_1371847 313074175746044167112665 := by
  unfold tailWord_1371847
  simp only [CollatzResearch.WordTrace]
  refine ⟨50035370661040086659705795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33356913774026724439803863 50035370661040086659705795)
  ·
    refine ⟨75053055991560129989558693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50035370661040086659705795 75053055991560129989558693)
    ·
      refine ⟨14072447998417524373042255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75053055991560129989558693 14072447998417524373042255)
      ·
        refine ⟨21108671997626286559563383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072447998417524373042255 21108671997626286559563383)
        ·
          refine ⟨31663007996439429839345075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21108671997626286559563383 31663007996439429839345075)
          ·
            refine ⟨47494511994659144759017613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31663007996439429839345075 47494511994659144759017613)
            ·
              refine ⟨17810441997997179284631605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47494511994659144759017613 17810441997997179284631605)
              ·
                refine ⟨1669728937312235557934213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17810441997997179284631605 1669728937312235557934213)
                ·
                  refine ⟨313074175746044167112665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669728937312235557934213 313074175746044167112665)
                  ·
                    rfl

theorem cell21_1371847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_1371847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371847 prefixEnd_1371847 := by exact prefixLift 1371847
  have htrace : WordTrace (prefixWord ++ tailWord_1371847) baseStart_1371847 baseEnd_1371847 := by
    simpa [prefixWord, tailWord_1371847, baseEnd_1371847] using wordTrace_append hprefix tailTrace_1371847
  have hstable : (prefixWord ++ tailWord_1371847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371847).length < 2 ^ (prefixWord ++ tailWord_1371847).sum := by decide
  have hdescent : baseEnd_1371847 < baseStart_1371847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371937 : List Nat := [1, 2, 3, 2, 1, 3, 9]
def baseStart_1371937 : Nat := 118140960795 + 1371937 * 2 ^ 59
def prefixEnd_1371937 : Nat := 4983230072969 + 3 ^ 40 * 1371937 * 2
def baseEnd_1371937 : Nat := 34788301663580445623609

theorem tailTrace_1371937 : CollatzResearch.WordTrace tailWord_1371937 prefixEnd_1371937 34788301663580445623609 := by
  unfold tailWord_1371937
  simp only [CollatzResearch.WordTrace]
  refine ⟨50038653230714032030482065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33359102153809354686988043 50038653230714032030482065)
  ·
    refine ⟨37528989923035524022861549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50038653230714032030482065 37528989923035524022861549)
    ·
      refine ⟨14073371221138321508573081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37528989923035524022861549 14073371221138321508573081)
      ·
        refine ⟨10555028415853741131429811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14073371221138321508573081 10555028415853741131429811)
        ·
          refine ⟨15832542623780611697144717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10555028415853741131429811 15832542623780611697144717)
          ·
            refine ⟨5937203483917729386429269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15832542623780611697144717 5937203483917729386429269)
            ·
              refine ⟨34788301663580445623609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5937203483917729386429269 34788301663580445623609)
              ·
                rfl

theorem cell21_1371937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 9].length) (baseStart_1371937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371937 prefixEnd_1371937 := by exact prefixLift 1371937
  have htrace : WordTrace (prefixWord ++ tailWord_1371937) baseStart_1371937 baseEnd_1371937 := by
    simpa [prefixWord, tailWord_1371937, baseEnd_1371937] using wordTrace_append hprefix tailTrace_1371937
  have hstable : (prefixWord ++ tailWord_1371937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371937).length < 2 ^ (prefixWord ++ tailWord_1371937).sum := by decide
  have hdescent : baseEnd_1371937 < baseStart_1371937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371954 : List Nat := [3, 2, 1, 1, 3, 3, 2, 6]
def baseStart_1371954 : Nat := 118140960795 + 1371954 * 2 ^ 59
def prefixEnd_1371954 : Nat := 4983230072969 + 3 ^ 40 * 1371954 * 2
def baseEnd_1371954 : Nat := 104366198201278586276371

theorem tailTrace_1371954 : CollatzResearch.WordTrace tailWord_1371954 prefixEnd_1371954 104366198201278586276371 := by
  unfold tailWord_1371954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509818317913110983462729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33359515514434962622567277 12509818317913110983462729)
  ·
    refine ⟨9382363738434833237597047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12509818317913110983462729 9382363738434833237597047)
    ·
      refine ⟨14073545607652249856395571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9382363738434833237597047 14073545607652249856395571)
      ·
        refine ⟨21110318411478374784593357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073545607652249856395571 21110318411478374784593357)
        ·
          refine ⟨7916369404304390544222509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21110318411478374784593357 7916369404304390544222509)
          ·
            refine ⟨2968638526614146454083441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7916369404304390544222509 2968638526614146454083441)
            ·
              refine ⟨2226478894960609840562581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968638526614146454083441 2226478894960609840562581)
              ·
                refine ⟨104366198201278586276371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2226478894960609840562581 104366198201278586276371)
                ·
                  rfl

theorem cell21_1371954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_1371954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371954 prefixEnd_1371954 := by exact prefixLift 1371954
  have htrace : WordTrace (prefixWord ++ tailWord_1371954) baseStart_1371954 baseEnd_1371954 := by
    simpa [prefixWord, tailWord_1371954, baseEnd_1371954] using wordTrace_append hprefix tailTrace_1371954
  have hstable : (prefixWord ++ tailWord_1371954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371954).length < 2 ^ (prefixWord ++ tailWord_1371954).sum := by decide
  have hdescent : baseEnd_1371954 < baseStart_1371954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371999 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_1371999 : Nat := 118140960795 + 1371999 * 2 ^ 59
def prefixEnd_1371999 : Nat := 4983230072969 + 3 ^ 40 * 1371999 * 2
def baseEnd_1371999 : Nat := 313108864216925680579021

theorem tailTrace_1371999 : CollatzResearch.WordTrace tailWord_1371999 prefixEnd_1371999 313108864216925680579021 := by
  unfold tailWord_1371999
  simp only [CollatzResearch.WordTrace]
  refine ⟨50040914556489416619239051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33360609704326277746159367 50040914556489416619239051)
  ·
    refine ⟨75061371834734124928858577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50040914556489416619239051 75061371834734124928858577)
    ·
      refine ⟨56296028876050593696643933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75061371834734124928858577 56296028876050593696643933)
      ·
        refine ⟨21111010828518972636241475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56296028876050593696643933 21111010828518972636241475)
        ·
          refine ⟨31666516242778458954362213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21111010828518972636241475 31666516242778458954362213)
          ·
            refine ⟨5937471795520961053942915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31666516242778458954362213 5937471795520961053942915)
            ·
              refine ⟨8906207693281441580914373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937471795520961053942915 8906207693281441580914373)
              ·
                refine ⟨1669913942490270296421445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8906207693281441580914373 1669913942490270296421445)
                ·
                  refine ⟨313108864216925680579021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669913942490270296421445 313108864216925680579021)
                  ·
                    rfl

theorem cell21_1371999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_1371999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1371999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1371999 prefixEnd_1371999 := by exact prefixLift 1371999
  have htrace : WordTrace (prefixWord ++ tailWord_1371999) baseStart_1371999 baseEnd_1371999 := by
    simpa [prefixWord, tailWord_1371999, baseEnd_1371999] using wordTrace_append hprefix tailTrace_1371999
  have hstable : (prefixWord ++ tailWord_1371999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371999).length < 2 ^ (prefixWord ++ tailWord_1371999).sum := by decide
  have hdescent : baseEnd_1371999 < baseStart_1371999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372061 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1372061 : Nat := 118140960795 + 1372061 * 2 ^ 59
def prefixEnd_1372061 : Nat := 4983230072969 + 3 ^ 40 * 1372061 * 2
def baseEnd_1372061 : Nat := 313123013461627350545561

theorem tailTrace_1372061 : CollatzResearch.WordTrace tailWord_1372061 prefixEnd_1372061 313123013461627350545561 := by
  unfold tailWord_1372061
  simp only [CollatzResearch.WordTrace]
  refine ⟨50043175882264801207996037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33362117254843200805330691 50043175882264801207996037)
  ·
    refine ⟨9383095477924650226499257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50043175882264801207996037 9383095477924650226499257)
    ·
      refine ⟨7037321608443487669874443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9383095477924650226499257 7037321608443487669874443)
      ·
        refine ⟨10555982412665231504811665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037321608443487669874443 10555982412665231504811665)
        ·
          refine ⟨7916986809498923628608749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10555982412665231504811665 7916986809498923628608749)
          ·
            refine ⟨2968870053562096360728281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7916986809498923628608749 2968870053562096360728281)
            ·
              refine ⟨2226652540171572270546211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968870053562096360728281 2226652540171572270546211)
              ·
                refine ⟨3339978810257358405819317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226652540171572270546211 3339978810257358405819317)
                ·
                  refine ⟨313123013461627350545561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3339978810257358405819317 313123013461627350545561)
                  ·
                    rfl

theorem cell21_1372061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1372061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372061 prefixEnd_1372061 := by exact prefixLift 1372061
  have htrace : WordTrace (prefixWord ++ tailWord_1372061) baseStart_1372061 baseEnd_1372061 := by
    simpa [prefixWord, tailWord_1372061, baseEnd_1372061] using wordTrace_append hprefix tailTrace_1372061
  have hstable : (prefixWord ++ tailWord_1372061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372061).length < 2 ^ (prefixWord ++ tailWord_1372061).sum := by decide
  have hdescent : baseEnd_1372061 < baseStart_1372061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372089 : List Nat := [1, 2, 1, 4, 2, 1, 3, 7]
def baseStart_1372089 : Nat := 118140960795 + 1372089 * 2 ^ 59
def prefixEnd_1372089 : Nat := 4983230072969 + 3 ^ 40 * 1372089 * 2
def baseEnd_1372089 : Nat := 104376467814368508026279

theorem tailTrace_1372089 : CollatzResearch.WordTrace tailWord_1372089 prefixEnd_1372089 104376467814368508026279 := by
  unfold tailWord_1372089
  simp only [CollatzResearch.WordTrace]
  refine ⟨50044197126163361990015321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33362798084108907993343547 50044197126163361990015321)
  ·
    refine ⟨37533147844622521492511491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50044197126163361990015321 37533147844622521492511491)
    ·
      refine ⟨56299721766933782238767237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37533147844622521492511491 56299721766933782238767237)
      ·
        refine ⟨10556197831300084169768857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56299721766933782238767237 10556197831300084169768857)
        ·
          refine ⟨7917148373475063127326643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10556197831300084169768857 7917148373475063127326643)
          ·
            refine ⟨11875722560212594690989965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917148373475063127326643 11875722560212594690989965)
            ·
              refine ⟨4453395960079723009121237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11875722560212594690989965 4453395960079723009121237)
              ·
                refine ⟨104376467814368508026279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4453395960079723009121237 104376467814368508026279)
                ·
                  rfl

theorem cell21_1372089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_1372089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372089 prefixEnd_1372089 := by exact prefixLift 1372089
  have htrace : WordTrace (prefixWord ++ tailWord_1372089) baseStart_1372089 baseEnd_1372089 := by
    simpa [prefixWord, tailWord_1372089, baseEnd_1372089] using wordTrace_append hprefix tailTrace_1372089
  have hstable : (prefixWord ++ tailWord_1372089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372089).length < 2 ^ (prefixWord ++ tailWord_1372089).sum := by decide
  have hdescent : baseEnd_1372089 < baseStart_1372089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372213 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1372213 : Nat := 118140960795 + 1372213 * 2 ^ 59
def prefixEnd_1372213 : Nat := 4983230072969 + 3 ^ 40 * 1372213 * 2
def baseEnd_1372213 : Nat := 313157701932508864011917

theorem tailTrace_1372213 : CollatzResearch.WordTrace tailWord_1372213 prefixEnd_1372213 313157701932508864011917 := by
  unfold tailWord_1372213
  simp only [CollatzResearch.WordTrace]
  refine ⟨50048719777714131167529293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33365813185142754111686195 50048719777714131167529293)
  ·
    refine ⟨18768269916642799187823485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50048719777714131167529293 18768269916642799187823485)
    ·
      refine ⟨7038101218741049695433807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18768269916642799187823485 7038101218741049695433807)
      ·
        refine ⟨10557151828111574543150711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038101218741049695433807 10557151828111574543150711)
        ·
          refine ⟨15835727742167361814726067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557151828111574543150711 15835727742167361814726067)
          ·
            refine ⟨23753591613251042722089101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835727742167361814726067 23753591613251042722089101)
            ·
              refine ⟨8907596854969141020783413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23753591613251042722089101 8907596854969141020783413)
              ·
                refine ⟨835087205153356970698445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8907596854969141020783413 835087205153356970698445)
                ·
                  refine ⟨313157701932508864011917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835087205153356970698445 313157701932508864011917)
                  ·
                    rfl

theorem cell21_1372213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1372213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372213 prefixEnd_1372213 := by exact prefixLift 1372213
  have htrace : WordTrace (prefixWord ++ tailWord_1372213) baseStart_1372213 baseEnd_1372213 := by
    simpa [prefixWord, tailWord_1372213, baseEnd_1372213] using wordTrace_append hprefix tailTrace_1372213
  have hstable : (prefixWord ++ tailWord_1372213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372213).length < 2 ^ (prefixWord ++ tailWord_1372213).sum := by decide
  have hdescent : baseEnd_1372213 < baseStart_1372213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372230 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1372230 : Nat := 118140960795 + 1372230 * 2 ^ 59
def prefixEnd_1372230 : Nat := 4983230072969 + 3 ^ 40 * 1372230 * 2
def baseEnd_1372230 : Nat := 313161581564120612228549

theorem tailTrace_1372230 : CollatzResearch.WordTrace tailWord_1372230 prefixEnd_1372230 313161581564120612228549 := by
  unfold tailWord_1372230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564041869332891970965567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33366226545768362047265429 1564041869332891970965567)
  ·
    refine ⟨2346062803999337956448351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564041869332891970965567 2346062803999337956448351)
    ·
      refine ⟨3519094205999006934672527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346062803999337956448351 3519094205999006934672527)
      ·
        refine ⟨5278641308998510402008791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519094205999006934672527 5278641308998510402008791)
        ·
          refine ⟨7917961963497765603013187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278641308998510402008791 7917961963497765603013187)
          ·
            refine ⟨11876942945246648404519781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917961963497765603013187 11876942945246648404519781)
            ·
              refine ⟨2226926802233746575847459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11876942945246648404519781 2226926802233746575847459)
              ·
                refine ⟨3340390203350619863771189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226926802233746575847459 3340390203350619863771189)
                ·
                  refine ⟨313161581564120612228549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340390203350619863771189 313161581564120612228549)
                  ·
                    rfl

theorem cell21_1372230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1372230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372230 prefixEnd_1372230 := by exact prefixLift 1372230
  have htrace : WordTrace (prefixWord ++ tailWord_1372230) baseStart_1372230 baseEnd_1372230 := by
    simpa [prefixWord, tailWord_1372230, baseEnd_1372230] using wordTrace_append hprefix tailTrace_1372230
  have hstable : (prefixWord ++ tailWord_1372230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372230).length < 2 ^ (prefixWord ++ tailWord_1372230).sum := by decide
  have hdescent : baseEnd_1372230 < baseStart_1372230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372255 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_1372255 : Nat := 118140960795 + 1372255 * 2 ^ 59
def prefixEnd_1372255 : Nat := 4983230072969 + 3 ^ 40 * 1372255 * 2
def baseEnd_1372255 : Nat := 313167286904726124311831

theorem tailTrace_1372255 : CollatzResearch.WordTrace tailWord_1372255 prefixEnd_1372255 313167286904726124311831 := by
  unfold tailWord_1372255
  simp only [CollatzResearch.WordTrace]
  refine ⟨50050251643561972340558219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33366834429041314893705479 50050251643561972340558219)
  ·
    refine ⟨75075377465342958510837329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50050251643561972340558219 75075377465342958510837329)
    ·
      refine ⟨56306533099007218883127997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75075377465342958510837329 56306533099007218883127997)
      ·
        refine ⟨21114949912127707081172999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56306533099007218883127997 21114949912127707081172999)
        ·
          refine ⟨31672424868191560621759499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21114949912127707081172999 31672424868191560621759499)
          ·
            refine ⟨47508637302287340932639249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31672424868191560621759499 47508637302287340932639249)
            ·
              refine ⟨35631477976715505699479437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47508637302287340932639249 35631477976715505699479437)
              ·
                refine ⟨13361804241268314637304789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35631477976715505699479437 13361804241268314637304789)
                ·
                  refine ⟨313167286904726124311831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13361804241268314637304789 313167286904726124311831)
                  ·
                    rfl

theorem cell21_1372255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_1372255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372255 prefixEnd_1372255 := by exact prefixLift 1372255
  have htrace : WordTrace (prefixWord ++ tailWord_1372255) baseStart_1372255 baseEnd_1372255 := by
    simpa [prefixWord, tailWord_1372255, baseEnd_1372255] using wordTrace_append hprefix tailTrace_1372255
  have hstable : (prefixWord ++ tailWord_1372255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372255).length < 2 ^ (prefixWord ++ tailWord_1372255).sum := by decide
  have hdescent : baseEnd_1372255 < baseStart_1372255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372317 : List Nat := [1, 4, 2, 1, 1, 3, 2, 7]
def baseStart_1372317 : Nat := 118140960795 + 1372317 * 2 ^ 59
def prefixEnd_1372317 : Nat := 4983230072969 + 3 ^ 40 * 1372317 * 2
def baseEnd_1372317 : Nat := 104393812049809264759457

theorem tailTrace_1372317 : CollatzResearch.WordTrace tailWord_1372317 prefixEnd_1372317 104393812049809264759457 := by
  unfold tailWord_1372317
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052512969337356929315205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33368341979558237952876803 50052512969337356929315205)
  ·
    refine ⟨9384846181750754424246601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50052512969337356929315205 9384846181750754424246601)
    ·
      refine ⟨7038634636313065818184951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9384846181750754424246601 7038634636313065818184951)
      ·
        refine ⟨10557951954469598727277427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038634636313065818184951 10557951954469598727277427)
        ·
          refine ⟨15836927931704398090916141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557951954469598727277427 15836927931704398090916141)
          ·
            refine ⟨5938847974389149284093553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15836927931704398090916141 5938847974389149284093553)
            ·
              refine ⟨4454135980791861963070165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938847974389149284093553 4454135980791861963070165)
              ·
                refine ⟨104393812049809264759457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4454135980791861963070165 104393812049809264759457)
                ·
                  rfl

theorem cell21_1372317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_1372317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372317 prefixEnd_1372317 := by exact prefixLift 1372317
  have htrace : WordTrace (prefixWord ++ tailWord_1372317) baseStart_1372317 baseEnd_1372317 := by
    simpa [prefixWord, tailWord_1372317, baseEnd_1372317] using wordTrace_append hprefix tailTrace_1372317
  have hstable : (prefixWord ++ tailWord_1372317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372317).length < 2 ^ (prefixWord ++ tailWord_1372317).sum := by decide
  have hdescent : baseEnd_1372317 < baseStart_1372317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372334 : List Nat := [4, 1, 4, 2, 10]
def baseStart_1372334 : Nat := 118140960795 + 1372334 * 2 ^ 59
def prefixEnd_1372334 : Nat := 4983230072969 + 3 ^ 40 * 1372334 * 2
def baseEnd_1372334 : Nat := 3866485380012833857963

theorem tailTrace_1372334 : CollatzResearch.WordTrace tailWord_1372334 prefixEnd_1372334 3866485380012833857963 := by
  unfold tailWord_1372334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256641626284471104085507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33368755340183845888456037 6256641626284471104085507)
  ·
    refine ⟨9384962439426706656128261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256641626284471104085507 9384962439426706656128261)
    ·
      refine ⟨1759680457392507498024049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9384962439426706656128261 1759680457392507498024049)
      ·
        refine ⟨1319760343044380623518037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1759680457392507498024049 1319760343044380623518037)
        ·
          refine ⟨3866485380012833857963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1319760343044380623518037 3866485380012833857963)
          ·
            rfl

theorem cell21_1372334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 10].length) (baseStart_1372334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372334 prefixEnd_1372334 := by exact prefixLift 1372334
  have htrace : WordTrace (prefixWord ++ tailWord_1372334) baseStart_1372334 baseEnd_1372334 := by
    simpa [prefixWord, tailWord_1372334, baseEnd_1372334] using wordTrace_append hprefix tailTrace_1372334
  have hstable : (prefixWord ++ tailWord_1372334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372334).length < 2 ^ (prefixWord ++ tailWord_1372334).sum := by decide
  have hdescent : baseEnd_1372334 < baseStart_1372334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372424 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_1372424 : Nat := 118140960795 + 1372424 * 2 ^ 59
def prefixEnd_1372424 : Nat := 4983230072969 + 3 ^ 40 * 1372424 * 2
def baseEnd_1372424 : Nat := 313205855007219385994819

theorem tailTrace_1372424 : CollatzResearch.WordTrace tailWord_1372424 prefixEnd_1372424 313205855007219385994819 := by
  unfold tailWord_1372424
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028207789974857101730163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33370943719966476135640217 25028207789974857101730163)
  ·
    refine ⟨37542311684962285652595245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25028207789974857101730163 37542311684962285652595245)
    ·
      refine ⟨14078366881860857119723217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37542311684962285652595245 14078366881860857119723217)
      ·
        refine ⟨10558775161395642839792413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14078366881860857119723217 10558775161395642839792413)
        ·
          refine ⟨3959540685523366064922155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10558775161395642839792413 3959540685523366064922155)
          ·
            refine ⟨5939311028285049097383233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959540685523366064922155 5939311028285049097383233)
            ·
              refine ⟨4454483271213786823037425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939311028285049097383233 4454483271213786823037425)
              ·
                refine ⟨3340862453410340117278069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454483271213786823037425 3340862453410340117278069)
                ·
                  refine ⟨313205855007219385994819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340862453410340117278069 313205855007219385994819)
                  ·
                    rfl

theorem cell21_1372424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_1372424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372424 prefixEnd_1372424 := by exact prefixLift 1372424
  have htrace : WordTrace (prefixWord ++ tailWord_1372424) baseStart_1372424 baseEnd_1372424 := by
    simpa [prefixWord, tailWord_1372424, baseEnd_1372424] using wordTrace_append hprefix tailTrace_1372424
  have hstable : (prefixWord ++ tailWord_1372424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372424).length < 2 ^ (prefixWord ++ tailWord_1372424).sum := by decide
  have hdescent : baseEnd_1372424 < baseStart_1372424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372458 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1372458 : Nat := 118140960795 + 1372458 * 2 ^ 59
def prefixEnd_1372458 : Nat := 4983230072969 + 3 ^ 40 * 1372458 * 2
def baseEnd_1372458 : Nat := 313213614270442882428083

theorem tailTrace_1372458 : CollatzResearch.WordTrace tailWord_1372458 prefixEnd_1372458 313213614270442882428083 := by
  unfold tailWord_1372458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514413915456634502549507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33371770441217692006798685 12514413915456634502549507)
  ·
    refine ⟨18771620873184951753824261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12514413915456634502549507 18771620873184951753824261)
    ·
      refine ⟨3519678913722178453842049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18771620873184951753824261 3519678913722178453842049)
      ·
        refine ⟨2639759185291633840381537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519678913722178453842049 2639759185291633840381537)
        ·
          refine ⟨1979819388968725380286153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639759185291633840381537 1979819388968725380286153)
          ·
            refine ⟨1484864541726544035214615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979819388968725380286153 1484864541726544035214615)
            ·
              refine ⟨2227296812589816052821923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484864541726544035214615 2227296812589816052821923)
              ·
                refine ⟨3340945218884724079232885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227296812589816052821923 3340945218884724079232885)
                ·
                  refine ⟨313213614270442882428083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340945218884724079232885 313213614270442882428083)
                  ·
                    rfl

theorem cell21_1372458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1372458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372458 prefixEnd_1372458 := by exact prefixLift 1372458
  have htrace : WordTrace (prefixWord ++ tailWord_1372458) baseStart_1372458 baseEnd_1372458 := by
    simpa [prefixWord, tailWord_1372458, baseEnd_1372458] using wordTrace_append hprefix tailTrace_1372458
  have hstable : (prefixWord ++ tailWord_1372458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372458).length < 2 ^ (prefixWord ++ tailWord_1372458).sum := by decide
  have hdescent : baseEnd_1372458 < baseStart_1372458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372469 : List Nat := [1, 3, 3, 1, 2, 1, 4, 6]
def baseStart_1372469 : Nat := 118140960795 + 1372469 * 2 ^ 59
def prefixEnd_1372469 : Nat := 4983230072969 + 3 ^ 40 * 1372469 * 2
def baseEnd_1372469 : Nat := 104405374873436435914909

theorem tailTrace_1372469 : CollatzResearch.WordTrace tailWord_1372469 prefixEnd_1372469 104405374873436435914909 := by
  unfold tailWord_1372469
  simp only [CollatzResearch.WordTrace]
  refine ⟨50058056864786686888848461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33372037909857791259232307 50058056864786686888848461)
  ·
    refine ⟨18771771324295007583318173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50058056864786686888848461 18771771324295007583318173)
    ·
      refine ⟨7039414246610627843744315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18771771324295007583318173 7039414246610627843744315)
      ·
        refine ⟨10559121369915941765616473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039414246610627843744315 10559121369915941765616473)
        ·
          refine ⟨7919341027436956324212355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10559121369915941765616473 7919341027436956324212355)
          ·
            refine ⟨11879011541155434486318533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7919341027436956324212355 11879011541155434486318533)
            ·
              refine ⟨2227314663966643966184725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11879011541155434486318533 2227314663966643966184725)
              ·
                refine ⟨104405374873436435914909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2227314663966643966184725 104405374873436435914909)
                ·
                  rfl

theorem cell21_1372469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_1372469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372469 prefixEnd_1372469 := by exact prefixLift 1372469
  have htrace : WordTrace (prefixWord ++ tailWord_1372469) baseStart_1372469 baseEnd_1372469 := by
    simpa [prefixWord, tailWord_1372469, baseEnd_1372469] using wordTrace_append hprefix tailTrace_1372469
  have hstable : (prefixWord ++ tailWord_1372469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372469).length < 2 ^ (prefixWord ++ tailWord_1372469).sum := by decide
  have hdescent : baseEnd_1372469 < baseStart_1372469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372483 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_1372483 : Nat := 118140960795 + 1372483 * 2 ^ 59
def prefixEnd_1372483 : Nat := 4983230072969 + 3 ^ 40 * 1372483 * 2
def baseEnd_1372483 : Nat := 313219319611048394511365

theorem tailTrace_1372483 : CollatzResearch.WordTrace tailWord_1372483 prefixEnd_1372483 313219319611048394511365 := by
  unfold tailWord_1372483
  simp only [CollatzResearch.WordTrace]
  refine ⟨50058567486735967279858103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33372378324490644853238735 50058567486735967279858103)
  ·
    refine ⟨75087851230103950919787155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50058567486735967279858103 75087851230103950919787155)
    ·
      refine ⟨112631776845155926379680733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75087851230103950919787155 112631776845155926379680733)
      ·
        refine ⟨42236916316933472392380275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112631776845155926379680733 42236916316933472392380275)
        ·
          refine ⟨63355374475400208588570413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42236916316933472392380275 63355374475400208588570413)
          ·
            refine ⟨23758265428275078220713905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63355374475400208588570413 23758265428275078220713905)
            ·
              refine ⟨17818699071206308665535429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23758265428275078220713905 17818699071206308665535429)
              ·
                refine ⟨3341006075851182874787893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17818699071206308665535429 3341006075851182874787893)
                ·
                  refine ⟨313219319611048394511365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341006075851182874787893 313219319611048394511365)
                  ·
                    rfl

theorem cell21_1372483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_1372483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372483 prefixEnd_1372483 := by exact prefixLift 1372483
  have htrace : WordTrace (prefixWord ++ tailWord_1372483) baseStart_1372483 baseEnd_1372483 := by
    simpa [prefixWord, tailWord_1372483, baseEnd_1372483] using wordTrace_append hprefix tailTrace_1372483
  have hstable : (prefixWord ++ tailWord_1372483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372483).length < 2 ^ (prefixWord ++ tailWord_1372483).sum := by decide
  have hdescent : baseEnd_1372483 < baseStart_1372483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372517 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 3]
def baseStart_1372517 : Nat := 118140960795 + 1372517 * 2 ^ 59
def prefixEnd_1372517 : Nat := 4983230072969 + 3 ^ 40 * 1372517 * 2
def baseEnd_1372517 : Nat := 313227078874271890944629

theorem tailTrace_1372517 : CollatzResearch.WordTrace tailWord_1372517 prefixEnd_1372517 313227078874271890944629 := by
  unfold tailWord_1372517
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059807568612791086595805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33373205045741860724397203 50059807568612791086595805)
  ·
    refine ⟨18772427838229796657473427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50059807568612791086595805 18772427838229796657473427)
    ·
      refine ⟨28158641757344694986210141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18772427838229796657473427 28158641757344694986210141)
      ·
        refine ⟨10559490659004260619828803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28158641757344694986210141 10559490659004260619828803)
        ·
          refine ⟨15839235988506390929743205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559490659004260619828803 15839235988506390929743205)
          ·
            refine ⟨2969856747844948299326851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15839235988506390929743205 2969856747844948299326851)
            ·
              refine ⟨4454785121767422448990277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969856747844948299326851 4454785121767422448990277)
              ·
                refine ⟨835272210331391709185677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4454785121767422448990277 835272210331391709185677)
                ·
                  refine ⟨313227078874271890944629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835272210331391709185677 313227078874271890944629)
                  ·
                    rfl

theorem cell21_1372517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_1372517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372517 prefixEnd_1372517 := by exact prefixLift 1372517
  have htrace : WordTrace (prefixWord ++ tailWord_1372517) baseStart_1372517 baseEnd_1372517 := by
    simpa [prefixWord, tailWord_1372517, baseEnd_1372517] using wordTrace_append hprefix tailTrace_1372517
  have hstable : (prefixWord ++ tailWord_1372517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372517).length < 2 ^ (prefixWord ++ tailWord_1372517).sum := by decide
  have hdescent : baseEnd_1372517 < baseStart_1372517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372534 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1372534 : Nat := 118140960795 + 1372534 * 2 ^ 59
def prefixEnd_1372534 : Nat := 4983230072969 + 3 ^ 40 * 1372534 * 2
def baseEnd_1372534 : Nat := 313230958505883639161261

theorem tailTrace_1372534 : CollatzResearch.WordTrace tailWord_1372534 prefixEnd_1372534 313230958505883639161261 := by
  unfold tailWord_1372534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128776725596950186872791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33373618406367468659976437 3128776725596950186872791)
  ·
    refine ⟨4693165088395425280309187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128776725596950186872791 4693165088395425280309187)
    ·
      refine ⟨7039747632593137920463781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4693165088395425280309187 7039747632593137920463781)
      ·
        refine ⟨1319952681111213360086959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7039747632593137920463781 1319952681111213360086959)
        ·
          refine ⟨1979929021666820040130439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319952681111213360086959 1979929021666820040130439)
          ·
            refine ⟨2969893532500230060195659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979929021666820040130439 2969893532500230060195659)
            ·
              refine ⟨4454840298750345090293489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969893532500230060195659 4454840298750345090293489)
              ·
                refine ⟨3341130224062758817720117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454840298750345090293489 3341130224062758817720117)
                ·
                  refine ⟨313230958505883639161261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341130224062758817720117 313230958505883639161261)
                  ·
                    rfl

theorem cell21_1372534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1372534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372534 prefixEnd_1372534 := by exact prefixLift 1372534
  have htrace : WordTrace (prefixWord ++ tailWord_1372534) baseStart_1372534 baseEnd_1372534 := by
    simpa [prefixWord, tailWord_1372534, baseEnd_1372534] using wordTrace_append hprefix tailTrace_1372534
  have hstable : (prefixWord ++ tailWord_1372534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372534).length < 2 ^ (prefixWord ++ tailWord_1372534).sum := by decide
  have hdescent : baseEnd_1372534 < baseStart_1372534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372576 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_1372576 : Nat := 118140960795 + 1372576 * 2 ^ 59
def prefixEnd_1372576 : Nat := 4983230072969 + 3 ^ 40 * 1372576 * 2
def baseEnd_1372576 : Nat := 313240543478100899461175

theorem tailTrace_1372576 : CollatzResearch.WordTrace tailWord_1372576 prefixEnd_1372576 313240543478100899461175 := by
  unfold tailWord_1372576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030979737699522081496791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33374639650266029441995721 25030979737699522081496791)
  ·
    refine ⟨37546469606549283122245187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25030979737699522081496791 37546469606549283122245187)
    ·
      refine ⟨56319704409823924683367781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37546469606549283122245187 56319704409823924683367781)
      ·
        refine ⟨10559944576841985878131459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56319704409823924683367781 10559944576841985878131459)
        ·
          refine ⟨15839916865262978817197189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559944576841985878131459 15839916865262978817197189)
          ·
            refine ⟨2969984412236808528224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15839916865262978817197189 2969984412236808528224473)
            ·
              refine ⟨2227488309177606396168355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969984412236808528224473 2227488309177606396168355)
              ·
                refine ⟨3341232463766409594252533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227488309177606396168355 3341232463766409594252533)
                ·
                  refine ⟨313240543478100899461175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341232463766409594252533 313240543478100899461175)
                  ·
                    rfl

theorem cell21_1372576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_1372576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372576 prefixEnd_1372576 := by exact prefixLift 1372576
  have htrace : WordTrace (prefixWord ++ tailWord_1372576) baseStart_1372576 baseEnd_1372576 := by
    simpa [prefixWord, tailWord_1372576, baseEnd_1372576] using wordTrace_append hprefix tailTrace_1372576
  have hstable : (prefixWord ++ tailWord_1372576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372576).length < 2 ^ (prefixWord ++ tailWord_1372576).sum := by decide
  have hdescent : baseEnd_1372576 < baseStart_1372576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372649 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_1372649 : Nat := 118140960795 + 1372649 * 2 ^ 59
def prefixEnd_1372649 : Nat := 4983230072969 + 3 ^ 40 * 1372649 * 2
def baseEnd_1372649 : Nat := 313257203072668994744359

theorem tailTrace_1372649 : CollatzResearch.WordTrace tailWord_1372649 prefixEnd_1372649 313257203072668994744359 := by
  unfold tailWord_1372649
  simp only [CollatzResearch.WordTrace]
  refine ⟨50064622004134577630401001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33376414669423051753600667 50064622004134577630401001)
  ·
    refine ⟨37548466503100933222800751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50064622004134577630401001 37548466503100933222800751)
    ·
      refine ⟨56322699754651399834201127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37548466503100933222800751 56322699754651399834201127)
      ·
        refine ⟨84484049631977099751301691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56322699754651399834201127 84484049631977099751301691)
        ·
          refine ⟨126726074447965649626952537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84484049631977099751301691 126726074447965649626952537)
          ·
            refine ⟨95044555835974237220214403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126726074447965649626952537 95044555835974237220214403)
            ·
              refine ⟨142566833753961355830321605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95044555835974237220214403 142566833753961355830321605)
              ·
                refine ⟨26731281328867754218185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142566833753961355830321605 26731281328867754218185301)
                ·
                  refine ⟨313257203072668994744359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26731281328867754218185301 313257203072668994744359)
                  ·
                    rfl

theorem cell21_1372649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_1372649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372649 prefixEnd_1372649 := by exact prefixLift 1372649
  have htrace : WordTrace (prefixWord ++ tailWord_1372649) baseStart_1372649 baseEnd_1372649 := by
    simpa [prefixWord, tailWord_1372649, baseEnd_1372649] using wordTrace_append hprefix tailTrace_1372649
  have hstable : (prefixWord ++ tailWord_1372649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372649).length < 2 ^ (prefixWord ++ tailWord_1372649).sum := by decide
  have hdescent : baseEnd_1372649 < baseStart_1372649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372683 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_1372683 : Nat := 118140960795 + 1372683 * 2 ^ 59
def prefixEnd_1372683 : Nat := 4983230072969 + 3 ^ 40 * 1372683 * 2
def baseEnd_1372683 : Nat := 313264962335892491177623

theorem tailTrace_1372683 : CollatzResearch.WordTrace tailWord_1372683 prefixEnd_1372683 313264962335892491177623 := by
  unfold tailWord_1372683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50065862086011401437138703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33377241390674267624759135 50065862086011401437138703)
  ·
    refine ⟨75098793129017102155708055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50065862086011401437138703 75098793129017102155708055)
    ·
      refine ⟨112648189693525653233562083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75098793129017102155708055 112648189693525653233562083)
      ·
        refine ⟨168972284540288479850343125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112648189693525653233562083 168972284540288479850343125)
        ·
          refine ⟨3960287918913011246492417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168972284540288479850343125 3960287918913011246492417)
          ·
            refine ⟨2970215939184758434869313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960287918913011246492417 2970215939184758434869313)
            ·
              refine ⟨2227661954388568826151985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970215939184758434869313 2227661954388568826151985)
              ·
                refine ⟨1670746465791426619613989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227661954388568826151985 1670746465791426619613989)
                ·
                  refine ⟨313264962335892491177623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670746465791426619613989 313264962335892491177623)
                  ·
                    rfl

theorem cell21_1372683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_1372683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372683 prefixEnd_1372683 := by exact prefixLift 1372683
  have htrace : WordTrace (prefixWord ++ tailWord_1372683) baseStart_1372683 baseEnd_1372683 := by
    simpa [prefixWord, tailWord_1372683, baseEnd_1372683] using wordTrace_append hprefix tailTrace_1372683
  have hstable : (prefixWord ++ tailWord_1372683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372683).length < 2 ^ (prefixWord ++ tailWord_1372683).sum := by decide
  have hdescent : baseEnd_1372683 < baseStart_1372683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372686 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1372686 : Nat := 118140960795 + 1372686 * 2 ^ 59
def prefixEnd_1372686 : Nat := 4983230072969 + 3 ^ 40 * 1372686 * 2
def baseEnd_1372686 : Nat := 313265646976765152627617

theorem tailTrace_1372686 : CollatzResearch.WordTrace tailWord_1372686 prefixEnd_1372686 313265646976765152627617 := by
  unfold tailWord_1372686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258246438125066618687239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33377314336667021966331941 6258246438125066618687239)
  ·
    refine ⟨9387369657187599928030859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6258246438125066618687239 9387369657187599928030859)
    ·
      refine ⟨14081054485781399892046289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387369657187599928030859 14081054485781399892046289)
      ·
        refine ⟨10560790864336049919034717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14081054485781399892046289 10560790864336049919034717)
        ·
          refine ⟨3960296574126018719638019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10560790864336049919034717 3960296574126018719638019)
          ·
            refine ⟨5940444861189028079457029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960296574126018719638019 5940444861189028079457029)
            ·
              refine ⟨1113833411472942764898193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5940444861189028079457029 1113833411472942764898193)
              ·
                refine ⟨835375058604707073673645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113833411472942764898193 835375058604707073673645)
                ·
                  refine ⟨313265646976765152627617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835375058604707073673645 313265646976765152627617)
                  ·
                    rfl

theorem cell21_1372686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1372686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372686 prefixEnd_1372686 := by exact prefixLift 1372686
  have htrace : WordTrace (prefixWord ++ tailWord_1372686) baseStart_1372686 baseEnd_1372686 := by
    simpa [prefixWord, tailWord_1372686, baseEnd_1372686] using wordTrace_append hprefix tailTrace_1372686
  have hstable : (prefixWord ++ tailWord_1372686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372686).length < 2 ^ (prefixWord ++ tailWord_1372686).sum := by decide
  have hdescent : baseEnd_1372686 < baseStart_1372686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372714 : List Nat := [3, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1372714 : Nat := 118140960795 + 1372714 * 2 ^ 59
def prefixEnd_1372714 : Nat := 4983230072969 + 3 ^ 40 * 1372714 * 2
def baseEnd_1372714 : Nat := 104424012319414442053631

theorem tailTrace_1372714 : CollatzResearch.WordTrace tailWord_1372714 prefixEnd_1372714 104424012319414442053631 := by
  unfold tailWord_1372714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516748187224773432879299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33377995165932729154344797 12516748187224773432879299)
  ·
    refine ⟨18775122280837160149318949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12516748187224773432879299 18775122280837160149318949)
    ·
      refine ⟨3520335427656967527997303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18775122280837160149318949 3520335427656967527997303)
      ·
        refine ⟨5280503141485451291995955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520335427656967527997303 5280503141485451291995955)
        ·
          refine ⟨7920754712228176937993933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280503141485451291995955 7920754712228176937993933)
          ·
            refine ⟨2970283017085566351747725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7920754712228176937993933 2970283017085566351747725)
            ·
              refine ⟨1113856131407087381905397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2970283017085566351747725 1113856131407087381905397)
              ·
                refine ⟨104424012319414442053631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1113856131407087381905397 104424012319414442053631)
                ·
                  rfl

theorem cell21_1372714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1372714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372714 prefixEnd_1372714 := by exact prefixLift 1372714
  have htrace : WordTrace (prefixWord ++ tailWord_1372714) baseStart_1372714 baseEnd_1372714 := by
    simpa [prefixWord, tailWord_1372714, baseEnd_1372714] using wordTrace_append hprefix tailTrace_1372714
  have hstable : (prefixWord ++ tailWord_1372714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372714).length < 2 ^ (prefixWord ++ tailWord_1372714).sum := by decide
  have hdescent : baseEnd_1372714 < baseStart_1372714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372734 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1372734 : Nat := 118140960795 + 1372734 * 2 ^ 59
def prefixEnd_1372734 : Nat := 4983230072969 + 3 ^ 40 * 1372734 * 2
def baseEnd_1372734 : Nat := 313276601230727735827519

theorem tailTrace_1372734 : CollatzResearch.WordTrace tailWord_1372734 prefixEnd_1372734 313276601230727735827519 := by
  unfold tailWord_1372734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258465276103329643405657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33378481472551091431496837 6258465276103329643405657)
  ·
    refine ⟨4693848957077497232554243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6258465276103329643405657 4693848957077497232554243)
    ·
      refine ⟨7040773435616245848831365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4693848957077497232554243 7040773435616245848831365)
      ·
        refine ⟨1320145019178046096655881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7040773435616245848831365 1320145019178046096655881)
        ·
          refine ⟨990108764383534572491911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320145019178046096655881 990108764383534572491911)
          ·
            refine ⟨1485163146575301858737867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990108764383534572491911 1485163146575301858737867)
            ·
              refine ⟨2227744719862952788106801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485163146575301858737867 2227744719862952788106801)
              ·
                refine ⟨1670808539897214591080101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227744719862952788106801 1670808539897214591080101)
                ·
                  refine ⟨313276601230727735827519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670808539897214591080101 313276601230727735827519)
                  ·
                    rfl

theorem cell21_1372734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1372734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372734 prefixEnd_1372734 := by exact prefixLift 1372734
  have htrace : WordTrace (prefixWord ++ tailWord_1372734) baseStart_1372734 baseEnd_1372734 := by
    simpa [prefixWord, tailWord_1372734, baseEnd_1372734] using wordTrace_append hprefix tailTrace_1372734
  have hstable : (prefixWord ++ tailWord_1372734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372734).length < 2 ^ (prefixWord ++ tailWord_1372734).sum := by decide
  have hdescent : baseEnd_1372734 < baseStart_1372734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372759 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 4]
def baseStart_1372759 : Nat := 118140960795 + 1372759 * 2 ^ 59
def prefixEnd_1372759 : Nat := 4983230072969 + 3 ^ 40 * 1372759 * 2
def baseEnd_1372759 : Nat := 313282306571333247910801

theorem tailTrace_1372759 : CollatzResearch.WordTrace tailWord_1372759 prefixEnd_1372759 313282306571333247910801 := by
  unfold tailWord_1372759
  simp only [CollatzResearch.WordTrace]
  refine ⟨50068634033736066416905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33379089355824044277936887 50068634033736066416905331)
  ·
    refine ⟨75102951050604099625357997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50068634033736066416905331 75102951050604099625357997)
    ·
      refine ⟨28163606643976537359509249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75102951050604099625357997 28163606643976537359509249)
      ·
        refine ⟨21122704982982403019631937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28163606643976537359509249 21122704982982403019631937)
        ·
          refine ⟨15842028737236802264723953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21122704982982403019631937 15842028737236802264723953)
          ·
            refine ⟨11881521552927601698542965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842028737236802264723953 11881521552927601698542965)
            ·
              refine ⟨1113892645586962659238403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11881521552927601698542965 1113892645586962659238403)
              ·
                refine ⟨1670838968380443988857605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113892645586962659238403 1670838968380443988857605)
                ·
                  refine ⟨313282306571333247910801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670838968380443988857605 313282306571333247910801)
                  ·
                    rfl

theorem cell21_1372759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_1372759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372759 prefixEnd_1372759 := by exact prefixLift 1372759
  have htrace : WordTrace (prefixWord ++ tailWord_1372759) baseStart_1372759 baseEnd_1372759 := by
    simpa [prefixWord, tailWord_1372759, baseEnd_1372759] using wordTrace_append hprefix tailTrace_1372759
  have hstable : (prefixWord ++ tailWord_1372759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372759).length < 2 ^ (prefixWord ++ tailWord_1372759).sum := by decide
  have hdescent : baseEnd_1372759 < baseStart_1372759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372773 : List Nat := [1, 3, 1, 3, 4, 1, 1, 7]
def baseStart_1372773 : Nat := 118140960795 + 1372773 * 2 ^ 59
def prefixEnd_1372773 : Nat := 4983230072969 + 3 ^ 40 * 1372773 * 2
def baseEnd_1372773 : Nat := 104428500520690778225813

theorem tailTrace_1372773 : CollatzResearch.WordTrace tailWord_1372773 prefixEnd_1372773 104428500520690778225813 := by
  unfold tailWord_1372773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50069144655685346807914973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33379429770456897871943315 50069144655685346807914973)
  ·
    refine ⟨18775929245882005052968115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50069144655685346807914973 18775929245882005052968115)
    ·
      refine ⟨28163893868823007579452173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18775929245882005052968115 28163893868823007579452173)
      ·
        refine ⟨10561460200808627842294565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28163893868823007579452173 10561460200808627842294565)
        ·
          refine ⟨1980273787651617720430231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10561460200808627842294565 1980273787651617720430231)
          ·
            refine ⟨2970410681477426580645347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980273787651617720430231 2970410681477426580645347)
            ·
              refine ⟨4455616022216139870968021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970410681477426580645347 4455616022216139870968021)
              ·
                refine ⟨104428500520690778225813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4455616022216139870968021 104428500520690778225813)
                ·
                  rfl

theorem cell21_1372773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_1372773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372773 prefixEnd_1372773 := by exact prefixLift 1372773
  have htrace : WordTrace (prefixWord ++ tailWord_1372773) baseStart_1372773 baseEnd_1372773 := by
    simpa [prefixWord, tailWord_1372773, baseEnd_1372773] using wordTrace_append hprefix tailTrace_1372773
  have hstable : (prefixWord ++ tailWord_1372773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372773).length < 2 ^ (prefixWord ++ tailWord_1372773).sum := by decide
  have hdescent : baseEnd_1372773 < baseStart_1372773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372790 : List Nat := [5, 1, 1, 2, 3, 2, 7]
def baseStart_1372790 : Nat := 118140960795 + 1372790 * 2 ^ 59
def prefixEnd_1372790 : Nat := 4983230072969 + 3 ^ 40 * 1372790 * 2
def baseEnd_1372790 : Nat := 34809931243742675877119

theorem tailTrace_1372790 : CollatzResearch.WordTrace tailWord_1372790 prefixEnd_1372790 34809931243742675877119 := by
  unfold tailWord_1372790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129360293538984919455239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33379843131082505807522549 3129360293538984919455239)
  ·
    refine ⟨4694040440308477379182859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129360293538984919455239 4694040440308477379182859)
    ·
      refine ⟨7041060660462716068774289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694040440308477379182859 7041060660462716068774289)
      ·
        refine ⟨5280795495347037051580717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7041060660462716068774289 5280795495347037051580717)
        ·
          refine ⟨1980298310755138894342769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5280795495347037051580717 1980298310755138894342769)
          ·
            refine ⟨1485223733066354170757077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980298310755138894342769 1485223733066354170757077)
            ·
              refine ⟨34809931243742675877119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1485223733066354170757077 34809931243742675877119)
              ·
                rfl

theorem cell21_1372790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 7].length) (baseStart_1372790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372790 prefixEnd_1372790 := by exact prefixLift 1372790
  have htrace : WordTrace (prefixWord ++ tailWord_1372790) baseStart_1372790 baseEnd_1372790 := by
    simpa [prefixWord, tailWord_1372790, baseEnd_1372790] using wordTrace_append hprefix tailTrace_1372790
  have hstable : (prefixWord ++ tailWord_1372790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372790).length < 2 ^ (prefixWord ++ tailWord_1372790).sum := by decide
  have hdescent : baseEnd_1372790 < baseStart_1372790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372804 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1372804 : Nat := 118140960795 + 1372804 * 2 ^ 59
def prefixEnd_1372804 : Nat := 4983230072969 + 3 ^ 40 * 1372804 * 2
def baseEnd_1372804 : Nat := 313292576184423169660709

theorem tailTrace_1372804 : CollatzResearch.WordTrace tailWord_1372804 prefixEnd_1372804 313292576184423169660709 := by
  unfold tailWord_1372804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035137659286519551146733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33380183545715359401528977 25035137659286519551146733)
  ·
    refine ⟨9388176622232444831680025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25035137659286519551146733 9388176622232444831680025)
    ·
      refine ⟨7041132466674333623760019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9388176622232444831680025 7041132466674333623760019)
      ·
        refine ⟨10561698700011500435640029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041132466674333623760019 10561698700011500435640029)
        ·
          refine ⟨3960637012504312663365011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10561698700011500435640029 3960637012504312663365011)
          ·
            refine ⟨5940955518756468995047517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960637012504312663365011 5940955518756468995047517)
            ·
              refine ⟨2227858319533675873142819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5940955518756468995047517 2227858319533675873142819)
              ·
                refine ⟨3341787479300513809714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227858319533675873142819 3341787479300513809714229)
                ·
                  refine ⟨313292576184423169660709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341787479300513809714229 313292576184423169660709)
                  ·
                    rfl

theorem cell21_1372804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1372804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372804 prefixEnd_1372804 := by exact prefixLift 1372804
  have htrace : WordTrace (prefixWord ++ tailWord_1372804) baseStart_1372804 baseEnd_1372804 := by
    simpa [prefixWord, tailWord_1372804, baseEnd_1372804] using wordTrace_append hprefix tailTrace_1372804
  have hstable : (prefixWord ++ tailWord_1372804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372804).length < 2 ^ (prefixWord ++ tailWord_1372804).sum := by decide
  have hdescent : baseEnd_1372804 < baseStart_1372804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372849 : List Nat := [1, 2, 2, 6, 1, 9]
def baseStart_1372849 : Nat := 118140960795 + 1372849 * 2 ^ 59
def prefixEnd_1372849 : Nat := 4983230072969 + 3 ^ 40 * 1372849 * 2
def baseEnd_1372849 : Nat := 11603809103611595978171

theorem tailTrace_1372849 : CollatzResearch.WordTrace tailWord_1372849 prefixEnd_1372849 11603809103611595978171 := by
  unfold tailWord_1372849
  simp only [CollatzResearch.WordTrace]
  refine ⟨50071916603410011787681601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33381277735606674525121067 50071916603410011787681601)
  ·
    refine ⟨37553937452557508840761201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50071916603410011787681601 37553937452557508840761201)
    ·
      refine ⟨28165453089418131630570901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37553937452557508840761201 28165453089418131630570901)
      ·
        refine ⟨1320255613566474920183011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28165453089418131630570901 1320255613566474920183011)
        ·
          refine ⟨1980383420349712380274517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320255613566474920183011 1980383420349712380274517)
          ·
            refine ⟨11603809103611595978171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1980383420349712380274517 11603809103611595978171)
            ·
              rfl

theorem cell21_1372849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 9].length) (baseStart_1372849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372849 prefixEnd_1372849 := by exact prefixLift 1372849
  have htrace : WordTrace (prefixWord ++ tailWord_1372849) baseStart_1372849 baseEnd_1372849 := by
    simpa [prefixWord, tailWord_1372849, baseEnd_1372849] using wordTrace_append hprefix tailTrace_1372849
  have hstable : (prefixWord ++ tailWord_1372849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372849).length < 2 ^ (prefixWord ++ tailWord_1372849).sum := by decide
  have hdescent : baseEnd_1372849 < baseStart_1372849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372855 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 3]
def baseStart_1372855 : Nat := 118140960795 + 1372855 * 2 ^ 59
def prefixEnd_1372855 : Nat := 4983230072969 + 3 ^ 40 * 1372855 * 2
def baseEnd_1372855 : Nat := 313304215079258414310605

theorem tailTrace_1372855 : CollatzResearch.WordTrace tailWord_1372855 prefixEnd_1372855 313304215079258414310605 := by
  unfold tailWord_1372855
  simp only [CollatzResearch.WordTrace]
  refine ⟨50072135441388274812400019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33381423627592183208266679 50072135441388274812400019)
  ·
    refine ⟨75108203162082412218600029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50072135441388274812400019 75108203162082412218600029)
    ·
      refine ⟨28165576185780904581975011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75108203162082412218600029 28165576185780904581975011)
      ·
        refine ⟨42248364278671356872962517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28165576185780904581975011 42248364278671356872962517)
        ·
          refine ⟨990196037781359926710059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42248364278671356872962517 990196037781359926710059)
          ·
            refine ⟨1485294056672039890065089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990196037781359926710059 1485294056672039890065089)
            ·
              refine ⟨1113970542504029917548817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485294056672039890065089 1113970542504029917548817)
              ·
                refine ⟨835477906878022438161613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113970542504029917548817 835477906878022438161613)
                ·
                  refine ⟨313304215079258414310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835477906878022438161613 313304215079258414310605)
                  ·
                    rfl

theorem cell21_1372855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].length) (baseStart_1372855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372855 prefixEnd_1372855 := by exact prefixLift 1372855
  have htrace : WordTrace (prefixWord ++ tailWord_1372855) baseStart_1372855 baseEnd_1372855 := by
    simpa [prefixWord, tailWord_1372855, baseEnd_1372855] using wordTrace_append hprefix tailTrace_1372855
  have hstable : (prefixWord ++ tailWord_1372855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372855).length < 2 ^ (prefixWord ++ tailWord_1372855).sum := by decide
  have hdescent : baseEnd_1372855 < baseStart_1372855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372897 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 3]
def baseStart_1372897 : Nat := 118140960795 + 1372897 * 2 ^ 59
def prefixEnd_1372897 : Nat := 4983230072969 + 3 ^ 40 * 1372897 * 2
def baseEnd_1372897 : Nat := 313313800051475674610519

theorem tailTrace_1372897 : CollatzResearch.WordTrace tailWord_1372897 prefixEnd_1372897 313313800051475674610519 := by
  unfold tailWord_1372897
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073667307236115985428945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33382444871490743990285963 50073667307236115985428945)
  ·
    refine ⟨37555250480427086989071709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50073667307236115985428945 37555250480427086989071709)
    ·
      refine ⟨14083218930160157620901891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37555250480427086989071709 14083218930160157620901891)
      ·
        refine ⟨21124828395240236431352837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14083218930160157620901891 21124828395240236431352837)
        ·
          refine ⟨3960905324107544330878657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21124828395240236431352837 3960905324107544330878657)
          ·
            refine ⟨2970678993080658248158993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960905324107544330878657 2970678993080658248158993)
            ·
              refine ⟨2228009244810493686119245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970678993080658248158993 2228009244810493686119245)
              ·
                refine ⟨835503466803935132294717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2228009244810493686119245 835503466803935132294717)
                ·
                  refine ⟨313313800051475674610519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835503466803935132294717 313313800051475674610519)
                  ·
                    rfl

theorem cell21_1372897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_1372897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372897 prefixEnd_1372897 := by exact prefixLift 1372897
  have htrace : WordTrace (prefixWord ++ tailWord_1372897) baseStart_1372897 baseEnd_1372897 := by
    simpa [prefixWord, tailWord_1372897, baseEnd_1372897] using wordTrace_append hprefix tailTrace_1372897
  have hstable : (prefixWord ++ tailWord_1372897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372897).length < 2 ^ (prefixWord ++ tailWord_1372897).sum := by decide
  have hdescent : baseEnd_1372897 < baseStart_1372897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372911 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_1372911 : Nat := 118140960795 + 1372911 * 2 ^ 59
def prefixEnd_1372911 : Nat := 4983230072969 + 3 ^ 40 * 1372911 * 2
def baseEnd_1372911 : Nat := 313316995042214761377157

theorem tailTrace_1372911 : CollatzResearch.WordTrace tailWord_1372911 prefixEnd_1372911 313316995042214761377157 := by
  unfold tailWord_1372911
  simp only [CollatzResearch.WordTrace]
  refine ⟨50074177929185396376438587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33382785286123597584292391 50074177929185396376438587)
  ·
    refine ⟨75111266893778094564657881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50074177929185396376438587 75111266893778094564657881)
    ·
      refine ⟨56333450170333570923493411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75111266893778094564657881 56333450170333570923493411)
      ·
        refine ⟨84500175255500356385240117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56333450170333570923493411 84500175255500356385240117)
        ·
          refine ⟨7921891430203158411116261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84500175255500356385240117 7921891430203158411116261)
          ·
            refine ⟨1485354643163092202084299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7921891430203158411116261 1485354643163092202084299)
            ·
              refine ⟨2228031964744638303126449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485354643163092202084299 2228031964744638303126449)
              ·
                refine ⟨1671023973558478727344837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228031964744638303126449 1671023973558478727344837)
                ·
                  refine ⟨313316995042214761377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671023973558478727344837 313316995042214761377157)
                  ·
                    rfl

theorem cell21_1372911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_1372911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372911 prefixEnd_1372911 := by exact prefixLift 1372911
  have htrace : WordTrace (prefixWord ++ tailWord_1372911) baseStart_1372911 baseEnd_1372911 := by
    simpa [prefixWord, tailWord_1372911, baseEnd_1372911] using wordTrace_append hprefix tailTrace_1372911
  have hstable : (prefixWord ++ tailWord_1372911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372911).length < 2 ^ (prefixWord ++ tailWord_1372911).sum := by decide
  have hdescent : baseEnd_1372911 < baseStart_1372911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372984 : List Nat := [2, 1, 2, 1, 3, 2, 4, 6]
def baseStart_1372984 : Nat := 118140960795 + 1372984 * 2 ^ 59
def prefixEnd_1372984 : Nat := 4983230072969 + 3 ^ 40 * 1372984 * 2
def baseEnd_1372984 : Nat := 104444551545594285553447

theorem tailTrace_1372984 : CollatzResearch.WordTrace tailWord_1372984 prefixEnd_1372984 104444551545594285553447 := by
  unfold tailWord_1372984
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038420228960464921923003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33384560305280619895897337 25038420228960464921923003)
  ·
    refine ⟨37557630343440697382884505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25038420228960464921923003 37557630343440697382884505)
    ·
      refine ⟨28168222757580523037163379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37557630343440697382884505 28168222757580523037163379)
      ·
        refine ⟨42252334136370784555745069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28168222757580523037163379 42252334136370784555745069)
        ·
          refine ⟨15844625301139044208404401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42252334136370784555745069 15844625301139044208404401)
          ·
            refine ⟨11883468975854283156303301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15844625301139044208404401 11883468975854283156303301)
            ·
              refine ⟨2228150432972678091806869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11883468975854283156303301 2228150432972678091806869)
              ·
                refine ⟨104444551545594285553447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2228150432972678091806869 104444551545594285553447)
                ·
                  rfl

theorem cell21_1372984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_1372984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1372984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1372984 prefixEnd_1372984 := by exact prefixLift 1372984
  have htrace : WordTrace (prefixWord ++ tailWord_1372984) baseStart_1372984 baseEnd_1372984 := by
    simpa [prefixWord, tailWord_1372984, baseEnd_1372984] using wordTrace_append hprefix tailTrace_1372984
  have hstable : (prefixWord ++ tailWord_1372984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372984).length < 2 ^ (prefixWord ++ tailWord_1372984).sum := by decide
  have hdescent : baseEnd_1372984 < baseStart_1372984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373029 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1373029 : Nat := 118140960795 + 1373029 * 2 ^ 59
def prefixEnd_1373029 : Nat := 4983230072969 + 3 ^ 40 * 1373029 * 2
def baseEnd_1373029 : Nat := 313343924249872778410249

theorem tailTrace_1373029 : CollatzResearch.WordTrace tailWord_1373029 prefixEnd_1373029 313343924249872778410249 := by
  unfold tailWord_1373029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50078481742757902529234141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33385654495171935019489427 50078481742757902529234141)
  ·
    refine ⟨18779430653534213448462803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50078481742757902529234141 18779430653534213448462803)
    ·
      refine ⟨28169145980301320172694205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18779430653534213448462803 28169145980301320172694205)
      ·
        refine ⟨10563429742612995064760327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28169145980301320172694205 10563429742612995064760327)
        ·
          refine ⟨15845144613919492597140491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563429742612995064760327 15845144613919492597140491)
          ·
            refine ⟨23767716920879238895710737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845144613919492597140491 23767716920879238895710737)
            ·
              refine ⟨17825787690659429171783053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23767716920879238895710737 17825787690659429171783053)
              ·
                refine ⟨6684670383997285939418645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17825787690659429171783053 6684670383997285939418645)
                ·
                  refine ⟨313343924249872778410249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6684670383997285939418645 313343924249872778410249)
                  ·
                    rfl

theorem cell21_1373029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1373029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373029 prefixEnd_1373029 := by exact prefixLift 1373029
  have htrace : WordTrace (prefixWord ++ tailWord_1373029) baseStart_1373029 baseEnd_1373029 := by
    simpa [prefixWord, tailWord_1373029, baseEnd_1373029] using wordTrace_append hprefix tailTrace_1373029
  have hstable : (prefixWord ++ tailWord_1373029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373029).length < 2 ^ (prefixWord ++ tailWord_1373029).sum := by decide
  have hdescent : baseEnd_1373029 < baseStart_1373029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373195 : List Nat := [1, 1, 1, 1, 6, 11]
def baseStart_1373195 : Nat := 118140960795 + 1373195 * 2 ^ 59
def prefixEnd_1373195 : Nat := 4983230072969 + 3 ^ 40 * 1373195 * 2
def baseEnd_1373195 : Nat := 11606733618944199209009

theorem tailTrace_1373195 : CollatzResearch.WordTrace tailWord_1373195 prefixEnd_1373195 11606733618944199209009 := by
  unfold tailWord_1373195
  simp only [CollatzResearch.WordTrace]
  refine ⟨50084536260156512879777039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33389690840104341919851359 50084536260156512879777039)
  ·
    refine ⟨75126804390234769319665559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50084536260156512879777039 75126804390234769319665559)
    ·
      refine ⟨112690206585352153979498339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75126804390234769319665559 112690206585352153979498339)
      ·
        refine ⟨169035309878028230969247509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112690206585352153979498339 169035309878028230969247509)
        ·
          refine ⟨7923530150532573326683477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169035309878028230969247509 7923530150532573326683477)
          ·
            refine ⟨11606733618944199209009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7923530150532573326683477 11606733618944199209009)
            ·
              rfl

theorem cell21_1373195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 11].length) (baseStart_1373195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373195 prefixEnd_1373195 := by exact prefixLift 1373195
  have htrace : WordTrace (prefixWord ++ tailWord_1373195) baseStart_1373195 baseEnd_1373195 := by
    simpa [prefixWord, tailWord_1373195, baseEnd_1373195] using wordTrace_append hprefix tailTrace_1373195
  have hstable : (prefixWord ++ tailWord_1373195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373195).length < 2 ^ (prefixWord ++ tailWord_1373195).sum := by decide
  have hdescent : baseEnd_1373195 < baseStart_1373195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373198 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_1373198 : Nat := 118140960795 + 1373198 * 2 ^ 59
def prefixEnd_1373198 : Nat := 4983230072969 + 3 ^ 40 * 1373198 * 2
def baseEnd_1373198 : Nat := 313382492352366040093237

theorem tailTrace_1373198 : CollatzResearch.WordTrace tailWord_1373198 prefixEnd_1373198 313382492352366040093237 := by
  unfold tailWord_1373198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260580709893205549017031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33389763786097096261424165 6260580709893205549017031)
  ·
    refine ⟨9390871064839808323525547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6260580709893205549017031 9390871064839808323525547)
    ·
      refine ⟨14086306597259712485288321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390871064839808323525547 14086306597259712485288321)
      ·
        refine ⟨10564729947944784363966241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086306597259712485288321 10564729947944784363966241)
        ·
          refine ⟨7923547460958588272974681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564729947944784363966241 7923547460958588272974681)
          ·
            refine ⟨5942660595718941204731011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923547460958588272974681 5942660595718941204731011)
            ·
              refine ⟨8913990893578411807096517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942660595718941204731011 8913990893578411807096517)
              ·
                refine ⟨1671373292545952213830597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8913990893578411807096517 1671373292545952213830597)
                ·
                  refine ⟨313382492352366040093237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671373292545952213830597 313382492352366040093237)
                  ·
                    rfl

theorem cell21_1373198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_1373198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373198 prefixEnd_1373198 := by exact prefixLift 1373198
  have htrace : WordTrace (prefixWord ++ tailWord_1373198) baseStart_1373198 baseEnd_1373198 := by
    simpa [prefixWord, tailWord_1373198, baseEnd_1373198] using wordTrace_append hprefix tailTrace_1373198
  have hstable : (prefixWord ++ tailWord_1373198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373198).length < 2 ^ (prefixWord ++ tailWord_1373198).sum := by decide
  have hdescent : baseEnd_1373198 < baseStart_1373198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373257 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_1373257 : Nat := 118140960795 + 1373257 * 2 ^ 59
def prefixEnd_1373257 : Nat := 4983230072969 + 3 ^ 40 * 1373257 * 2
def baseEnd_1373257 : Nat := 313395956956195048609783

theorem tailTrace_1373257 : CollatzResearch.WordTrace tailWord_1373257 prefixEnd_1373257 313395956956195048609783 := by
  unfold tailWord_1373257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50086797585931897468534025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33391198390621264979022683 50086797585931897468534025)
  ·
    refine ⟨37565098189448923101400519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50086797585931897468534025 37565098189448923101400519)
    ·
      refine ⟨56347647284173384652100779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37565098189448923101400519 56347647284173384652100779)
      ·
        refine ⟨84521470926260076978151169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56347647284173384652100779 84521470926260076978151169)
        ·
          refine ⟨63391103194695057733613377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84521470926260076978151169 63391103194695057733613377)
          ·
            refine ⟨47543327396021293300210033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63391103194695057733613377 47543327396021293300210033)
            ·
              refine ⟨35657495547015969975157525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47543327396021293300210033 35657495547015969975157525)
              ·
                refine ⟨1671445103766373592585509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35657495547015969975157525 1671445103766373592585509)
                ·
                  refine ⟨313395956956195048609783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671445103766373592585509 313395956956195048609783)
                  ·
                    rfl

theorem cell21_1373257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_1373257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373257 prefixEnd_1373257 := by exact prefixLift 1373257
  have htrace : WordTrace (prefixWord ++ tailWord_1373257) baseStart_1373257 baseEnd_1373257 := by
    simpa [prefixWord, tailWord_1373257, baseEnd_1373257] using wordTrace_append hprefix tailTrace_1373257
  have hstable : (prefixWord ++ tailWord_1373257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373257).length < 2 ^ (prefixWord ++ tailWord_1373257).sum := by decide
  have hdescent : baseEnd_1373257 < baseStart_1373257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373271 : List Nat := [1, 1, 3, 2, 2, 1, 1, 10]
def baseStart_1373271 : Nat := 118140960795 + 1373271 * 2 ^ 59
def prefixEnd_1373271 : Nat := 4983230072969 + 3 ^ 40 * 1373271 * 2
def baseEnd_1373271 : Nat := 104466383982311378458807

theorem tailTrace_1373271 : CollatzResearch.WordTrace tailWord_1373271 prefixEnd_1373271 104466383982311378458807 := by
  unfold tailWord_1373271
  simp only [CollatzResearch.WordTrace]
  refine ⟨50087308207881177859543667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33391538805254118573029111 50087308207881177859543667)
  ·
    refine ⟨75130962311821766789315501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50087308207881177859543667 75130962311821766789315501)
    ·
      refine ⟨28174110866933162545993313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75130962311821766789315501 28174110866933162545993313)
      ·
        refine ⟨21130583150199871909494985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28174110866933162545993313 21130583150199871909494985)
        ·
          refine ⟨15847937362649903932121239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21130583150199871909494985 15847937362649903932121239)
          ·
            refine ⟨23771906043974855898181859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15847937362649903932121239 23771906043974855898181859)
            ·
              refine ⟨35657859065962283847272789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23771906043974855898181859 35657859065962283847272789)
              ·
                refine ⟨104466383982311378458807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35657859065962283847272789 104466383982311378458807)
                ·
                  rfl

theorem cell21_1373271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_1373271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373271 prefixEnd_1373271 := by exact prefixLift 1373271
  have htrace : WordTrace (prefixWord ++ tailWord_1373271) baseStart_1373271 baseEnd_1373271 := by
    simpa [prefixWord, tailWord_1373271, baseEnd_1373271] using wordTrace_append hprefix tailTrace_1373271
  have hstable : (prefixWord ++ tailWord_1373271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373271).length < 2 ^ (prefixWord ++ tailWord_1373271).sum := by decide
  have hdescent : baseEnd_1373271 < baseStart_1373271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373305 : List Nat := [1, 2, 1, 3, 6, 1, 7]
def baseStart_1373305 : Nat := 118140960795 + 1373305 * 2 ^ 59
def prefixEnd_1373305 : Nat := 4983230072969 + 3 ^ 40 * 1373305 * 2
def baseEnd_1373305 : Nat := 34822990134461959089965

theorem tailTrace_1373305 : CollatzResearch.WordTrace tailWord_1373305 prefixEnd_1373305 34822990134461959089965 := by
  unfold tailWord_1373305
  simp only [CollatzResearch.WordTrace]
  refine ⟨50088548289758001666281369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33392365526505334444187579 50088548289758001666281369)
  ·
    refine ⟨37566411217318501249711027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50088548289758001666281369 37566411217318501249711027)
    ·
      refine ⟨56349616825977751874566541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37566411217318501249711027 56349616825977751874566541)
      ·
        refine ⟨21131106309741656952962453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56349616825977751874566541 21131106309741656952962453)
        ·
          refine ⟨990520608269140169670115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21131106309741656952962453 990520608269140169670115)
          ·
            refine ⟨1485780912403710254505173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990520608269140169670115 1485780912403710254505173)
            ·
              refine ⟨34822990134461959089965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1485780912403710254505173 34822990134461959089965)
              ·
                rfl

theorem cell21_1373305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 7].length) (baseStart_1373305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373305 prefixEnd_1373305 := by exact prefixLift 1373305
  have htrace : WordTrace (prefixWord ++ tailWord_1373305) baseStart_1373305 baseEnd_1373305 := by
    simpa [prefixWord, tailWord_1373305, baseEnd_1373305] using wordTrace_append hprefix tailTrace_1373305
  have hstable : (prefixWord ++ tailWord_1373305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373305).length < 2 ^ (prefixWord ++ tailWord_1373305).sum := by decide
  have hdescent : baseEnd_1373305 < baseStart_1373305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373426 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1373426 : Nat := 118140960795 + 1373426 * 2 ^ 59
def prefixEnd_1373426 : Nat := 4983230072969 + 3 ^ 40 * 1373426 * 2
def baseEnd_1373426 : Nat := 313434525058688310292771

theorem tailTrace_1373426 : CollatzResearch.WordTrace tailWord_1373426 prefixEnd_1373426 313434525058688310292771 := by
  unfold tailWord_1373426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12523240380579909832859033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33395307681546426220957421 12523240380579909832859033)
  ·
    refine ⟨9392430285434932374644275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12523240380579909832859033 9392430285434932374644275)
    ·
      refine ⟨14088645428152398561966413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9392430285434932374644275 14088645428152398561966413)
      ·
        refine ⟨5283242035557149460737405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14088645428152398561966413 5283242035557149460737405)
        ·
          refine ⟨1981215763333931047776527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5283242035557149460737405 1981215763333931047776527)
          ·
            refine ⟨2971823645000896571664791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981215763333931047776527 2971823645000896571664791)
            ·
              refine ⟨4457735467501344857497187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971823645000896571664791 4457735467501344857497187)
              ·
                refine ⟨6686603201252017286245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457735467501344857497187 6686603201252017286245781)
                ·
                  refine ⟨313434525058688310292771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6686603201252017286245781 313434525058688310292771)
                  ·
                    rfl

theorem cell21_1373426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1373426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373426 prefixEnd_1373426 := by exact prefixLift 1373426
  have htrace : WordTrace (prefixWord ++ tailWord_1373426) baseStart_1373426 baseEnd_1373426 := by
    simpa [prefixWord, tailWord_1373426, baseEnd_1373426] using wordTrace_append hprefix tailTrace_1373426
  have hstable : (prefixWord ++ tailWord_1373426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373426).length < 2 ^ (prefixWord ++ tailWord_1373426).sum := by decide
  have hdescent : baseEnd_1373426 < baseStart_1373426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373488 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_1373488 : Nat := 118140960795 + 1373488 * 2 ^ 59
def prefixEnd_1373488 : Nat := 4983230072969 + 3 ^ 40 * 1373488 * 2
def baseEnd_1373488 : Nat := 313448674303389980259311

theorem tailTrace_1373488 : CollatzResearch.WordTrace tailWord_1373488 prefixEnd_1373488 313448674303389980259311 := by
  unfold tailWord_1373488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25047611424047511960096559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33396815232063349280128745 25047611424047511960096559)
  ·
    refine ⟨37571417136071267940144839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25047611424047511960096559 37571417136071267940144839)
    ·
      refine ⟨56357125704106901910217259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37571417136071267940144839 56357125704106901910217259)
      ·
        refine ⟨84535688556160352865325889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56357125704106901910217259 84535688556160352865325889)
        ·
          refine ⟨63401766417120264648994417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84535688556160352865325889 63401766417120264648994417)
          ·
            refine ⟨47551324812840198486745813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63401766417120264648994417 47551324812840198486745813)
            ·
              refine ⟨1114484175300942152033105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47551324812840198486745813 1114484175300942152033105)
              ·
                refine ⟨835863131475706614024829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114484175300942152033105 835863131475706614024829)
                ·
                  refine ⟨313448674303389980259311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835863131475706614024829 313448674303389980259311)
                  ·
                    rfl

theorem cell21_1373488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_1373488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373488 prefixEnd_1373488 := by exact prefixLift 1373488
  have htrace : WordTrace (prefixWord ++ tailWord_1373488) baseStart_1373488 baseEnd_1373488 := by
    simpa [prefixWord, tailWord_1373488, baseEnd_1373488] using wordTrace_append hprefix tailTrace_1373488
  have hstable : (prefixWord ++ tailWord_1373488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373488).length < 2 ^ (prefixWord ++ tailWord_1373488).sum := by decide
  have hdescent : baseEnd_1373488 < baseStart_1373488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373494 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1373494 : Nat := 118140960795 + 1373494 * 2 ^ 59
def prefixEnd_1373494 : Nat := 4983230072969 + 3 ^ 40 * 1373494 * 2
def baseEnd_1373494 : Nat := 313450043585135303159299

theorem tailTrace_1373494 : CollatzResearch.WordTrace tailWord_1373494 prefixEnd_1373494 313450043585135303159299 := by
  unfold tailWord_1373494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130965105379580434056971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33396961124048857963274357 3130965105379580434056971)
  ·
    refine ⟨4696447658069370651085457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130965105379580434056971 4696447658069370651085457)
    ·
      refine ⟨3522335743552027988314093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4696447658069370651085457 3522335743552027988314093)
      ·
        refine ⟨1320875903832010495617785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3522335743552027988314093 1320875903832010495617785)
        ·
          refine ⟨990656927874007871713339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320875903832010495617785 990656927874007871713339)
          ·
            refine ⟨1485985391811011807570009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990656927874007871713339 1485985391811011807570009)
            ·
              refine ⟨1114489043858258855677507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485985391811011807570009 1114489043858258855677507)
              ·
                refine ⟨1671733565787388283516261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114489043858258855677507 1671733565787388283516261)
                ·
                  refine ⟨313450043585135303159299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671733565787388283516261 313450043585135303159299)
                  ·
                    rfl

theorem cell21_1373494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1373494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373494 prefixEnd_1373494 := by exact prefixLift 1373494
  have htrace : WordTrace (prefixWord ++ tailWord_1373494) baseStart_1373494 baseEnd_1373494 := by
    simpa [prefixWord, tailWord_1373494, baseEnd_1373494] using wordTrace_append hprefix tailTrace_1373494
  have hstable : (prefixWord ++ tailWord_1373494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373494).length < 2 ^ (prefixWord ++ tailWord_1373494).sum := by decide
  have hdescent : baseEnd_1373494 < baseStart_1373494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373502 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1373502 : Nat := 118140960795 + 1373502 * 2 ^ 59
def prefixEnd_1373502 : Nat := 4983230072969 + 3 ^ 40 * 1373502 * 2
def baseEnd_1373502 : Nat := 313451869294129067025949

theorem tailTrace_1373502 : CollatzResearch.WordTrace tailWord_1373502 prefixEnd_1373502 313451869294129067025949 := by
  unfold tailWord_1373502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261966683755538038900345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33397155646696202874135173 6261966683755538038900345)
  ·
    refine ⟨4696475012816653529175259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6261966683755538038900345 4696475012816653529175259)
    ·
      refine ⟨7044712519224980293762889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696475012816653529175259 7044712519224980293762889)
      ·
        refine ⟨5283534389418735220322167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7044712519224980293762889 5283534389418735220322167)
        ·
          refine ⟨7925301584128102830483251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283534389418735220322167 7925301584128102830483251)
          ·
            refine ⟨11887952376192154245724877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925301584128102830483251 11887952376192154245724877)
            ·
              refine ⟨4457982141072057842146829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11887952376192154245724877 4457982141072057842146829)
              ·
                refine ⟨1671743302902021690805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457982141072057842146829 1671743302902021690805061)
                ·
                  refine ⟨313451869294129067025949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671743302902021690805061 313451869294129067025949)
                  ·
                    rfl

theorem cell21_1373502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1373502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373502 prefixEnd_1373502 := by exact prefixLift 1373502
  have htrace : WordTrace (prefixWord ++ tailWord_1373502) baseStart_1373502 baseEnd_1373502 := by
    simpa [prefixWord, tailWord_1373502, baseEnd_1373502] using wordTrace_append hprefix tailTrace_1373502
  have hstable : (prefixWord ++ tailWord_1373502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373502).length < 2 ^ (prefixWord ++ tailWord_1373502).sum := by decide
  have hdescent : baseEnd_1373502 < baseStart_1373502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373533 : List Nat := [1, 4, 5, 1, 10]
def baseStart_1373533 : Nat := 118140960795 + 1373533 * 2 ^ 59
def prefixEnd_1373533 : Nat := 4983230072969 + 3 ^ 40 * 1373533 * 2
def baseEnd_1373533 : Nat := 3869863505141727185299

theorem tailTrace_1373533 : CollatzResearch.WordTrace tailWord_1373533 prefixEnd_1373533 3869863505141727185299 := by
  unfold tailWord_1373533
  simp only [CollatzResearch.WordTrace]
  refine ⟨50096864132931996605581253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33397909421954664403720835 50096864132931996605581253)
  ·
    refine ⟨9393162024924749363546485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50096864132931996605581253 9393162024924749363546485)
    ·
      refine ⟨880608939836695252832483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9393162024924749363546485 880608939836695252832483)
      ·
        refine ⟨1320913409755042879248725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880608939836695252832483 1320913409755042879248725)
        ·
          refine ⟨3869863505141727185299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1320913409755042879248725 3869863505141727185299)
          ·
            rfl

theorem cell21_1373533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 10].length) (baseStart_1373533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373533 prefixEnd_1373533 := by exact prefixLift 1373533
  have htrace : WordTrace (prefixWord ++ tailWord_1373533) baseStart_1373533 baseEnd_1373533 := by
    simpa [prefixWord, tailWord_1373533, baseEnd_1373533] using wordTrace_append hprefix tailTrace_1373533
  have hstable : (prefixWord ++ tailWord_1373533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373533).length < 2 ^ (prefixWord ++ tailWord_1373533).sum := by decide
  have hdescent : baseEnd_1373533 < baseStart_1373533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373550 : List Nat := [4, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1373550 : Nat := 118140960795 + 1373550 * 2 ^ 59
def prefixEnd_1373550 : Nat := 4983230072969 + 3 ^ 40 * 1373550 * 2
def baseEnd_1373550 : Nat := 104487607849363883408617

theorem tailTrace_1373550 : CollatzResearch.WordTrace tailWord_1373550 prefixEnd_1373550 104487607849363883408617 := by
  unfold tailWord_1373550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262185521733801063618763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33398322782580272339300069 6262185521733801063618763)
  ·
    refine ⟨9393278282600701595428145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262185521733801063618763 9393278282600701595428145)
    ·
      refine ⟨7044958711950526196571109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9393278282600701595428145 7044958711950526196571109)
      ·
        refine ⟨1320929758490723661857083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7044958711950526196571109 1320929758490723661857083)
        ·
          refine ⟨1981394637736085492785625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320929758490723661857083 1981394637736085492785625)
          ·
            refine ⟨1486045978302064119589219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981394637736085492785625 1486045978302064119589219)
            ·
              refine ⟨2229068967453096179383829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486045978302064119589219 2229068967453096179383829)
              ·
                refine ⟨104487607849363883408617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2229068967453096179383829 104487607849363883408617)
                ·
                  rfl

theorem cell21_1373550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1373550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373550 prefixEnd_1373550 := by exact prefixLift 1373550
  have htrace : WordTrace (prefixWord ++ tailWord_1373550) baseStart_1373550 baseEnd_1373550 := by
    simpa [prefixWord, tailWord_1373550, baseEnd_1373550] using wordTrace_append hprefix tailTrace_1373550
  have hstable : (prefixWord ++ tailWord_1373550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373550).length < 2 ^ (prefixWord ++ tailWord_1373550).sum := by decide
  have hdescent : baseEnd_1373550 < baseStart_1373550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373561 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_1373561 : Nat := 118140960795 + 1373561 * 2 ^ 59
def prefixEnd_1373561 : Nat := 4983230072969 + 3 ^ 40 * 1373561 * 2
def baseEnd_1373561 : Nat := 313465333897958075542495

theorem tailTrace_1373561 : CollatzResearch.WordTrace tailWord_1373561 prefixEnd_1373561 313465333897958075542495 := by
  unfold tailWord_1373561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097885376830557387600537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33398590251220371591733691 50097885376830557387600537)
  ·
    refine ⟨37573414032622918040700403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50097885376830557387600537 37573414032622918040700403)
    ·
      refine ⟨56360121048934377061050605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37573414032622918040700403 56360121048934377061050605)
      ·
        refine ⟨21135045393350391397893977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56360121048934377061050605 21135045393350391397893977)
        ·
          refine ⟨15851284045012793548420483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21135045393350391397893977 15851284045012793548420483)
          ·
            refine ⟨23776926067519190322630725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15851284045012793548420483 23776926067519190322630725)
            ·
              refine ⟨4458173637659848185493261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23776926067519190322630725 4458173637659848185493261)
              ·
                refine ⟨1671815114122443069559973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4458173637659848185493261 1671815114122443069559973)
                ·
                  refine ⟨313465333897958075542495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671815114122443069559973 313465333897958075542495)
                  ·
                    rfl

theorem cell21_1373561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_1373561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373561 prefixEnd_1373561 := by exact prefixLift 1373561
  have htrace : WordTrace (prefixWord ++ tailWord_1373561) baseStart_1373561 baseEnd_1373561 := by
    simpa [prefixWord, tailWord_1373561, baseEnd_1373561] using wordTrace_append hprefix tailTrace_1373561
  have hstable : (prefixWord ++ tailWord_1373561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373561).length < 2 ^ (prefixWord ++ tailWord_1373561).sum := by decide
  have hdescent : baseEnd_1373561 < baseStart_1373561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373592 : List Nat := [2, 1, 2, 5, 2, 1, 8]
def baseStart_1373592 : Nat := 118140960795 + 1373592 * 2 ^ 59
def prefixEnd_1373592 : Nat := 4983230072969 + 3 ^ 40 * 1373592 * 2
def baseEnd_1373592 : Nat := 34830267613367656725085

theorem tailTrace_1373592 : CollatzResearch.WordTrace tailWord_1373592 prefixEnd_1373592 34830267613367656725085 := by
  unfold tailWord_1373592
  simp only [CollatzResearch.WordTrace]
  refine ⟨25049508019859124840989515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33399344026478833121319353 25049508019859124840989515)
  ·
    refine ⟨37574262029788687261484273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25049508019859124840989515 37574262029788687261484273)
    ·
      refine ⟨28180696522341515446113205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37574262029788687261484273 28180696522341515446113205)
      ·
        refine ⟨2641940298969517073073113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28180696522341515446113205 2641940298969517073073113)
        ·
          refine ⟨1981455224227137804804835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2641940298969517073073113 1981455224227137804804835)
          ·
            refine ⟨2972182836340706707207253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981455224227137804804835 2972182836340706707207253)
            ·
              refine ⟨34830267613367656725085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2972182836340706707207253 34830267613367656725085)
              ·
                rfl

theorem cell21_1373592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 8].length) (baseStart_1373592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373592 prefixEnd_1373592 := by exact prefixLift 1373592
  have htrace : WordTrace (prefixWord ++ tailWord_1373592) baseStart_1373592 baseEnd_1373592 := by
    simpa [prefixWord, tailWord_1373592, baseEnd_1373592] using wordTrace_append hprefix tailTrace_1373592
  have hstable : (prefixWord ++ tailWord_1373592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373592).length < 2 ^ (prefixWord ++ tailWord_1373592).sum := by decide
  have hdescent : baseEnd_1373592 < baseStart_1373592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373654 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1373654 : Nat := 118140960795 + 1373654 * 2 ^ 59
def prefixEnd_1373654 : Nat := 4983230072969 + 3 ^ 40 * 1373654 * 2
def baseEnd_1373654 : Nat := 313486557765010580492305

theorem tailTrace_1373654 : CollatzResearch.WordTrace tailWord_1373654 prefixEnd_1373654 313486557765010580492305 := by
  unfold tailWord_1373654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131329835343352141921001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33400851576995756180490677 3131329835343352141921001)
  ·
    refine ⟨2348497376507514106440751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3131329835343352141921001 2348497376507514106440751)
    ·
      refine ⟨3522746064761271159661127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348497376507514106440751 3522746064761271159661127)
      ·
        refine ⟨5284119097141906739491691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522746064761271159661127 5284119097141906739491691)
        ·
          refine ⟨7926178645712860109237537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284119097141906739491691 7926178645712860109237537)
          ·
            refine ⟨5944633984284645081928153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926178645712860109237537 5944633984284645081928153)
            ·
              refine ⟨4458475488213483811446115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944633984284645081928153 4458475488213483811446115)
              ·
                refine ⟨6687713232320225717169173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458475488213483811446115 6687713232320225717169173)
                ·
                  refine ⟨313486557765010580492305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6687713232320225717169173 313486557765010580492305)
                  ·
                    rfl

theorem cell21_1373654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1373654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373654 prefixEnd_1373654 := by exact prefixLift 1373654
  have htrace : WordTrace (prefixWord ++ tailWord_1373654) baseStart_1373654 baseEnd_1373654 := by
    simpa [prefixWord, tailWord_1373654, baseEnd_1373654] using wordTrace_append hprefix tailTrace_1373654
  have hstable : (prefixWord ++ tailWord_1373654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373654).length < 2 ^ (prefixWord ++ tailWord_1373654).sum := by decide
  have hdescent : baseEnd_1373654 < baseStart_1373654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373671 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 4]
def baseStart_1373671 : Nat := 118140960795 + 1373671 * 2 ^ 59
def prefixEnd_1373671 : Nat := 4983230072969 + 3 ^ 40 * 1373671 * 2
def baseEnd_1373671 : Nat := 313490437396622328708937

theorem tailTrace_1373671 : CollatzResearch.WordTrace tailWord_1373671 prefixEnd_1373671 313490437396622328708937 := by
  unfold tailWord_1373671
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101897406432046174104867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33401264937621364116069911 50101897406432046174104867)
  ·
    refine ⟨75152846109648069261157301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50101897406432046174104867 75152846109648069261157301)
    ·
      refine ⟨7045579322779506493233497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75152846109648069261157301 7045579322779506493233497)
      ·
        refine ⟨5284184492084629869925123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045579322779506493233497 5284184492084629869925123)
        ·
          refine ⟨7926276738126944804887685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284184492084629869925123 7926276738126944804887685)
          ·
            refine ⟨1486176888398802150916441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7926276738126944804887685 1486176888398802150916441)
            ·
              refine ⟨1114632666299101613187331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486176888398802150916441 1114632666299101613187331)
              ·
                refine ⟨1671948999448652419780997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114632666299101613187331 1671948999448652419780997)
                ·
                  refine ⟨313490437396622328708937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671948999448652419780997 313490437396622328708937)
                  ·
                    rfl

theorem cell21_1373671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_1373671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373671 prefixEnd_1373671 := by exact prefixLift 1373671
  have htrace : WordTrace (prefixWord ++ tailWord_1373671) baseStart_1373671 baseEnd_1373671 := by
    simpa [prefixWord, tailWord_1373671, baseEnd_1373671] using wordTrace_append hprefix tailTrace_1373671
  have hstable : (prefixWord ++ tailWord_1373671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373671).length < 2 ^ (prefixWord ++ tailWord_1373671).sum := by decide
  have hdescent : baseEnd_1373671 < baseStart_1373671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373702 : List Nat := [6, 2, 1, 1, 2, 9]
def baseStart_1373702 : Nat := 118140960795 + 1373702 * 2 ^ 59
def prefixEnd_1373702 : Nat := 4983230072969 + 3 ^ 40 * 1373702 * 2
def baseEnd_1373702 : Nat := 11611018963665672729341

theorem tailTrace_1373702 : CollatzResearch.WordTrace tailWord_1373702 prefixEnd_1373702 11611018963665672729341 := by
  unfold tailWord_1373702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565719627166241827140105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33402018712879825645655573 1565719627166241827140105)
  ·
    refine ⟨1174289720374681370355079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1565719627166241827140105 1174289720374681370355079)
    ·
      refine ⟨1761434580562022055532619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174289720374681370355079 1761434580562022055532619)
      ·
        refine ⟨2642151870843033083298929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761434580562022055532619 2642151870843033083298929)
        ·
          refine ⟨1981613903132274812474197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642151870843033083298929 1981613903132274812474197)
          ·
            refine ⟨11611018963665672729341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1981613903132274812474197 11611018963665672729341)
            ·
              rfl

theorem cell21_1373702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 9].length) (baseStart_1373702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373702 prefixEnd_1373702 := by exact prefixLift 1373702
  have htrace : WordTrace (prefixWord ++ tailWord_1373702) baseStart_1373702 baseEnd_1373702 := by
    simpa [prefixWord, tailWord_1373702, baseEnd_1373702] using wordTrace_append hprefix tailTrace_1373702
  have hstable : (prefixWord ++ tailWord_1373702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373702).length < 2 ^ (prefixWord ++ tailWord_1373702).sum := by decide
  have hdescent : baseEnd_1373702 < baseStart_1373702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373713 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_1373713 : Nat := 118140960795 + 1373713 * 2 ^ 59
def prefixEnd_1373713 : Nat := 4983230072969 + 3 ^ 40 * 1373713 * 2
def baseEnd_1373713 : Nat := 313500022368839589008851

theorem tailTrace_1373713 : CollatzResearch.WordTrace tailWord_1373713 prefixEnd_1373713 313500022368839589008851 := by
  unfold tailWord_1373713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50103429272279887347133793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33402286181519924898089195 50103429272279887347133793)
  ·
    refine ⟨37577571954209915510350345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50103429272279887347133793 37577571954209915510350345)
    ·
      refine ⟨28183178965657436632762759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37577571954209915510350345 28183178965657436632762759)
      ·
        refine ⟨42274768448486154949144139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28183178965657436632762759 42274768448486154949144139)
        ·
          refine ⟨63412152672729232423716209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42274768448486154949144139 63412152672729232423716209)
          ·
            refine ⟨47559114504546924317787157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63412152672729232423716209 47559114504546924317787157)
            ·
              refine ⟨2229333492400637077396273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47559114504546924317787157 2229333492400637077396273)
              ·
                refine ⟨1672000119300477808047205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229333492400637077396273 1672000119300477808047205)
                ·
                  refine ⟨313500022368839589008851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672000119300477808047205 313500022368839589008851)
                  ·
                    rfl

theorem cell21_1373713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_1373713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373713 prefixEnd_1373713 := by exact prefixLift 1373713
  have htrace : WordTrace (prefixWord ++ tailWord_1373713) baseStart_1373713 baseEnd_1373713 := by
    simpa [prefixWord, tailWord_1373713, baseEnd_1373713] using wordTrace_append hprefix tailTrace_1373713
  have hstable : (prefixWord ++ tailWord_1373713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373713).length < 2 ^ (prefixWord ++ tailWord_1373713).sum := by decide
  have hdescent : baseEnd_1373713 < baseStart_1373713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373727 : List Nat := [1, 1, 2, 4, 1, 1, 5, 6]
def baseStart_1373727 : Nat := 118140960795 + 1373727 * 2 ^ 59
def prefixEnd_1373727 : Nat := 4983230072969 + 3 ^ 40 * 1373727 * 2
def baseEnd_1373727 : Nat := 104501072453192891925163

theorem tailTrace_1373727 : CollatzResearch.WordTrace tailWord_1373727 prefixEnd_1373727 104501072453192891925163 := by
  unfold tailWord_1373727
  simp only [CollatzResearch.WordTrace]
  refine ⟨50103939894229167738143435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33402626596152778492095623 50103939894229167738143435)
  ·
    refine ⟨75155909841343751607215153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50103939894229167738143435 75155909841343751607215153)
    ·
      refine ⟨56366932381007813705411365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75155909841343751607215153 56366932381007813705411365)
      ·
        refine ⟨10568799821438965069764631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56366932381007813705411365 10568799821438965069764631)
        ·
          refine ⟨15853199732158447604646947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568799821438965069764631 15853199732158447604646947)
          ·
            refine ⟨23779799598237671406970421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853199732158447604646947 23779799598237671406970421)
            ·
              refine ⟨2229356212334781694403477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23779799598237671406970421 2229356212334781694403477)
              ·
                refine ⟨104501072453192891925163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2229356212334781694403477 104501072453192891925163)
                ·
                  rfl

theorem cell21_1373727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_1373727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373727 prefixEnd_1373727 := by exact prefixLift 1373727
  have htrace : WordTrace (prefixWord ++ tailWord_1373727) baseStart_1373727 baseEnd_1373727 := by
    simpa [prefixWord, tailWord_1373727, baseEnd_1373727] using wordTrace_append hprefix tailTrace_1373727
  have hstable : (prefixWord ++ tailWord_1373727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373727).length < 2 ^ (prefixWord ++ tailWord_1373727).sum := by decide
  have hdescent : baseEnd_1373727 < baseStart_1373727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373924 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1373924 : Nat := 118140960795 + 1373924 * 2 ^ 59
def prefixEnd_1373924 : Nat := 4983230072969 + 3 ^ 40 * 1373924 * 2
def baseEnd_1373924 : Nat := 313548175443550110991753

theorem tailTrace_1373924 : CollatzResearch.WordTrace tailWord_1373924 prefixEnd_1373924 313548175443550110991753 := by
  unfold tailWord_1373924
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055562537257735191532413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33407416716343646922043217 25055562537257735191532413)
  ·
    refine ⟨9395835951471650696824655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25055562537257735191532413 9395835951471650696824655)
    ·
      refine ⟨14093753927207476045236983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395835951471650696824655 14093753927207476045236983)
      ·
        refine ⟨21140630890811214067855475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093753927207476045236983 21140630890811214067855475)
        ·
          refine ⟨31710946336216821101783213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21140630890811214067855475 31710946336216821101783213)
          ·
            refine ⟨11891604876081307913168705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31710946336216821101783213 11891604876081307913168705)
            ·
              refine ⟨8918703657060980934876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11891604876081307913168705 8918703657060980934876529)
              ·
                refine ⟨6689027742795735701157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8918703657060980934876529 6689027742795735701157397)
                ·
                  refine ⟨313548175443550110991753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6689027742795735701157397 313548175443550110991753)
                  ·
                    rfl

theorem cell21_1373924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1373924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1373924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1373924 prefixEnd_1373924 := by exact prefixLift 1373924
  have htrace : WordTrace (prefixWord ++ tailWord_1373924) baseStart_1373924 baseEnd_1373924 := by
    simpa [prefixWord, tailWord_1373924, baseEnd_1373924] using wordTrace_append hprefix tailTrace_1373924
  have hstable : (prefixWord ++ tailWord_1373924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373924).length < 2 ^ (prefixWord ++ tailWord_1373924).sum := by decide
  have hdescent : baseEnd_1373924 < baseStart_1373924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
