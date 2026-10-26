import V185TrunkScan22Chunk405

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3621333 : List Nat := [1, 3, 2, 3, 1, 4, 8]
def baseStart_3621333 : Nat := 118140960795 + 3621333 * 2 ^ 59
def prefixEnd_3621333 : Nat := 4983230072969 + 3 ^ 40 * 3621333 * 2
def baseEnd_3621333 : Nat := 45913196024404574115637

theorem tailTrace_3621333 : CollatzResearch.WordTrace tailWord_3621333 prefixEnd_3621333 45913196024404574115637 := by
  unfold tailWord_3621333
  simp only [CollatzResearch.WordTrace]
  refine ⟨132080865389536490282244653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88053910259690993521496435 132080865389536490282244653)
  ·
    refine ⟨49530324521076183855841745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132080865389536490282244653 49530324521076183855841745)
    ·
      refine ⟨37147743390807137891881309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49530324521076183855841745 37147743390807137891881309)
      ·
        refine ⟨13930403771552676709455491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37147743390807137891881309 13930403771552676709455491)
        ·
          refine ⟨20895605657329015064183237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13930403771552676709455491 20895605657329015064183237)
          ·
            refine ⟨3917926060749190324534357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20895605657329015064183237 3917926060749190324534357)
            ·
              refine ⟨45913196024404574115637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3917926060749190324534357 45913196024404574115637)
              ·
                rfl

theorem cell22_3621333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 8].length) (baseStart_3621333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621333 prefixEnd_3621333 := by exact prefixLift 3621333
  have htrace : WordTrace (prefixWord ++ tailWord_3621333) baseStart_3621333 baseEnd_3621333 := by
    simpa [prefixWord, tailWord_3621333, baseEnd_3621333] using wordTrace_append hprefix tailTrace_3621333
  have hstable : (prefixWord ++ tailWord_3621333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621333).length < 2 ^ (prefixWord ++ tailWord_3621333).sum := by decide
  have hdescent : baseEnd_3621333 < baseStart_3621333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621354 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3621354 : Nat := 118140960795 + 3621354 * 2 ^ 59
def prefixEnd_3621354 : Nat := 4983230072969 + 3 ^ 40 * 3621354 * 2
def baseEnd_3621354 : Nat := 1239663481388086446347135

theorem tailTrace_3621354 : CollatzResearch.WordTrace tailWord_3621354 prefixEnd_3621354 1239663481388086446347135 := by
  unfold tailWord_3621354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33020407830615102717189779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88054420881640273912506077 33020407830615102717189779)
  ·
    refine ⟨49530611745922654075784669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33020407830615102717189779 49530611745922654075784669)
    ·
      refine ⟨18573979404720995278419251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49530611745922654075784669 18573979404720995278419251)
      ·
        refine ⟨27860969107081492917628877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573979404720995278419251 27860969107081492917628877)
        ·
          refine ⟨10447863415155559844110829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27860969107081492917628877 10447863415155559844110829)
          ·
            refine ⟨3917948780683334941541561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10447863415155559844110829 3917948780683334941541561)
            ·
              refine ⟨2938461585512501206156171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917948780683334941541561 2938461585512501206156171)
              ·
                refine ⟨4407692378268751809234257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938461585512501206156171 4407692378268751809234257)
                ·
                  refine ⟨3305769283701563856925693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407692378268751809234257 3305769283701563856925693)
                  ·
                    refine ⟨1239663481388086446347135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305769283701563856925693 1239663481388086446347135)
                    ·
                      rfl

theorem cell22_3621354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3621354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621354 prefixEnd_3621354 := by exact prefixLift 3621354
  have htrace : WordTrace (prefixWord ++ tailWord_3621354) baseStart_3621354 baseEnd_3621354 := by
    simpa [prefixWord, tailWord_3621354, baseEnd_3621354] using wordTrace_append hprefix tailTrace_3621354
  have hstable : (prefixWord ++ tailWord_3621354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621354).length < 2 ^ (prefixWord ++ tailWord_3621354).sum := by decide
  have hdescent : baseEnd_3621354 < baseStart_3621354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621440 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_3621440 : Nat := 118140960795 + 3621440 * 2 ^ 59
def prefixEnd_3621440 : Nat := 4983230072969 + 3 ^ 40 * 3621440 * 2
def baseEnd_3621440 : Nat := 413230973648536962898957

theorem tailTrace_3621440 : CollatzResearch.WordTrace tailWord_3621440 prefixEnd_3621440 413230973648536962898957 := by
  unfold tailWord_3621440
  simp only [CollatzResearch.WordTrace]
  refine ⟨66042384000074423778194887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88056512000099231704259849 66042384000074423778194887)
  ·
    refine ⟨99063576000111635667292331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66042384000074423778194887 99063576000111635667292331)
    ·
      refine ⟨148595364000167453500938497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99063576000111635667292331 148595364000167453500938497)
      ·
        refine ⟨111446523000125590125703873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148595364000167453500938497 111446523000125590125703873)
        ·
          refine ⟨83584892250094192594277905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111446523000125590125703873 83584892250094192594277905)
          ·
            refine ⟨62688669187570644445708429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83584892250094192594277905 62688669187570644445708429)
            ·
              refine ⟨23508250945338991667140661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62688669187570644445708429 23508250945338991667140661)
              ·
                refine ⟨2203898526125530468794437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23508250945338991667140661 2203898526125530468794437)
                ·
                  refine ⟨413230973648536962898957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203898526125530468794437 413230973648536962898957)
                  ·
                    rfl

theorem cell22_3621440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_3621440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621440 prefixEnd_3621440 := by exact prefixLift 3621440
  have htrace : WordTrace (prefixWord ++ tailWord_3621440) baseStart_3621440 baseEnd_3621440 := by
    simpa [prefixWord, tailWord_3621440, baseEnd_3621440] using wordTrace_append hprefix tailTrace_3621440
  have hstable : (prefixWord ++ tailWord_3621440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621440).length < 2 ^ (prefixWord ++ tailWord_3621440).sum := by decide
  have hdescent : baseEnd_3621440 < baseStart_3621440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621485 : List Nat := [1, 5, 1, 1, 3, 2, 1, 8]
def baseStart_3621485 : Nat := 118140960795 + 3621485 * 2 ^ 59
def prefixEnd_3621485 : Nat := 4983230072969 + 3 ^ 40 * 3621485 * 2
def baseEnd_3621485 : Nat := 137745369485027307924637

theorem tailTrace_3621485 : CollatzResearch.WordTrace tailWord_3621485 prefixEnd_3621485 137745369485027307924637 := by
  unfold tailWord_3621485
  simp only [CollatzResearch.WordTrace]
  refine ⟨132086409284985820241777909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88057606189990546827851939 132086409284985820241777909)
  ·
    refine ⟨12383100870467420647666679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132086409284985820241777909 12383100870467420647666679)
    ·
      refine ⟨18574651305701130971500019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383100870467420647666679 18574651305701130971500019)
      ·
        refine ⟨27861976958551696457250029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18574651305701130971500019 27861976958551696457250029)
        ·
          refine ⟨10448241359456886171468761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27861976958551696457250029 10448241359456886171468761)
          ·
            refine ⟨7836181019592664628601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448241359456886171468761 7836181019592664628601571)
            ·
              refine ⟨11754271529388996942902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836181019592664628601571 11754271529388996942902357)
              ·
                refine ⟨137745369485027307924637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11754271529388996942902357 137745369485027307924637)
                ·
                  rfl

theorem cell22_3621485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 8].length) (baseStart_3621485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621485 prefixEnd_3621485 := by exact prefixLift 3621485
  have htrace : WordTrace (prefixWord ++ tailWord_3621485) baseStart_3621485 baseEnd_3621485 := by
    simpa [prefixWord, tailWord_3621485, baseEnd_3621485] using wordTrace_append hprefix tailTrace_3621485
  have hstable : (prefixWord ++ tailWord_3621485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621485).length < 2 ^ (prefixWord ++ tailWord_3621485).sum := by decide
  have hdescent : baseEnd_3621485 < baseStart_3621485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621500 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_3621500 : Nat := 118140960795 + 3621500 * 2 ^ 59
def prefixEnd_3621500 : Nat := 4983230072969 + 3 ^ 40 * 3621500 * 2
def baseEnd_3621500 : Nat := 1239713460171790732196687

theorem tailTrace_3621500 : CollatzResearch.WordTrace tailWord_3621500 prefixEnd_3621500 1239713460171790732196687 := by
  unfold tailWord_3621500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66043478189965738901786977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88057970919954318535715969 66043478189965738901786977)
  ·
    refine ⟨49532608642474304176340233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66043478189965738901786977 49532608642474304176340233)
    ·
      refine ⟨37149456481855728132255175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49532608642474304176340233 37149456481855728132255175)
      ·
        refine ⟨55724184722783592198382763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37149456481855728132255175 55724184722783592198382763)
        ·
          refine ⟨83586277084175388297574145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55724184722783592198382763 83586277084175388297574145)
          ·
            refine ⟨62689707813131541223180609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83586277084175388297574145 62689707813131541223180609)
            ·
              refine ⟨47017280859848655917385457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62689707813131541223180609 47017280859848655917385457)
              ·
                refine ⟨35262960644886491938039093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47017280859848655917385457 35262960644886491938039093)
                ·
                  refine ⟨3305902560458108619191165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35262960644886491938039093 3305902560458108619191165)
                  ·
                    refine ⟨1239713460171790732196687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305902560458108619191165 1239713460171790732196687)
                    ·
                      rfl

theorem cell22_3621500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_3621500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621500 prefixEnd_3621500 := by exact prefixLift 3621500
  have htrace : WordTrace (prefixWord ++ tailWord_3621500) baseStart_3621500 baseEnd_3621500 := by
    simpa [prefixWord, tailWord_3621500, baseEnd_3621500] using wordTrace_append hprefix tailTrace_3621500
  have hstable : (prefixWord ++ tailWord_3621500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621500).length < 2 ^ (prefixWord ++ tailWord_3621500).sum := by decide
  have hdescent : baseEnd_3621500 < baseStart_3621500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621622 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3621622 : Nat := 118140960795 + 3621622 * 2 ^ 59
def prefixEnd_3621622 : Nat := 4983230072969 + 3 ^ 40 * 3621622 * 2
def baseEnd_3621622 : Nat := 1239755223265023080646313

theorem tailTrace_3621622 : CollatzResearch.WordTrace tailWord_3621622 prefixEnd_3621622 1239755223265023080646313 := by
  unfold tailWord_3621622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255712880343093289969695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88060937390326328426343413 8255712880343093289969695)
  ·
    refine ⟨12383569320514639934954543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255712880343093289969695 12383569320514639934954543)
    ·
      refine ⟨18575353980771959902431815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383569320514639934954543 18575353980771959902431815)
      ·
        refine ⟨27863030971157939853647723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18575353980771959902431815 27863030971157939853647723)
        ·
          refine ⟨41794546456736909780471585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27863030971157939853647723 41794546456736909780471585)
          ·
            refine ⟨31345909842552682335353689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41794546456736909780471585 31345909842552682335353689)
            ·
              refine ⟨23509432381914511751515267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31345909842552682335353689 23509432381914511751515267)
              ·
                refine ⟨35264148572871767627272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23509432381914511751515267 35264148572871767627272901)
                ·
                  refine ⟨6612027857413456430113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35264148572871767627272901 6612027857413456430113669)
                  ·
                    refine ⟨1239755223265023080646313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612027857413456430113669 1239755223265023080646313)
                    ·
                      rfl

theorem cell22_3621622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3621622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621622 prefixEnd_3621622 := by exact prefixLift 3621622
  have htrace : WordTrace (prefixWord ++ tailWord_3621622) baseStart_3621622 baseEnd_3621622 := by
    simpa [prefixWord, tailWord_3621622, baseEnd_3621622] using wordTrace_append hprefix tailTrace_3621622
  have hstable : (prefixWord ++ tailWord_3621622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621622).length < 2 ^ (prefixWord ++ tailWord_3621622).sum := by decide
  have hdescent : baseEnd_3621622 < baseStart_3621622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621665 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 9]
def baseStart_3621665 : Nat := 118140960795 + 3621665 * 2 ^ 59
def prefixEnd_3621665 : Nat := 4983230072969 + 3 ^ 40 * 3621665 * 2
def baseEnd_3621665 : Nat := 413256647681261767273727

theorem tailTrace_3621665 : CollatzResearch.WordTrace tailWord_3621665 prefixEnd_3621665 413256647681261767273727 := by
  unfold tailWord_3621665
  simp only [CollatzResearch.WordTrace]
  refine ⟨132092974424333710983330449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88061982949555807322220299 132092974424333710983330449)
  ·
    refine ⟨99069730818250283237497837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132092974424333710983330449 99069730818250283237497837)
    ·
      refine ⟨37151149056843856214061689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99069730818250283237497837 37151149056843856214061689)
      ·
        refine ⟨27863361792632892160546267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37151149056843856214061689 27863361792632892160546267)
        ·
          refine ⟨41795042688949338240819401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27863361792632892160546267 41795042688949338240819401)
          ·
            refine ⟨31346282016712003680614551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41795042688949338240819401 31346282016712003680614551)
            ·
              refine ⟨47019423025068005520921827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31346282016712003680614551 47019423025068005520921827)
              ·
                refine ⟨70529134537602008281382741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47019423025068005520921827 70529134537602008281382741)
                ·
                  refine ⟨413256647681261767273727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70529134537602008281382741 413256647681261767273727)
                  ·
                    rfl

theorem cell22_3621665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_3621665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621665 prefixEnd_3621665 := by exact prefixLift 3621665
  have htrace : WordTrace (prefixWord ++ tailWord_3621665) baseStart_3621665 baseEnd_3621665 := by
    simpa [prefixWord, tailWord_3621665, baseEnd_3621665] using wordTrace_append hprefix tailTrace_3621665
  have hstable : (prefixWord ++ tailWord_3621665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621665).length < 2 ^ (prefixWord ++ tailWord_3621665).sum := by decide
  have hdescent : baseEnd_3621665 < baseStart_3621665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621680 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_3621680 : Nat := 118140960795 + 3621680 * 2 ^ 59
def prefixEnd_3621680 : Nat := 4983230072969 + 3 ^ 40 * 3621680 * 2
def baseEnd_3621680 : Nat := 1239775077850330262696135

theorem tailTrace_3621680 : CollatzResearch.WordTrace tailWord_3621680 prefixEnd_3621680 1239775077850330262696135 := by
  unfold tailWord_3621680
  simp only [CollatzResearch.WordTrace]
  refine ⟨66046760759639684272563247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88062347679519579030084329 66046760759639684272563247)
  ·
    refine ⟨99070141139459526408844871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66046760759639684272563247 99070141139459526408844871)
    ·
      refine ⟨148605211709189289613267307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99070141139459526408844871 148605211709189289613267307)
      ·
        refine ⟨222907817563783934419900961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148605211709189289613267307 222907817563783934419900961)
        ·
          refine ⟨167180863172837950814925721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222907817563783934419900961 167180863172837950814925721)
          ·
            refine ⟨125385647379628463111194291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167180863172837950814925721 125385647379628463111194291)
            ·
              refine ⟨188078471069442694666791437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125385647379628463111194291 188078471069442694666791437)
              ·
                refine ⟨70529426651041010500046789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188078471069442694666791437 70529426651041010500046789)
                ·
                  refine ⟨13224267497070189468758773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70529426651041010500046789 13224267497070189468758773)
                  ·
                    refine ⟨1239775077850330262696135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13224267497070189468758773 1239775077850330262696135)
                    ·
                      rfl

theorem cell22_3621680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_3621680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621680 prefixEnd_3621680 := by exact prefixLift 3621680
  have htrace : WordTrace (prefixWord ++ tailWord_3621680) baseStart_3621680 baseEnd_3621680 := by
    simpa [prefixWord, tailWord_3621680, baseEnd_3621680] using wordTrace_append hprefix tailTrace_3621680
  have hstable : (prefixWord ++ tailWord_3621680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621680).length < 2 ^ (prefixWord ++ tailWord_3621680).sum := by decide
  have hdescent : baseEnd_3621680 < baseStart_3621680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621682 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3621682 : Nat := 118140960795 + 3621682 * 2 ^ 59
def prefixEnd_3621682 : Nat := 4983230072969 + 3 ^ 40 * 3621682 * 2
def baseEnd_3621682 : Nat := 413258587497067641382043

theorem tailTrace_3621682 : CollatzResearch.WordTrace tailWord_3621682 prefixEnd_3621682 413258587497067641382043 := by
  unfold tailWord_3621682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33023398616318030721674825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88062396310181415257799533 33023398616318030721674825)
  ·
    refine ⟨24767548962238523041256119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33023398616318030721674825 24767548962238523041256119)
    ·
      refine ⟨37151323443357784561884179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24767548962238523041256119 37151323443357784561884179)
      ·
        refine ⟨55726985165036676842826269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37151323443357784561884179 55726985165036676842826269)
        ·
          refine ⟨20897619436888753816059851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55726985165036676842826269 20897619436888753816059851)
          ·
            refine ⟨31346429155333130724089777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20897619436888753816059851 31346429155333130724089777)
            ·
              refine ⟨23509821866499848043067333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31346429155333130724089777 23509821866499848043067333)
              ·
                refine ⟨4408091599968721508075125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23509821866499848043067333 4408091599968721508075125)
                ·
                  refine ⟨413258587497067641382043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4408091599968721508075125 413258587497067641382043)
                  ·
                    rfl

theorem cell22_3621682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3621682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621682 prefixEnd_3621682 := by exact prefixLift 3621682
  have htrace : WordTrace (prefixWord ++ tailWord_3621682) baseStart_3621682 baseEnd_3621682 := by
    simpa [prefixWord, tailWord_3621682, baseEnd_3621682] using wordTrace_append hprefix tailTrace_3621682
  have hstable : (prefixWord ++ tailWord_3621682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621682).length < 2 ^ (prefixWord ++ tailWord_3621682).sum := by decide
  have hdescent : baseEnd_3621682 < baseStart_3621682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621757 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3621757 : Nat := 118140960795 + 3621757 * 2 ^ 59
def prefixEnd_3621757 : Nat := 4983230072969 + 3 ^ 40 * 3621757 * 2
def baseEnd_3621757 : Nat := 1239801436523927728520899

theorem tailTrace_3621757 : CollatzResearch.WordTrace tailWord_3621757 prefixEnd_3621757 1239801436523927728520899 := by
  unfold tailWord_3621757
  simp only [CollatzResearch.WordTrace]
  refine ⟨132096329940000410695679525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88064219960000273797119683 132096329940000410695679525)
  ·
    refine ⟨24768061863750077005439911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132096329940000410695679525 24768061863750077005439911)
    ·
      refine ⟨37152092795625115508159867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24768061863750077005439911 37152092795625115508159867)
      ·
        refine ⟨55728139193437673262239801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37152092795625115508159867 55728139193437673262239801)
        ·
          refine ⟨41796104395078254946679851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55728139193437673262239801 41796104395078254946679851)
          ·
            refine ⟨62694156592617382420019777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41796104395078254946679851 62694156592617382420019777)
            ·
              refine ⟨47020617444463036815014833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62694156592617382420019777 47020617444463036815014833)
              ·
                refine ⟨35265463083347277611261125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47020617444463036815014833 35265463083347277611261125)
                ·
                  refine ⟨6612274328127614552111461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35265463083347277611261125 6612274328127614552111461)
                  ·
                    refine ⟨1239801436523927728520899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612274328127614552111461 1239801436523927728520899)
                    ·
                      rfl

theorem cell22_3621757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3621757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621757 prefixEnd_3621757 := by exact prefixLift 3621757
  have htrace : WordTrace (prefixWord ++ tailWord_3621757) baseStart_3621757 baseEnd_3621757 := by
    simpa [prefixWord, tailWord_3621757, baseEnd_3621757] using wordTrace_append hprefix tailTrace_3621757
  have hstable : (prefixWord ++ tailWord_3621757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621757).length < 2 ^ (prefixWord ++ tailWord_3621757).sum := by decide
  have hdescent : baseEnd_3621757 < baseStart_3621757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621759 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 2, 3]
def baseStart_3621759 : Nat := 118140960795 + 3621759 * 2 ^ 59
def prefixEnd_3621759 : Nat := 4983230072969 + 3 ^ 40 * 3621759 * 2
def baseEnd_3621759 : Nat := 1239802121164800389970893

theorem tailTrace_3621759 : CollatzResearch.WordTrace tailWord_3621759 prefixEnd_3621759 1239802121164800389970893 := by
  unfold tailWord_3621759
  simp only [CollatzResearch.WordTrace]
  refine ⟨132096402885993165037252331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88064268590662110024834887 132096402885993165037252331)
  ·
    refine ⟨198144604328989747555878497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132096402885993165037252331 198144604328989747555878497)
    ·
      refine ⟨148608453246742310666908873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198144604328989747555878497 148608453246742310666908873)
      ·
        refine ⟨111456339935056733000181655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148608453246742310666908873 111456339935056733000181655)
        ·
          refine ⟨167184509902585099500272483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111456339935056733000181655 167184509902585099500272483)
          ·
            refine ⟨250776764853877649250408725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167184509902585099500272483 250776764853877649250408725)
            ·
              refine ⟨11755160852525514808612909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250776764853877649250408725 11755160852525514808612909)
              ·
                refine ⟨4408185319697068053229841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755160852525514808612909 4408185319697068053229841)
                ·
                  refine ⟨3306138989772801039922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408185319697068053229841 3306138989772801039922381)
                  ·
                    refine ⟨1239802121164800389970893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306138989772801039922381 1239802121164800389970893)
                    ·
                      rfl

theorem cell22_3621759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_3621759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621759 prefixEnd_3621759 := by exact prefixLift 3621759
  have htrace : WordTrace (prefixWord ++ tailWord_3621759) baseStart_3621759 baseEnd_3621759 := by
    simpa [prefixWord, tailWord_3621759, baseEnd_3621759] using wordTrace_append hprefix tailTrace_3621759
  have hstable : (prefixWord ++ tailWord_3621759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621759).length < 2 ^ (prefixWord ++ tailWord_3621759).sum := by decide
  have hdescent : baseEnd_3621759 < baseStart_3621759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621778 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3621778 : Nat := 118140960795 + 3621778 * 2 ^ 59
def prefixEnd_3621778 : Nat := 4983230072969 + 3 ^ 40 * 3621778 * 2
def baseEnd_3621778 : Nat := 413269541751030224581945

theorem tailTrace_3621778 : CollatzResearch.WordTrace tailWord_3621778 prefixEnd_3621778 413269541751030224581945 := by
  unfold tailWord_3621778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024273968231082820548497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88064730581949554188129325 33024273968231082820548497)
  ·
    refine ⟨24768205476173312115411373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33024273968231082820548497 24768205476173312115411373)
    ·
      refine ⟨9288077053564992043279265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24768205476173312115411373 9288077053564992043279265)
      ·
        refine ⟨6966057790173744032459449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9288077053564992043279265 6966057790173744032459449)
        ·
          refine ⟨5224543342630308024344587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6966057790173744032459449 5224543342630308024344587)
          ·
            refine ⟨7836815013945462036516881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224543342630308024344587 7836815013945462036516881)
            ·
              refine ⟨5877611260459096527387661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7836815013945462036516881 5877611260459096527387661)
              ·
                refine ⟨2204104222672161197770373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877611260459096527387661 2204104222672161197770373)
                ·
                  refine ⟨413269541751030224581945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204104222672161197770373 413269541751030224581945)
                  ·
                    rfl

theorem cell22_3621778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3621778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621778 prefixEnd_3621778 := by exact prefixLift 3621778
  have htrace : WordTrace (prefixWord ++ tailWord_3621778) baseStart_3621778 baseEnd_3621778 := by
    simpa [prefixWord, tailWord_3621778, baseEnd_3621778] using wordTrace_append hprefix tailTrace_3621778
  have hstable : (prefixWord ++ tailWord_3621778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621778).length < 2 ^ (prefixWord ++ tailWord_3621778).sum := by decide
  have hdescent : baseEnd_3621778 < baseStart_3621778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621793 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3621793 : Nat := 118140960795 + 3621793 * 2 ^ 59
def prefixEnd_3621793 : Nat := 4983230072969 + 3 ^ 40 * 3621793 * 2
def baseEnd_3621793 : Nat := 1239813760059635634620789

theorem tailTrace_3621793 : CollatzResearch.WordTrace tailWord_3621793 prefixEnd_3621793 1239813760059635634620789 := by
  unfold tailWord_3621793
  simp only [CollatzResearch.WordTrace]
  refine ⟨132097642967869988843990033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88065095311913325895993355 132097642967869988843990033)
  ·
    refine ⟨99073232225902491632992525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132097642967869988843990033 99073232225902491632992525)
    ·
      refine ⟨37152462084713434362372197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99073232225902491632992525 37152462084713434362372197)
      ·
        refine ⟨6966086640883768942944787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37152462084713434362372197 6966086640883768942944787)
        ·
          refine ⟨10449129961325653414417181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966086640883768942944787 10449129961325653414417181)
          ·
            refine ⟨3918423735497120030406443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10449129961325653414417181 3918423735497120030406443)
            ·
              refine ⟨5877635603245680045609665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918423735497120030406443 5877635603245680045609665)
              ·
                refine ⟨4408226702434260034207249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877635603245680045609665 4408226702434260034207249)
                ·
                  refine ⟨3306170026825695025655437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408226702434260034207249 3306170026825695025655437)
                  ·
                    refine ⟨1239813760059635634620789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306170026825695025655437 1239813760059635634620789)
                    ·
                      rfl

theorem cell22_3621793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3621793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621793 prefixEnd_3621793 := by exact prefixLift 3621793
  have htrace : WordTrace (prefixWord ++ tailWord_3621793) baseStart_3621793 baseEnd_3621793 := by
    simpa [prefixWord, tailWord_3621793, baseEnd_3621793] using wordTrace_append hprefix tailTrace_3621793
  have hstable : (prefixWord ++ tailWord_3621793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621793).length < 2 ^ (prefixWord ++ tailWord_3621793).sum := by decide
  have hdescent : baseEnd_3621793 < baseStart_3621793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621838 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3621838 : Nat := 118140960795 + 3621838 * 2 ^ 59
def prefixEnd_3621838 : Nat := 4983230072969 + 3 ^ 40 * 3621838 * 2
def baseEnd_3621838 : Nat := 1239829164479270517245651

theorem tailTrace_3621838 : CollatzResearch.WordTrace tailWord_3621838 prefixEnd_3621838 1239829164479270517245651 := by
  unfold tailWord_3621838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512410531588370191172271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88066189501804641019585445 16512410531588370191172271)
  ·
    refine ⟨24768615797382555286758407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16512410531588370191172271 24768615797382555286758407)
    ·
      refine ⟨37152923696073832930137611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24768615797382555286758407 37152923696073832930137611)
      ·
        refine ⟨55729385544110749395206417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37152923696073832930137611 55729385544110749395206417)
        ·
          refine ⟨41797039158083062046404813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55729385544110749395206417 41797039158083062046404813)
          ·
            refine ⟨15673889684281148267401805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41797039158083062046404813 15673889684281148267401805)
            ·
              refine ⟨5877708631605430600275677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15673889684281148267401805 5877708631605430600275677)
              ·
                refine ⟨2204140736852036475103379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877708631605430600275677 2204140736852036475103379)
                ·
                  refine ⟨3306211105278054712655069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204140736852036475103379 3306211105278054712655069)
                  ·
                    refine ⟨1239829164479270517245651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306211105278054712655069 1239829164479270517245651)
                    ·
                      rfl

theorem cell22_3621838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3621838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621838 prefixEnd_3621838 := by exact prefixLift 3621838
  have htrace : WordTrace (prefixWord ++ tailWord_3621838) baseStart_3621838 baseEnd_3621838 := by
    simpa [prefixWord, tailWord_3621838, baseEnd_3621838] using wordTrace_append hprefix tailTrace_3621838
  have hstable : (prefixWord ++ tailWord_3621838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621838).length < 2 ^ (prefixWord ++ tailWord_3621838).sum := by decide
  have hdescent : baseEnd_3621838 < baseStart_3621838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621855 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 1, 3]
def baseStart_3621855 : Nat := 118140960795 + 3621855 * 2 ^ 59
def prefixEnd_3621855 : Nat := 4983230072969 + 3 ^ 40 * 3621855 * 2
def baseEnd_3621855 : Nat := 1239834983926688139570599

theorem tailTrace_3621855 : CollatzResearch.WordTrace tailWord_3621855 prefixEnd_3621855 1239834983926688139570599 := by
  unfold tailWord_3621855
  simp only [CollatzResearch.WordTrace]
  refine ⟨132099904293645373432747019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88066602862430248955164679 132099904293645373432747019)
  ·
    refine ⟨198149856440468060149120529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132099904293645373432747019 198149856440468060149120529)
    ·
      refine ⟨148612392330351045111840397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198149856440468060149120529 148612392330351045111840397)
      ·
        refine ⟨55729647123881641916940149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148612392330351045111840397 55729647123881641916940149)
        ·
          refine ⟨5224654417863903929713139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55729647123881641916940149 5224654417863903929713139)
          ·
            refine ⟨7836981626795855894569709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224654417863903929713139 7836981626795855894569709)
            ·
              refine ⟨2938868110048445960463641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7836981626795855894569709 2938868110048445960463641)
              ·
                refine ⟨2204151082536334470347731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938868110048445960463641 2204151082536334470347731)
                ·
                  refine ⟨3306226623804501705521597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204151082536334470347731 3306226623804501705521597)
                  ·
                    refine ⟨1239834983926688139570599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306226623804501705521597 1239834983926688139570599)
                    ·
                      rfl

theorem cell22_3621855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_3621855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621855 prefixEnd_3621855 := by exact prefixLift 3621855
  have htrace : WordTrace (prefixWord ++ tailWord_3621855) baseStart_3621855 baseEnd_3621855 := by
    simpa [prefixWord, tailWord_3621855, baseEnd_3621855] using wordTrace_append hprefix tailTrace_3621855
  have hstable : (prefixWord ++ tailWord_3621855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621855).length < 2 ^ (prefixWord ++ tailWord_3621855).sum := by decide
  have hdescent : baseEnd_3621855 < baseStart_3621855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621898 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3621898 : Nat := 118140960795 + 3621898 * 2 ^ 59
def prefixEnd_3621898 : Nat := 4983230072969 + 3 ^ 40 * 3621898 * 2
def baseEnd_3621898 : Nat := 1239849703705450360745467

theorem tailTrace_3621898 : CollatzResearch.WordTrace tailWord_3621898 prefixEnd_3621898 1239849703705450360745467 := by
  unfold tailWord_3621898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33025368158122397944140587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88067648421659727851041565 33025368158122397944140587)
  ·
    refine ⟨49538052237183596916210881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33025368158122397944140587 49538052237183596916210881)
    ·
      refine ⟨37153539177887697687158161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49538052237183596916210881 37153539177887697687158161)
      ·
        refine ⟨27865154383415773265368621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37153539177887697687158161 27865154383415773265368621)
        ·
          refine ⟨10449432893780914974513233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27865154383415773265368621 10449432893780914974513233)
          ·
            refine ⟨7837074670335686230884925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10449432893780914974513233 7837074670335686230884925)
            ·
              refine ⟨2938903001375882336581847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7837074670335686230884925 2938903001375882336581847)
              ·
                refine ⟨4408354502063823504872771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938903001375882336581847 4408354502063823504872771)
                ·
                  refine ⟨6612531753095735257309157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408354502063823504872771 6612531753095735257309157)
                  ·
                    refine ⟨1239849703705450360745467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612531753095735257309157 1239849703705450360745467)
                    ·
                      rfl

theorem cell22_3621898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3621898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621898 prefixEnd_3621898 := by exact prefixLift 3621898
  have htrace : WordTrace (prefixWord ++ tailWord_3621898) baseStart_3621898 baseEnd_3621898 := by
    simpa [prefixWord, tailWord_3621898, baseEnd_3621898] using wordTrace_append hprefix tailTrace_3621898
  have hstable : (prefixWord ++ tailWord_3621898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621898).length < 2 ^ (prefixWord ++ tailWord_3621898).sum := by decide
  have hdescent : baseEnd_3621898 < baseStart_3621898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621906 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3621906 : Nat := 118140960795 + 3621906 * 2 ^ 59
def prefixEnd_3621906 : Nat := 4983230072969 + 3 ^ 40 * 3621906 * 2
def baseEnd_3621906 : Nat := 1239852442268941006545443

theorem tailTrace_3621906 : CollatzResearch.WordTrace tailWord_3621906 prefixEnd_3621906 1239852442268941006545443 := by
  unfold tailWord_3621906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33025441104115152285713393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88067842944307072761902381 33025441104115152285713393)
  ·
    refine ⟨24769080828086364214285045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33025441104115152285713393 24769080828086364214285045)
    ·
      refine ⟨2322101327633096645089223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24769080828086364214285045 2322101327633096645089223)
      ·
        refine ⟨3483151991449644967633835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322101327633096645089223 3483151991449644967633835)
        ·
          refine ⟨5224727987174467451450753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483151991449644967633835 5224727987174467451450753)
          ·
            refine ⟨3918545990380850588588065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224727987174467451450753 3918545990380850588588065)
            ·
              refine ⟨2938909492785637941441049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918545990380850588588065 2938909492785637941441049)
              ·
                refine ⟨2204182119589228456080787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938909492785637941441049 2204182119589228456080787)
                ·
                  refine ⟨3306273179383842684121181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204182119589228456080787 3306273179383842684121181)
                  ·
                    refine ⟨1239852442268941006545443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306273179383842684121181 1239852442268941006545443)
                    ·
                      rfl

theorem cell22_3621906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3621906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621906 prefixEnd_3621906 := by exact prefixLift 3621906
  have htrace : WordTrace (prefixWord ++ tailWord_3621906) baseStart_3621906 baseEnd_3621906 := by
    simpa [prefixWord, tailWord_3621906, baseEnd_3621906] using wordTrace_append hprefix tailTrace_3621906
  have hstable : (prefixWord ++ tailWord_3621906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621906).length < 2 ^ (prefixWord ++ tailWord_3621906).sum := by decide
  have hdescent : baseEnd_3621906 < baseStart_3621906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621973 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3621973 : Nat := 118140960795 + 3621973 * 2 ^ 59
def prefixEnd_3621973 : Nat := 4983230072969 + 3 ^ 40 * 3621973 * 2
def baseEnd_3621973 : Nat := 1239875377738175165120237

theorem tailTrace_3621973 : CollatzResearch.WordTrace tailWord_3621973 prefixEnd_3621973 1239875377738175165120237 := by
  unfold tailWord_3621973
  simp only [CollatzResearch.WordTrace]
  refine ⟨132104208107217879585542573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88069472071478586390361715 132104208107217879585542573)
  ·
    refine ⟨49539078040206704844578465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132104208107217879585542573 49539078040206704844578465)
    ·
      refine ⟨37154308530155028633433849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49539078040206704844578465 37154308530155028633433849)
      ·
        refine ⟨27865731397616271475075387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37154308530155028633433849 27865731397616271475075387)
        ·
          refine ⟨41798597096424407212613081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27865731397616271475075387 41798597096424407212613081)
          ·
            refine ⟨31348947822318305409459811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41798597096424407212613081 31348947822318305409459811)
            ·
              refine ⟨47023421733477458114189717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31348947822318305409459811 47023421733477458114189717)
              ·
                refine ⟨2204222893756755849102643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47023421733477458114189717 2204222893756755849102643)
                ·
                  refine ⟨3306334340635133773653965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204222893756755849102643 3306334340635133773653965)
                  ·
                    refine ⟨1239875377738175165120237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306334340635133773653965 1239875377738175165120237)
                    ·
                      rfl

theorem cell22_3621973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3621973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621973 prefixEnd_3621973 := by exact prefixLift 3621973
  have htrace : WordTrace (prefixWord ++ tailWord_3621973) baseStart_3621973 baseEnd_3621973 := by
    simpa [prefixWord, tailWord_3621973, baseEnd_3621973] using wordTrace_append hprefix tailTrace_3621973
  have hstable : (prefixWord ++ tailWord_3621973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621973).length < 2 ^ (prefixWord ++ tailWord_3621973).sum := by decide
  have hdescent : baseEnd_3621973 < baseStart_3621973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621984 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_3621984 : Nat := 118140960795 + 3621984 * 2 ^ 59
def prefixEnd_3621984 : Nat := 4983230072969 + 3 ^ 40 * 3621984 * 2
def baseEnd_3621984 : Nat := 1239879143262974803095203

theorem tailTrace_3621984 : CollatzResearch.WordTrace tailWord_3621984 prefixEnd_3621984 1239879143262974803095203 := by
  unfold tailWord_3621984
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052304655089014232096503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88069739540118685642795337 66052304655089014232096503)
  ·
    refine ⟨99078456982633521348144755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66052304655089014232096503 99078456982633521348144755)
    ·
      refine ⟨148617685473950282022217133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99078456982633521348144755 148617685473950282022217133)
      ·
        refine ⟨55731632052731355758331425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148617685473950282022217133 55731632052731355758331425)
        ·
          refine ⟨41798724039548516818748569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55731632052731355758331425 41798724039548516818748569)
          ·
            refine ⟨31349043029661387614061427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41798724039548516818748569 31349043029661387614061427)
            ·
              refine ⟨47023564544492081421092141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31349043029661387614061427 47023564544492081421092141)
              ·
                refine ⟨17633836704184530532909553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47023564544492081421092141 17633836704184530532909553)
                ·
                  refine ⟨13225377528138397899682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17633836704184530532909553 13225377528138397899682165)
                  ·
                    refine ⟨1239879143262974803095203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13225377528138397899682165 1239879143262974803095203)
                    ·
                      rfl

theorem cell22_3621984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_3621984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3621984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3621984 prefixEnd_3621984 := by exact prefixLift 3621984
  have htrace : WordTrace (prefixWord ++ tailWord_3621984) baseStart_3621984 baseEnd_3621984 := by
    simpa [prefixWord, tailWord_3621984, baseEnd_3621984] using wordTrace_append hprefix tailTrace_3621984
  have hstable : (prefixWord ++ tailWord_3621984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621984).length < 2 ^ (prefixWord ++ tailWord_3621984).sum := by decide
  have hdescent : baseEnd_3621984 < baseStart_3621984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622016 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_3622016 : Nat := 118140960795 + 3622016 * 2 ^ 59
def prefixEnd_3622016 : Nat := 4983230072969 + 3 ^ 40 * 3622016 * 2
def baseEnd_3622016 : Nat := 1239890097516937386295105

theorem tailTrace_3622016 : CollatzResearch.WordTrace tailWord_3622016 prefixEnd_3622016 1239890097516937386295105 := by
  unfold tailWord_3622016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052888223031048964678951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88070517630708065286238601 66052888223031048964678951)
  ·
    refine ⟨99079332334546573447018427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66052888223031048964678951 99079332334546573447018427)
    ·
      refine ⟨148618998501819860170527641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99079332334546573447018427 148618998501819860170527641)
      ·
        refine ⟨111464248876364895127895731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148618998501819860170527641 111464248876364895127895731)
        ·
          refine ⟨167196373314547342691843597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111464248876364895127895731 167196373314547342691843597)
          ·
            refine ⟨62698639992955253509441349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167196373314547342691843597 62698639992955253509441349)
            ·
              refine ⟨11755994998679110033020253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62698639992955253509441349 11755994998679110033020253)
              ·
                refine ⟨4408498124504666262382595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755994998679110033020253 4408498124504666262382595)
                ·
                  refine ⟨6612747186756999393573893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408498124504666262382595 6612747186756999393573893)
                  ·
                    refine ⟨1239890097516937386295105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612747186756999393573893 1239890097516937386295105)
                    ·
                      rfl

theorem cell22_3622016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_3622016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622016 prefixEnd_3622016 := by exact prefixLift 3622016
  have htrace : WordTrace (prefixWord ++ tailWord_3622016) baseStart_3622016 baseEnd_3622016 := by
    simpa [prefixWord, tailWord_3622016, baseEnd_3622016] using wordTrace_append hprefix tailTrace_3622016
  have hstable : (prefixWord ++ tailWord_3622016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622016).length < 2 ^ (prefixWord ++ tailWord_3622016).sum := by decide
  have hdescent : baseEnd_3622016 < baseStart_3622016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622078 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3622078 : Nat := 118140960795 + 3622078 * 2 ^ 59
def prefixEnd_3622078 : Nat := 4983230072969 + 3 ^ 40 * 3622078 * 2
def baseEnd_3622078 : Nat := 1239911321383989891244915

theorem tailTrace_3622078 : CollatzResearch.WordTrace tailWord_3622078 prefixEnd_3622078 1239911321383989891244915 := by
  unfold tailWord_3622078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513504721479685314764361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88072025181224988345409925 16513504721479685314764361)
  ·
    refine ⟨12385128541109763986073271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16513504721479685314764361 12385128541109763986073271)
    ·
      refine ⟨18577692811664645979109907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12385128541109763986073271 18577692811664645979109907)
      ·
        refine ⟨27866539217496968968664861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18577692811664645979109907 27866539217496968968664861)
        ·
          refine ⟨10449952206561363363249323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27866539217496968968664861 10449952206561363363249323)
          ·
            refine ⟨15674928309842045044873985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449952206561363363249323 15674928309842045044873985)
            ·
              refine ⟨11756196232381533783655489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15674928309842045044873985 11756196232381533783655489)
              ·
                refine ⟨8817147174286150337741617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11756196232381533783655489 8817147174286150337741617)
                ·
                  refine ⟨6612860380714612753306213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8817147174286150337741617 6612860380714612753306213)
                  ·
                    refine ⟨1239911321383989891244915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612860380714612753306213 1239911321383989891244915)
                    ·
                      rfl

theorem cell22_3622078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3622078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622078 prefixEnd_3622078 := by exact prefixLift 3622078
  have htrace : WordTrace (prefixWord ++ tailWord_3622078) baseStart_3622078 baseEnd_3622078 := by
    simpa [prefixWord, tailWord_3622078, baseEnd_3622078] using wordTrace_append hprefix tailTrace_3622078
  have hstable : (prefixWord ++ tailWord_3622078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622078).length < 2 ^ (prefixWord ++ tailWord_3622078).sum := by decide
  have hdescent : baseEnd_3622078 < baseStart_3622078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622080 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_3622080 : Nat := 118140960795 + 3622080 * 2 ^ 59
def prefixEnd_3622080 : Nat := 4983230072969 + 3 ^ 40 * 3622080 * 2
def baseEnd_3622080 : Nat := 1239912006024862552694909

theorem tailTrace_3622080 : CollatzResearch.WordTrace tailWord_3622080 prefixEnd_3622080 1239912006024862552694909 := by
  unfold tailWord_3622080
  simp only [CollatzResearch.WordTrace]
  refine ⟨66054055358915118429843847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88072073811886824573125129 66054055358915118429843847)
  ·
    refine ⟨99081083038372677644765771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66054055358915118429843847 99081083038372677644765771)
    ·
      refine ⟨148621624557559016467148657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99081083038372677644765771 148621624557559016467148657)
      ·
        refine ⟨111466218418169262350361493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148621624557559016467148657 111466218418169262350361493)
        ·
          refine ⟨5224978988351684172673195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111466218418169262350361493 5224978988351684172673195)
          ·
            refine ⟨7837468482527526259009793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224978988351684172673195 7837468482527526259009793)
            ·
              refine ⟨5878101361895644694257345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7837468482527526259009793 5878101361895644694257345)
              ·
                refine ⟨4408576021421733520693009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5878101361895644694257345 4408576021421733520693009)
                ·
                  refine ⟨3306432016066300140519757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408576021421733520693009 3306432016066300140519757)
                  ·
                    refine ⟨1239912006024862552694909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306432016066300140519757 1239912006024862552694909)
                    ·
                      rfl

theorem cell22_3622080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_3622080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622080 prefixEnd_3622080 := by exact prefixLift 3622080
  have htrace : WordTrace (prefixWord ++ tailWord_3622080) baseStart_3622080 baseEnd_3622080 := by
    simpa [prefixWord, tailWord_3622080, baseEnd_3622080] using wordTrace_append hprefix tailTrace_3622080
  have hstable : (prefixWord ++ tailWord_3622080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622080).length < 2 ^ (prefixWord ++ tailWord_3622080).sum := by decide
  have hdescent : baseEnd_3622080 < baseStart_3622080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622142 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3622142 : Nat := 118140960795 + 3622142 * 2 ^ 59
def prefixEnd_3622142 : Nat := 4983230072969 + 3 ^ 40 * 3622142 * 2
def baseEnd_3622142 : Nat := 1239933229891915057644719

theorem tailTrace_3622142 : CollatzResearch.WordTrace tailWord_3622142 prefixEnd_3622142 1239933229891915057644719 := by
  unfold tailWord_3622142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513796505450702681055585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88073581362403747632296453 16513796505450702681055585)
  ·
    refine ⟨12385347379088027010791689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16513796505450702681055585 12385347379088027010791689)
    ·
      refine ⟨9289010534316020258093767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12385347379088027010791689 9289010534316020258093767)
      ·
        refine ⟨13933515801474030387140651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289010534316020258093767 13933515801474030387140651)
        ·
          refine ⟨20900273702211045580710977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13933515801474030387140651 20900273702211045580710977)
          ·
            refine ⟨15675205276658284185533233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20900273702211045580710977 15675205276658284185533233)
            ·
              refine ⟨11756403957493713139149925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15675205276658284185533233 11756403957493713139149925)
              ·
                refine ⟨2204325742030071213590611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11756403957493713139149925 2204325742030071213590611)
                ·
                  refine ⟨3306488613045106820385917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204325742030071213590611 3306488613045106820385917)
                  ·
                    refine ⟨1239933229891915057644719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306488613045106820385917 1239933229891915057644719)
                    ·
                      rfl

theorem cell22_3622142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3622142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622142 prefixEnd_3622142 := by exact prefixLift 3622142
  have htrace : WordTrace (prefixWord ++ tailWord_3622142) baseStart_3622142 baseEnd_3622142 := by
    simpa [prefixWord, tailWord_3622142, baseEnd_3622142] using wordTrace_append hprefix tailTrace_3622142
  have hstable : (prefixWord ++ tailWord_3622142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622142).length < 2 ^ (prefixWord ++ tailWord_3622142).sum := by decide
  have hdescent : baseEnd_3622142 < baseStart_3622142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622168 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_3622168 : Nat := 118140960795 + 3622168 * 2 ^ 59
def prefixEnd_3622168 : Nat := 4983230072969 + 3 ^ 40 * 3622168 * 2
def baseEnd_3622168 : Nat := 1239942130223259656494639

theorem tailTrace_3622168 : CollatzResearch.WordTrace tailWord_3622168 prefixEnd_3622168 1239942130223259656494639 := by
  unfold tailWord_3622168
  simp only [CollatzResearch.WordTrace]
  refine ⟨66055660170755713944445579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88074213561007618592594105 66055660170755713944445579)
  ·
    refine ⟨99083490256133570916668369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66055660170755713944445579 99083490256133570916668369)
    ·
      refine ⟨74312617692100178187501277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99083490256133570916668369 74312617692100178187501277)
      ·
        refine ⟨27867231634537566820312979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74312617692100178187501277 27867231634537566820312979)
        ·
          refine ⟨41800847451806350230469469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27867231634537566820312979 41800847451806350230469469)
          ·
            refine ⟨15675317794427381336426051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41800847451806350230469469 15675317794427381336426051)
            ·
              refine ⟨23512976691641072004639077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15675317794427381336426051 23512976691641072004639077)
              ·
                refine ⟨4408683129682701000869827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23512976691641072004639077 4408683129682701000869827)
                ·
                  refine ⟨6613024694524051501304741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408683129682701000869827 6613024694524051501304741)
                  ·
                    refine ⟨1239942130223259656494639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613024694524051501304741 1239942130223259656494639)
                    ·
                      rfl

theorem cell22_3622168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_3622168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622168 prefixEnd_3622168 := by exact prefixLift 3622168
  have htrace : WordTrace (prefixWord ++ tailWord_3622168) baseStart_3622168 baseEnd_3622168 := by
    simpa [prefixWord, tailWord_3622168, baseEnd_3622168] using wordTrace_append hprefix tailTrace_3622168
  have hstable : (prefixWord ++ tailWord_3622168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622168).length < 2 ^ (prefixWord ++ tailWord_3622168).sum := by decide
  have hdescent : baseEnd_3622168 < baseStart_3622168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622215 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3622215 : Nat := 118140960795 + 3622215 * 2 ^ 59
def prefixEnd_3622215 : Nat := 4983230072969 + 3 ^ 40 * 3622215 * 2
def baseEnd_3622215 : Nat := 1239958219283767200569495

theorem tailTrace_3622215 : CollatzResearch.WordTrace tailWord_3622215 prefixEnd_3622215 1239958219283767200569495 := by
  unfold tailWord_3622215
  simp only [CollatzResearch.WordTrace]
  refine ⟨132113034572341154915852099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88075356381560769943901399 132113034572341154915852099)
  ·
    refine ⟨198169551858511732373778149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132113034572341154915852099 198169551858511732373778149)
    ·
      refine ⟨37156790973470949820083403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198169551858511732373778149 37156790973470949820083403)
      ·
        refine ⟨55735186460206424730125105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37156790973470949820083403 55735186460206424730125105)
        ·
          refine ⟨41801389845154818547593829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55735186460206424730125105 41801389845154818547593829)
          ·
            refine ⟨7837760595966528477673843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41801389845154818547593829 7837760595966528477673843)
            ·
              refine ⟨11756640893949792716510765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837760595966528477673843 11756640893949792716510765)
              ·
                refine ⟨4408740335231172268691537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11756640893949792716510765 4408740335231172268691537)
                ·
                  refine ⟨3306555251423379201518653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408740335231172268691537 3306555251423379201518653)
                  ·
                    refine ⟨1239958219283767200569495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306555251423379201518653 1239958219283767200569495)
                    ·
                      rfl

theorem cell22_3622215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3622215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622215 prefixEnd_3622215 := by exact prefixLift 3622215
  have htrace : WordTrace (prefixWord ++ tailWord_3622215) baseStart_3622215 baseEnd_3622215 := by
    simpa [prefixWord, tailWord_3622215, baseEnd_3622215] using wordTrace_append hprefix tailTrace_3622215
  have hstable : (prefixWord ++ tailWord_3622215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622215).length < 2 ^ (prefixWord ++ tailWord_3622215).sum := by decide
  have hdescent : baseEnd_3622215 < baseStart_3622215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622241 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3622241 : Nat := 118140960795 + 3622241 * 2 ^ 59
def prefixEnd_3622241 : Nat := 4983230072969 + 3 ^ 40 * 3622241 * 2
def baseEnd_3622241 : Nat := 1239967119615111799419415

theorem tailTrace_3622241 : CollatzResearch.WordTrace tailWord_3622241 prefixEnd_3622241 1239967119615111799419415 := by
  unfold tailWord_3622241
  simp only [CollatzResearch.WordTrace]
  refine ⟨132113982870246961356298577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88075988580164640904199051 132113982870246961356298577)
  ·
    refine ⟨99085487152685221017223933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132113982870246961356298577 99085487152685221017223933)
    ·
      refine ⟨37157057682256957881458975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99085487152685221017223933 37157057682256957881458975)
      ·
        refine ⟨55735586523385436822188463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37157057682256957881458975 55735586523385436822188463)
        ·
          refine ⟨83603379785078155233282695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55735586523385436822188463 83603379785078155233282695)
          ·
            refine ⟨125405069677617232849924043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83603379785078155233282695 125405069677617232849924043)
            ·
              refine ⟨188107604516425849274886065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125405069677617232849924043 188107604516425849274886065)
              ·
                refine ⟨141080703387319386956164549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188107604516425849274886065 141080703387319386956164549)
                ·
                  refine ⟨26452631885122385054280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141080703387319386956164549 26452631885122385054280853)
                  ·
                    refine ⟨1239967119615111799419415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26452631885122385054280853 1239967119615111799419415)
                    ·
                      rfl

theorem cell22_3622241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3622241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622241 prefixEnd_3622241 := by exact prefixLift 3622241
  have htrace : WordTrace (prefixWord ++ tailWord_3622241) baseStart_3622241 baseEnd_3622241 := by
    simpa [prefixWord, tailWord_3622241, baseEnd_3622241] using wordTrace_append hprefix tailTrace_3622241
  have hstable : (prefixWord ++ tailWord_3622241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622241).length < 2 ^ (prefixWord ++ tailWord_3622241).sum := by decide
  have hdescent : baseEnd_3622241 < baseStart_3622241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622350 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_3622350 : Nat := 118140960795 + 3622350 * 2 ^ 59
def prefixEnd_3622350 : Nat := 4983230072969 + 3 ^ 40 * 3622350 * 2
def baseEnd_3622350 : Nat := 1240004432542671848444081

theorem tailTrace_3622350 : CollatzResearch.WordTrace tailWord_3622350 prefixEnd_3622350 1240004432542671848444081 := by
  unfold tailWord_3622350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514744803356509121502063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88078638951234715314677669 16514744803356509121502063)
  ·
    refine ⟨24772117205034763682253095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16514744803356509121502063 24772117205034763682253095)
    ·
      refine ⟨37158175807552145523379643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24772117205034763682253095 37158175807552145523379643)
      ·
        refine ⟨55737263711328218285069465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37158175807552145523379643 55737263711328218285069465)
        ·
          refine ⟨41802947783496163713802099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55737263711328218285069465 41802947783496163713802099)
          ·
            refine ⟨62704421675244245570703149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41802947783496163713802099 62704421675244245570703149)
            ·
              refine ⟨23514158128216592089013681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62704421675244245570703149 23514158128216592089013681)
              ·
                refine ⟨17635618596162444066760261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23514158128216592089013681 17635618596162444066760261)
                ·
                  refine ⟨3306678486780458262517549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17635618596162444066760261 3306678486780458262517549)
                  ·
                    refine ⟨1240004432542671848444081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306678486780458262517549 1240004432542671848444081)
                    ·
                      rfl

theorem cell22_3622350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_3622350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622350 prefixEnd_3622350 := by exact prefixLift 3622350
  have htrace : WordTrace (prefixWord ++ tailWord_3622350) baseStart_3622350 baseEnd_3622350 := by
    simpa [prefixWord, tailWord_3622350, baseEnd_3622350] using wordTrace_append hprefix tailTrace_3622350
  have hstable : (prefixWord ++ tailWord_3622350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622350).length < 2 ^ (prefixWord ++ tailWord_3622350).sum := by decide
  have hdescent : baseEnd_3622350 < baseStart_3622350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622365 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3622365 : Nat := 118140960795 + 3622365 * 2 ^ 59
def prefixEnd_3622365 : Nat := 4983230072969 + 3 ^ 40 * 3622365 * 2
def baseEnd_3622365 : Nat := 1240009567349216809319035

theorem tailTrace_3622365 : CollatzResearch.WordTrace tailWord_3622365 prefixEnd_3622365 1240009567349216809319035 := by
  unfold tailWord_3622365
  simp only [CollatzResearch.WordTrace]
  refine ⟨132118505521797730533812549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88079003681198487022541699 132118505521797730533812549)
  ·
    refine ⟨24772219785337074475089853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132118505521797730533812549 24772219785337074475089853)
    ·
      refine ⟨9289582419501402928158695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24772219785337074475089853 9289582419501402928158695)
      ·
        refine ⟨13934373629252104392238043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289582419501402928158695 13934373629252104392238043)
        ·
          refine ⟨20901560443878156588357065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934373629252104392238043 20901560443878156588357065)
          ·
            refine ⟨15676170332908617441267799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901560443878156588357065 15676170332908617441267799)
            ·
              refine ⟨23514255499362926161901699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676170332908617441267799 23514255499362926161901699)
              ·
                refine ⟨35271383249044389242852549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514255499362926161901699 35271383249044389242852549)
                ·
                  refine ⟨6613384359195822983034853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35271383249044389242852549 6613384359195822983034853)
                  ·
                    refine ⟨1240009567349216809319035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613384359195822983034853 1240009567349216809319035)
                    ·
                      rfl

theorem cell22_3622365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3622365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622365 prefixEnd_3622365 := by exact prefixLift 3622365
  have htrace : WordTrace (prefixWord ++ tailWord_3622365) baseStart_3622365 baseEnd_3622365 := by
    simpa [prefixWord, tailWord_3622365, baseEnd_3622365] using wordTrace_append hprefix tailTrace_3622365
  have hstable : (prefixWord ++ tailWord_3622365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622365).length < 2 ^ (prefixWord ++ tailWord_3622365).sum := by decide
  have hdescent : baseEnd_3622365 < baseStart_3622365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622384 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_3622384 : Nat := 118140960795 + 3622384 * 2 ^ 59
def prefixEnd_3622384 : Nat := 4983230072969 + 3 ^ 40 * 3622384 * 2
def baseEnd_3622384 : Nat := 1240016071437507093093977

theorem tailTrace_3622384 : CollatzResearch.WordTrace tailWord_3622384 prefixEnd_3622384 1240016071437507093093977 := by
  unfold tailWord_3622384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66059599254364448389377103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88079465672485931185836137 66059599254364448389377103)
  ·
    refine ⟨99089398881546672584065655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66059599254364448389377103 99089398881546672584065655)
    ·
      refine ⟨148634098322320008876098483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99089398881546672584065655 148634098322320008876098483)
      ·
        refine ⟨222951147483480013314147725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148634098322320008876098483 222951147483480013314147725)
        ·
          refine ⟨83606680306305004992805397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222951147483480013314147725 83606680306305004992805397)
          ·
            refine ⟨3919063139358047109037753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83606680306305004992805397 3919063139358047109037753)
            ·
              refine ⟨2939297354518535331778315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919063139358047109037753 2939297354518535331778315)
              ·
                refine ⟨4408946031777802997667473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939297354518535331778315 4408946031777802997667473)
                ·
                  refine ⟨3306709523833352248250605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408946031777802997667473 3306709523833352248250605)
                  ·
                    refine ⟨1240016071437507093093977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306709523833352248250605 1240016071437507093093977)
                    ·
                      rfl

theorem cell22_3622384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_3622384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622384 prefixEnd_3622384 := by exact prefixLift 3622384
  have htrace : WordTrace (prefixWord ++ tailWord_3622384) baseStart_3622384 baseEnd_3622384 := by
    simpa [prefixWord, tailWord_3622384, baseEnd_3622384] using wordTrace_append hprefix tailTrace_3622384
  have hstable : (prefixWord ++ tailWord_3622384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622384).length < 2 ^ (prefixWord ++ tailWord_3622384).sum := by decide
  have hdescent : baseEnd_3622384 < baseStart_3622384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622408 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_3622408 : Nat := 118140960795 + 3622408 * 2 ^ 59
def prefixEnd_3622408 : Nat := 4983230072969 + 3 ^ 40 * 3622408 * 2
def baseEnd_3622408 : Nat := 413341429042659676831301

theorem tailTrace_3622408 : CollatzResearch.WordTrace tailWord_3622408 prefixEnd_3622408 413341429042659676831301 := by
  unfold tailWord_3622408
  simp only [CollatzResearch.WordTrace]
  refine ⟨66060036930320974438813939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88080049240427965918418585 66060036930320974438813939)
  ·
    refine ⟨99090055395481461658220909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66060036930320974438813939 99090055395481461658220909)
    ·
      refine ⟨37158770773305548121832841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99090055395481461658220909 37158770773305548121832841)
      ·
        refine ⟨27869078079979161091374631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37158770773305548121832841 27869078079979161091374631)
        ·
          refine ⟨41803617119968741637061947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869078079979161091374631 41803617119968741637061947)
          ·
            refine ⟨62705425679953112455592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41803617119968741637061947 62705425679953112455592921)
            ·
              refine ⟨47029069259964834341694691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62705425679953112455592921 47029069259964834341694691)
              ·
                refine ⟨70543603889947251512542037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47029069259964834341694691 70543603889947251512542037)
                ·
                  refine ⟨413341429042659676831301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70543603889947251512542037 413341429042659676831301)
                  ·
                    rfl

theorem cell22_3622408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_3622408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622408 prefixEnd_3622408 := by exact prefixLift 3622408
  have htrace : WordTrace (prefixWord ++ tailWord_3622408) baseStart_3622408 baseEnd_3622408 := by
    simpa [prefixWord, tailWord_3622408, baseEnd_3622408] using wordTrace_append hprefix tailTrace_3622408
  have hstable : (prefixWord ++ tailWord_3622408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622408).length < 2 ^ (prefixWord ++ tailWord_3622408).sum := by decide
  have hdescent : baseEnd_3622408 < baseStart_3622408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622429 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_3622429 : Nat := 118140960795 + 3622429 * 2 ^ 59
def prefixEnd_3622429 : Nat := 4983230072969 + 3 ^ 40 * 3622429 * 2
def baseEnd_3622429 : Nat := 1240031475857141975718839

theorem tailTrace_3622429 : CollatzResearch.WordTrace tailWord_3622429 prefixEnd_3622429 1240031475857141975718839 := by
  unfold tailWord_3622429
  simp only [CollatzResearch.WordTrace]
  refine ⟨132120839793565869464142341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88080559862377246309428227 132120839793565869464142341)
  ·
    refine ⟨24772657461293600524526689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132120839793565869464142341 24772657461293600524526689)
    ·
      refine ⟨18579493095970200393395017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24772657461293600524526689 18579493095970200393395017)
      ·
        refine ⟨13934619821977650295046263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18579493095970200393395017 13934619821977650295046263)
        ·
          refine ⟨20901929732966475442569395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934619821977650295046263 20901929732966475442569395)
          ·
            refine ⟨31352894599449713163854093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20901929732966475442569395 31352894599449713163854093)
            ·
              refine ⟨11757335474793642436445285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31352894599449713163854093 11757335474793642436445285)
              ·
                refine ⟨2204500401523807956833491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11757335474793642436445285 2204500401523807956833491)
                ·
                  refine ⟨3306750602285711935250237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204500401523807956833491 3306750602285711935250237)
                  ·
                    refine ⟨1240031475857141975718839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306750602285711935250237 1240031475857141975718839)
                    ·
                      rfl

theorem cell22_3622429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_3622429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622429 prefixEnd_3622429 := by exact prefixLift 3622429
  have htrace : WordTrace (prefixWord ++ tailWord_3622429) baseStart_3622429 baseEnd_3622429 := by
    simpa [prefixWord, tailWord_3622429, baseEnd_3622429] using wordTrace_append hprefix tailTrace_3622429
  have hstable : (prefixWord ++ tailWord_3622429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622429).length < 2 ^ (prefixWord ++ tailWord_3622429).sum := by decide
  have hdescent : baseEnd_3622429 < baseStart_3622429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622455 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3622455 : Nat := 118140960795 + 3622455 * 2 ^ 59
def prefixEnd_3622455 : Nat := 4983230072969 + 3 ^ 40 * 3622455 * 2
def baseEnd_3622455 : Nat := 1240040376188486574568759

theorem tailTrace_3622455 : CollatzResearch.WordTrace tailWord_3622455 prefixEnd_3622455 1240040376188486574568759 := by
  unfold tailWord_3622455
  simp only [CollatzResearch.WordTrace]
  refine ⟨132121788091471675904588819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88081192060981117269725879 132121788091471675904588819)
  ·
    refine ⟨198182682137207513856883229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132121788091471675904588819 198182682137207513856883229)
    ·
      refine ⟨74318505801452817696331211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198182682137207513856883229 74318505801452817696331211)
      ·
        refine ⟨111477758702179226544496817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74318505801452817696331211 111477758702179226544496817)
        ·
          refine ⟨83608319026634419908372613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111477758702179226544496817 83608319026634419908372613)
          ·
            refine ⟨15676559817493953732819865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83608319026634419908372613 15676559817493953732819865)
            ·
              refine ⟨11757419863120465299614899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676559817493953732819865 11757419863120465299614899)
              ·
                refine ⟨17636129794680697949422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757419863120465299614899 17636129794680697949422349)
                ·
                  refine ⟨6613548673005261731033381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17636129794680697949422349 6613548673005261731033381)
                  ·
                    refine ⟨1240040376188486574568759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613548673005261731033381 1240040376188486574568759)
                    ·
                      rfl

theorem cell22_3622455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3622455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622455 prefixEnd_3622455 := by exact prefixLift 3622455
  have htrace : WordTrace (prefixWord ++ tailWord_3622455) baseStart_3622455 baseEnd_3622455 := by
    simpa [prefixWord, tailWord_3622455, baseEnd_3622455] using wordTrace_append hprefix tailTrace_3622455
  have hstable : (prefixWord ++ tailWord_3622455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622455).length < 2 ^ (prefixWord ++ tailWord_3622455).sum := by decide
  have hdescent : baseEnd_3622455 < baseStart_3622455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622483 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_3622483 : Nat := 118140960795 + 3622483 * 2 ^ 59
def prefixEnd_3622483 : Nat := 4983230072969 + 3 ^ 40 * 3622483 * 2
def baseEnd_3622483 : Nat := 1240049961160703834868673

theorem tailTrace_3622483 : CollatzResearch.WordTrace tailWord_3622483 prefixEnd_3622483 1240049961160703834868673 := by
  unfold tailWord_3622483
  simp only [CollatzResearch.WordTrace]
  refine ⟨132122809335370236686608103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88081872890246824457738735 132122809335370236686608103)
  ·
    refine ⟨198184214003055355029912155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132122809335370236686608103 198184214003055355029912155)
    ·
      refine ⟨297276321004583032544868233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198184214003055355029912155 297276321004583032544868233)
      ·
        refine ⟨222957240753437274408651175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297276321004583032544868233 222957240753437274408651175)
        ·
          refine ⟨334435861130155911612976763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222957240753437274408651175 334435861130155911612976763)
          ·
            refine ⟨501653791695233867419465145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334435861130155911612976763 501653791695233867419465145)
            ·
              refine ⟨376240343771425400564598859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501653791695233867419465145 376240343771425400564598859)
              ·
                refine ⟨564360515657138100846898289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376240343771425400564598859 564360515657138100846898289)
                ·
                  refine ⟨423270386742853575635173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564360515657138100846898289 423270386742853575635173717)
                  ·
                    refine ⟨1240049961160703834868673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 423270386742853575635173717 1240049961160703834868673)
                    ·
                      rfl

theorem cell22_3622483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_3622483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622483 prefixEnd_3622483 := by exact prefixLift 3622483
  have htrace : WordTrace (prefixWord ++ tailWord_3622483) baseStart_3622483 baseEnd_3622483 := by
    simpa [prefixWord, tailWord_3622483, baseEnd_3622483] using wordTrace_append hprefix tailTrace_3622483
  have hstable : (prefixWord ++ tailWord_3622483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622483).length < 2 ^ (prefixWord ++ tailWord_3622483).sum := by decide
  have hdescent : baseEnd_3622483 < baseStart_3622483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622487 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 4]
def baseStart_3622487 : Nat := 118140960795 + 3622487 * 2 ^ 59
def prefixEnd_3622487 : Nat := 4983230072969 + 3 ^ 40 * 3622487 * 2
def baseEnd_3622487 : Nat := 413350443480816385922887

theorem tailTrace_3622487 : CollatzResearch.WordTrace tailWord_3622487 prefixEnd_3622487 413350443480816385922887 := by
  unfold tailWord_3622487
  simp only [CollatzResearch.WordTrace]
  refine ⟨132122955227355745369753715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88081970151570496913169143 132122955227355745369753715)
  ·
    refine ⟨198184432841033618054630573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132122955227355745369753715 198184432841033618054630573)
    ·
      refine ⟨74319162315387606770486465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198184432841033618054630573 74319162315387606770486465)
      ·
        refine ⟨55739371736540705077864849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74319162315387606770486465 55739371736540705077864849)
        ·
          refine ⟨41804528802405528808398637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55739371736540705077864849 41804528802405528808398637)
          ·
            refine ⟨15676698300902073303149489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41804528802405528808398637 15676698300902073303149489)
            ·
              refine ⟨11757523725676554977362117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676698300902073303149489 11757523725676554977362117)
              ·
                refine ⟨2204535698564354058255397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11757523725676554977362117 2204535698564354058255397)
                ·
                  refine ⟨413350443480816385922887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204535698564354058255397 413350443480816385922887)
                  ·
                    rfl

theorem cell22_3622487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 4].length) (baseStart_3622487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622487 prefixEnd_3622487 := by exact prefixLift 3622487
  have htrace : WordTrace (prefixWord ++ tailWord_3622487) baseStart_3622487 baseEnd_3622487 := by
    simpa [prefixWord, tailWord_3622487, baseEnd_3622487] using wordTrace_append hprefix tailTrace_3622487
  have hstable : (prefixWord ++ tailWord_3622487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622487).length < 2 ^ (prefixWord ++ tailWord_3622487).sum := by decide
  have hdescent : baseEnd_3622487 < baseStart_3622487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622500 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3622500 : Nat := 118140960795 + 3622500 * 2 ^ 59
def prefixEnd_3622500 : Nat := 4983230072969 + 3 ^ 40 * 3622500 * 2
def baseEnd_3622500 : Nat := 1240055780608121457193621

theorem tailTrace_3622500 : CollatzResearch.WordTrace tailWord_3622500 prefixEnd_3622500 1240055780608121457193621 := by
  unfold tailWord_3622500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061714688154324294988477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88082286250872432393317969 66061714688154324294988477)
  ·
    refine ⟨24773143008057871610620679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66061714688154324294988477 24773143008057871610620679)
    ·
      refine ⟨37159714512086807415931019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773143008057871610620679 37159714512086807415931019)
      ·
        refine ⟨55739571768130211123896529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159714512086807415931019 55739571768130211123896529)
        ·
          refine ⟨41804678826097658342922397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55739571768130211123896529 41804678826097658342922397)
          ·
            refine ⟨15676754559786621878595899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41804678826097658342922397 15676754559786621878595899)
            ·
              refine ⟨23515131839679932817893849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676754559786621878595899 23515131839679932817893849)
              ·
                refine ⟨17636348879759949613420387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23515131839679932817893849 17636348879759949613420387)
                ·
                  refine ⟨26454523319639924420130581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17636348879759949613420387 26454523319639924420130581)
                  ·
                    refine ⟨1240055780608121457193621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26454523319639924420130581 1240055780608121457193621)
                    ·
                      rfl

theorem cell22_3622500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3622500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622500 prefixEnd_3622500 := by exact prefixLift 3622500
  have htrace : WordTrace (prefixWord ++ tailWord_3622500) baseStart_3622500 baseEnd_3622500 := by
    simpa [prefixWord, tailWord_3622500, baseEnd_3622500] using wordTrace_append hprefix tailTrace_3622500
  have hstable : (prefixWord ++ tailWord_3622500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622500).length < 2 ^ (prefixWord ++ tailWord_3622500).sum := by decide
  have hdescent : baseEnd_3622500 < baseStart_3622500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622517 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3622517 : Nat := 118140960795 + 3622517 * 2 ^ 59
def prefixEnd_3622517 : Nat := 4983230072969 + 3 ^ 40 * 3622517 * 2
def baseEnd_3622517 : Nat := 1240061600055539079518569

theorem tailTrace_3622517 : CollatzResearch.WordTrace tailWord_3622517 prefixEnd_3622517 1240061600055539079518569 := by
  unfold tailWord_3622517
  simp only [CollatzResearch.WordTrace]
  refine ⟨132124049417247060493345805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88082699611498040328897203 132124049417247060493345805)
  ·
    refine ⟨49546518531467647685004677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132124049417247060493345805 49546518531467647685004677)
    ·
      refine ⟨9289972224650183940938377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49546518531467647685004677 9289972224650183940938377)
      ·
        refine ⟨6967479168487637955703783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9289972224650183940938377 6967479168487637955703783)
        ·
          refine ⟨10451218752731456933555675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967479168487637955703783 10451218752731456933555675)
          ·
            refine ⟨15676828129097185400333513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451218752731456933555675 15676828129097185400333513)
            ·
              refine ⟨11757621096822889050250135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676828129097185400333513 11757621096822889050250135)
              ·
                refine ⟨17636431645234333575375203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757621096822889050250135 17636431645234333575375203)
                ·
                  refine ⟨26454647467851500363062805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17636431645234333575375203 26454647467851500363062805)
                  ·
                    refine ⟨1240061600055539079518569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26454647467851500363062805 1240061600055539079518569)
                    ·
                      rfl

theorem cell22_3622517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3622517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622517 prefixEnd_3622517 := by exact prefixLift 3622517
  have htrace : WordTrace (prefixWord ++ tailWord_3622517) baseStart_3622517 baseEnd_3622517 := by
    simpa [prefixWord, tailWord_3622517, baseEnd_3622517] using wordTrace_append hprefix tailTrace_3622517
  have hstable : (prefixWord ++ tailWord_3622517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622517).length < 2 ^ (prefixWord ++ tailWord_3622517).sum := by decide
  have hdescent : baseEnd_3622517 < baseStart_3622517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622532 : List Nat := [2, 3, 2, 1, 4, 2, 8]
def baseStart_3622532 : Nat := 118140960795 + 3622532 * 2 ^ 59
def prefixEnd_3622532 : Nat := 4983230072969 + 3 ^ 40 * 3622532 * 2
def baseEnd_3622532 : Nat := 45928397587484594088649

theorem tailTrace_3622532 : CollatzResearch.WordTrace tailWord_3622532 prefixEnd_3622532 45928397587484594088649 := by
  unfold tailWord_3622532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66062298256096359027570925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88083064341461812036761233 66062298256096359027570925)
  ·
    refine ⟨24773361846036134635339097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66062298256096359027570925 24773361846036134635339097)
    ·
      refine ⟨18580021384527100976504323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24773361846036134635339097 18580021384527100976504323)
      ·
        refine ⟨27870032076790651464756485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18580021384527100976504323 27870032076790651464756485)
        ·
          refine ⟨5225631014398247149641841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27870032076790651464756485 5225631014398247149641841)
          ·
            refine ⟨3919223260798685362231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225631014398247149641841 3919223260798685362231381)
            ·
              refine ⟨45928397587484594088649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3919223260798685362231381 45928397587484594088649)
              ·
                rfl

theorem cell22_3622532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 8].length) (baseStart_3622532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622532 prefixEnd_3622532 := by exact prefixLift 3622532
  have htrace : WordTrace (prefixWord ++ tailWord_3622532) baseStart_3622532 baseEnd_3622532 := by
    simpa [prefixWord, tailWord_3622532, baseEnd_3622532] using wordTrace_append hprefix tailTrace_3622532
  have hstable : (prefixWord ++ tailWord_3622532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622532).length < 2 ^ (prefixWord ++ tailWord_3622532).sum := by decide
  have hdescent : baseEnd_3622532 < baseStart_3622532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622568 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3622568 : Nat := 118140960795 + 3622568 * 2 ^ 59
def prefixEnd_3622568 : Nat := 4983230072969 + 3 ^ 40 * 3622568 * 2
def baseEnd_3622568 : Nat := 1240079058397791946493413

theorem tailTrace_3622568 : CollatzResearch.WordTrace tailWord_3622568 prefixEnd_3622568 1240079058397791946493413 := by
  unfold tailWord_3622568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66062954770031148101726179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88083939693374864135634905 66062954770031148101726179)
  ·
    refine ⟨99094432155046722152589269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66062954770031148101726179 99094432155046722152589269)
    ·
      refine ⟨2322525753633907550451311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 99094432155046722152589269 2322525753633907550451311)
      ·
        refine ⟨3483788630450861325676967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322525753633907550451311 3483788630450861325676967)
        ·
          refine ⟨5225682945676291988515451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483788630450861325676967 5225682945676291988515451)
          ·
            refine ⟨7838524418514437982773177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225682945676291988515451 7838524418514437982773177)
            ·
              refine ⟨5878893313885828487079883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7838524418514437982773177 5878893313885828487079883)
              ·
                refine ⟨8818339970828742730619825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878893313885828487079883 8818339970828742730619825)
                ·
                  refine ⟨6613754978121557047964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8818339970828742730619825 6613754978121557047964869)
                  ·
                    refine ⟨1240079058397791946493413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613754978121557047964869 1240079058397791946493413)
                    ·
                      rfl

theorem cell22_3622568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3622568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622568 prefixEnd_3622568 := by exact prefixLift 3622568
  have htrace : WordTrace (prefixWord ++ tailWord_3622568) baseStart_3622568 baseEnd_3622568 := by
    simpa [prefixWord, tailWord_3622568, baseEnd_3622568] using wordTrace_append hprefix tailTrace_3622568
  have hstable : (prefixWord ++ tailWord_3622568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622568).length < 2 ^ (prefixWord ++ tailWord_3622568).sum := by decide
  have hdescent : baseEnd_3622568 < baseStart_3622568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622639 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 4]
def baseStart_3622639 : Nat := 118140960795 + 3622639 * 2 ^ 59
def prefixEnd_3622639 : Nat := 4983230072969 + 3 ^ 40 * 3622639 * 2
def baseEnd_3622639 : Nat := 413367787716257142656065

theorem tailTrace_3622639 : CollatzResearch.WordTrace tailWord_3622639 prefixEnd_3622639 413367787716257142656065 := by
  unfold tailWord_3622639
  simp only [CollatzResearch.WordTrace]
  refine ⟨132128499122805075329286971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88085666081870050219524647 132128499122805075329286971)
  ·
    refine ⟨198192748684207612993930457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132128499122805075329286971 198192748684207612993930457)
    ·
      refine ⟨148644561513155709745447843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198192748684207612993930457 148644561513155709745447843)
      ·
        refine ⟨222966842269733564618171765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148644561513155709745447843 222966842269733564618171765)
        ·
          refine ⟨20903141462787521682953603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222966842269733564618171765 20903141462787521682953603)
          ·
            refine ⟨31354712194181282524430405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20903141462787521682953603 31354712194181282524430405)
            ·
              refine ⟨5879008536408990473330701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31354712194181282524430405 5879008536408990473330701)
              ·
                refine ⟨2204628201153371427499013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5879008536408990473330701 2204628201153371427499013)
                ·
                  refine ⟨413367787716257142656065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204628201153371427499013 413367787716257142656065)
                  ·
                    rfl

theorem cell22_3622639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 4].length) (baseStart_3622639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622639 prefixEnd_3622639 := by exact prefixLift 3622639
  have htrace : WordTrace (prefixWord ++ tailWord_3622639) baseStart_3622639 baseEnd_3622639 := by
    simpa [prefixWord, tailWord_3622639, baseEnd_3622639] using wordTrace_append hprefix tailTrace_3622639
  have hstable : (prefixWord ++ tailWord_3622639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622639).length < 2 ^ (prefixWord ++ tailWord_3622639).sum := by decide
  have hdescent : baseEnd_3622639 < baseStart_3622639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622641 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3622641 : Nat := 118140960795 + 3622641 * 2 ^ 59
def prefixEnd_3622641 : Nat := 4983230072969 + 3 ^ 40 * 3622641 * 2
def baseEnd_3622641 : Nat := 1240104047789644089418189

theorem tailTrace_3622641 : CollatzResearch.WordTrace tailWord_3622641 prefixEnd_3622641 1240104047789644089418189 := by
  unfold tailWord_3622641
  simp only [CollatzResearch.WordTrace]
  refine ⟨132128572068797829670859777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88085714712531886447239851 132128572068797829670859777)
  ·
    refine ⟨99096429051598372253144833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132128572068797829670859777 99096429051598372253144833)
    ·
      refine ⟨74322321788698779189858625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99096429051598372253144833 74322321788698779189858625)
      ·
        refine ⟨55741741341524084392393969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74322321788698779189858625 55741741341524084392393969)
        ·
          refine ⟨41806306006143063294295477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55741741341524084392393969 41806306006143063294295477)
          ·
            refine ⟨3919341188075912183840201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41806306006143063294295477 3919341188075912183840201)
            ·
              refine ⟨2939505891056934137880151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919341188075912183840201 2939505891056934137880151)
              ·
                refine ⟨4409258836585401206820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939505891056934137880151 4409258836585401206820227)
                ·
                  refine ⟨6613888254878101810230341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409258836585401206820227 6613888254878101810230341)
                  ·
                    refine ⟨1240104047789644089418189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613888254878101810230341 1240104047789644089418189)
                    ·
                      rfl

theorem cell22_3622641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3622641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622641 prefixEnd_3622641 := by exact prefixLift 3622641
  have htrace : WordTrace (prefixWord ++ tailWord_3622641) baseStart_3622641 baseEnd_3622641 := by
    simpa [prefixWord, tailWord_3622641, baseEnd_3622641] using wordTrace_append hprefix tailTrace_3622641
  have hstable : (prefixWord ++ tailWord_3622641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622641).length < 2 ^ (prefixWord ++ tailWord_3622641).sum := by decide
  have hdescent : baseEnd_3622641 < baseStart_3622641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622652 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3622652 : Nat := 118140960795 + 3622652 * 2 ^ 59
def prefixEnd_3622652 : Nat := 4983230072969 + 3 ^ 40 * 3622652 * 2
def baseEnd_3622652 : Nat := 1240107813314443727393155

theorem tailTrace_3622652 : CollatzResearch.WordTrace tailWord_3622652 prefixEnd_3622652 1240107813314443727393155 := by
  unfold tailWord_3622652
  simp only [CollatzResearch.WordTrace]
  refine ⟨66064486635878989274755105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88085982181171985699673473 66064486635878989274755105)
  ·
    refine ⟨49548364976909241956066329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66064486635878989274755105 49548364976909241956066329)
    ·
      refine ⟨37161273732681931467049747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49548364976909241956066329 37161273732681931467049747)
      ·
        refine ⟨55741910599022897200574621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37161273732681931467049747 55741910599022897200574621)
        ·
          refine ⟨20903216474633586450215483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55741910599022897200574621 20903216474633586450215483)
          ·
            refine ⟨31354824711950379675323225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20903216474633586450215483 31354824711950379675323225)
            ·
              refine ⟨23516118533962784756492419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31354824711950379675323225 23516118533962784756492419)
              ·
                refine ⟨35274177800944177134738629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23516118533962784756492419 35274177800944177134738629)
                ·
                  refine ⟨6613908337677033212763493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35274177800944177134738629 6613908337677033212763493)
                  ·
                    refine ⟨1240107813314443727393155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613908337677033212763493 1240107813314443727393155)
                    ·
                      rfl

theorem cell22_3622652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3622652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622652 prefixEnd_3622652 := by exact prefixLift 3622652
  have htrace : WordTrace (prefixWord ++ tailWord_3622652) baseStart_3622652 baseEnd_3622652 := by
    simpa [prefixWord, tailWord_3622652, baseEnd_3622652] using wordTrace_append hprefix tailTrace_3622652
  have hstable : (prefixWord ++ tailWord_3622652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622652).length < 2 ^ (prefixWord ++ tailWord_3622652).sum := by decide
  have hdescent : baseEnd_3622652 < baseStart_3622652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622712 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_3622712 : Nat := 118140960795 + 3622712 * 2 ^ 59
def prefixEnd_3622712 : Nat := 4983230072969 + 3 ^ 40 * 3622712 * 2
def baseEnd_3622712 : Nat := 413376117513541190297657

theorem tailTrace_3622712 : CollatzResearch.WordTrace tailWord_3622712 prefixEnd_3622712 413376117513541190297657 := by
  unfold tailWord_3622712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66065580825770304398347195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88087441101027072531129593 66065580825770304398347195)
  ·
    refine ⟨99098371238655456597520793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66065580825770304398347195 99098371238655456597520793)
    ·
      refine ⟨74323778428991592448140595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99098371238655456597520793 74323778428991592448140595)
      ·
        refine ⟨111485667643487388672210893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74323778428991592448140595 111485667643487388672210893)
        ·
          refine ⟨41807125366307770752079085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111485667643487388672210893 41807125366307770752079085)
          ·
            refine ⟨15677672012365414032029657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41807125366307770752079085 15677672012365414032029657)
            ·
              refine ⟨11758254009274060524022243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15677672012365414032029657 11758254009274060524022243)
              ·
                refine ⟨17637381013911090786033365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11758254009274060524022243 17637381013911090786033365)
                ·
                  refine ⟨413376117513541190297657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17637381013911090786033365 413376117513541190297657)
                  ·
                    rfl

theorem cell22_3622712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_3622712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622712 prefixEnd_3622712 := by exact prefixLift 3622712
  have htrace : WordTrace (prefixWord ++ tailWord_3622712) baseStart_3622712 baseEnd_3622712 := by
    simpa [prefixWord, tailWord_3622712, baseEnd_3622712] using wordTrace_append hprefix tailTrace_3622712
  have hstable : (prefixWord ++ tailWord_3622712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622712).length < 2 ^ (prefixWord ++ tailWord_3622712).sum := by decide
  have hdescent : baseEnd_3622712 < baseStart_3622712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622716 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_3622716 : Nat := 118140960795 + 3622716 * 2 ^ 59
def prefixEnd_3622716 : Nat := 4983230072969 + 3 ^ 40 * 3622716 * 2
def baseEnd_3622716 : Nat := 1240129721822368893792959

theorem tailTrace_3622716 : CollatzResearch.WordTrace tailWord_3622716 prefixEnd_3622716 1240129721822368893792959 := by
  unfold tailWord_3622716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66065653771763058739920001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88087538362350744986560001 66065653771763058739920001)
  ·
    refine ⟨49549240328822294054940001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66065653771763058739920001 49549240328822294054940001)
    ·
      refine ⟨37161930246616720541205001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49549240328822294054940001 37161930246616720541205001)
      ·
        refine ⟨27871447684962540405903751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37161930246616720541205001 27871447684962540405903751)
        ·
          refine ⟨41807171527443810608855627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27871447684962540405903751 41807171527443810608855627)
          ·
            refine ⟨62710757291165715913283441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41807171527443810608855627 62710757291165715913283441)
            ·
              refine ⟨47033067968374286934962581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62710757291165715913283441 47033067968374286934962581)
              ·
                refine ⟨2204675061017544700076371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47033067968374286934962581 2204675061017544700076371)
                ·
                  refine ⟨3307012591526317050114557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204675061017544700076371 3307012591526317050114557)
                  ·
                    refine ⟨1240129721822368893792959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307012591526317050114557 1240129721822368893792959)
                    ·
                      rfl

theorem cell22_3622716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_3622716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622716 prefixEnd_3622716 := by exact prefixLift 3622716
  have htrace : WordTrace (prefixWord ++ tailWord_3622716) baseStart_3622716 baseEnd_3622716 := by
    simpa [prefixWord, tailWord_3622716, baseEnd_3622716] using wordTrace_append hprefix tailTrace_3622716
  have hstable : (prefixWord ++ tailWord_3622716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622716).length < 2 ^ (prefixWord ++ tailWord_3622716).sum := by decide
  have hdescent : baseEnd_3622716 < baseStart_3622716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622727 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3622727 : Nat := 118140960795 + 3622727 * 2 ^ 59
def prefixEnd_3622727 : Nat := 4983230072969 + 3 ^ 40 * 3622727 * 2
def baseEnd_3622727 : Nat := 1240133487347168531767925

theorem tailTrace_3622727 : CollatzResearch.WordTrace tailWord_3622727 prefixEnd_3622727 1240133487347168531767925 := by
  unfold tailWord_3622727
  simp only [CollatzResearch.WordTrace]
  refine ⟨132131708746486266358490435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88087805830990844238993623 132131708746486266358490435)
  ·
    refine ⟨198197563119729399537735653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132131708746486266358490435 198197563119729399537735653)
    ·
      refine ⟨37162043084949262413325435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198197563119729399537735653 37162043084949262413325435)
      ·
        refine ⟨55743064627423893619988153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37162043084949262413325435 55743064627423893619988153)
        ·
          refine ⟨41807298470567920214991115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55743064627423893619988153 41807298470567920214991115)
          ·
            refine ⟨62710947705851880322486673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41807298470567920214991115 62710947705851880322486673)
            ·
              refine ⟨47033210779388910241865005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62710947705851880322486673 47033210779388910241865005)
              ·
                refine ⟨17637454042270841340699377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47033210779388910241865005 17637454042270841340699377)
                ·
                  refine ⟨13228090531703131005524533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17637454042270841340699377 13228090531703131005524533)
                  ·
                    refine ⟨1240133487347168531767925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13228090531703131005524533 1240133487347168531767925)
                    ·
                      rfl

theorem cell22_3622727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3622727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622727 prefixEnd_3622727 := by exact prefixLift 3622727
  have htrace : WordTrace (prefixWord ++ tailWord_3622727) baseStart_3622727 baseEnd_3622727 := by
    simpa [prefixWord, tailWord_3622727, baseEnd_3622727] using wordTrace_append hprefix tailTrace_3622727
  have hstable : (prefixWord ++ tailWord_3622727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622727).length < 2 ^ (prefixWord ++ tailWord_3622727).sum := by decide
  have hdescent : baseEnd_3622727 < baseStart_3622727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622789 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3622789 : Nat := 118140960795 + 3622789 * 2 ^ 59
def prefixEnd_3622789 : Nat := 4983230072969 + 3 ^ 40 * 3622789 * 2
def baseEnd_3622789 : Nat := 1240154711214221036717735

theorem tailTrace_3622789 : CollatzResearch.WordTrace tailWord_3622789 prefixEnd_3622789 1240154711214221036717735 := by
  unfold tailWord_3622789
  simp only [CollatzResearch.WordTrace]
  refine ⟨132133970072261650947247421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88089313381507767298164947 132133970072261650947247421)
  ·
    refine ⟨49550238777098119105217783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132133970072261650947247421 49550238777098119105217783)
    ·
      refine ⟨74325358165647178657826675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49550238777098119105217783 74325358165647178657826675)
      ·
        refine ⟨111488037248470767986740013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74325358165647178657826675 111488037248470767986740013)
        ·
          refine ⟨41808013968176537995027505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111488037248470767986740013 41808013968176537995027505)
          ·
            refine ⟨31356010476132403496270629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41808013968176537995027505 31356010476132403496270629)
            ·
              refine ⟨5879251964274825655550743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31356010476132403496270629 5879251964274825655550743)
              ·
                refine ⟨8818877946412238483326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879251964274825655550743 8818877946412238483326115)
                ·
                  refine ⟨13228316919618357724989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818877946412238483326115 13228316919618357724989173)
                  ·
                    refine ⟨1240154711214221036717735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13228316919618357724989173 1240154711214221036717735)
                    ·
                      rfl

theorem cell22_3622789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3622789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622789 prefixEnd_3622789 := by exact prefixLift 3622789
  have htrace : WordTrace (prefixWord ++ tailWord_3622789) baseStart_3622789 baseEnd_3622789 := by
    simpa [prefixWord, tailWord_3622789, baseEnd_3622789] using wordTrace_append hprefix tailTrace_3622789
  have hstable : (prefixWord ++ tailWord_3622789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622789).length < 2 ^ (prefixWord ++ tailWord_3622789).sum := by decide
  have hdescent : baseEnd_3622789 < baseStart_3622789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622823 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3622823 : Nat := 118140960795 + 3622823 * 2 ^ 59
def prefixEnd_3622823 : Nat := 4983230072969 + 3 ^ 40 * 3622823 * 2
def baseEnd_3622823 : Nat := 1240166350109056281367631

theorem tailTrace_3622823 : CollatzResearch.WordTrace tailWord_3622823 prefixEnd_3622823 1240166350109056281367631 := by
  unfold tailWord_3622823
  simp only [CollatzResearch.WordTrace]
  refine ⟨132135210154138474753985123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88090140102758983169323415 132135210154138474753985123)
  ·
    refine ⟨198202815231207712130977685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132135210154138474753985123 198202815231207712130977685)
    ·
      refine ⟨9290756963962861506139579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198202815231207712130977685 9290756963962861506139579)
      ·
        refine ⟨13936135445944292259209369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9290756963962861506139579 13936135445944292259209369)
        ·
          refine ⟨10452101584458219194407027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13936135445944292259209369 10452101584458219194407027)
          ·
            refine ⟨15678152376687328791610541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452101584458219194407027 15678152376687328791610541)
            ·
              refine ⟨5879307141257748296853953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15678152376687328791610541 5879307141257748296853953)
              ·
                refine ⟨4409480355943311222640465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5879307141257748296853953 4409480355943311222640465)
                ·
                  refine ⟨3307110266957483416980349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4409480355943311222640465 3307110266957483416980349)
                  ·
                    refine ⟨1240166350109056281367631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307110266957483416980349 1240166350109056281367631)
                    ·
                      rfl

theorem cell22_3622823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3622823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622823 prefixEnd_3622823 := by exact prefixLift 3622823
  have htrace : WordTrace (prefixWord ++ tailWord_3622823) baseStart_3622823 baseEnd_3622823 := by
    simpa [prefixWord, tailWord_3622823, baseEnd_3622823] using wordTrace_append hprefix tailTrace_3622823
  have hstable : (prefixWord ++ tailWord_3622823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622823).length < 2 ^ (prefixWord ++ tailWord_3622823).sum := by decide
  have hdescent : baseEnd_3622823 < baseStart_3622823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622909 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3622909 : Nat := 118140960795 + 3622909 * 2 ^ 59
def prefixEnd_3622909 : Nat := 4983230072969 + 3 ^ 40 * 3622909 * 2
def baseEnd_3622909 : Nat := 413398596555526907905789

theorem tailTrace_3622909 : CollatzResearch.WordTrace tailWord_3622909 prefixEnd_3622909 413398596555526907905789 := by
  unfold tailWord_3622909
  simp only [CollatzResearch.WordTrace]
  refine ⟨132138346831826911441615781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88092231221217940961077187 132138346831826911441615781)
  ·
    refine ⟨24775940030967545895302959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132138346831826911441615781 24775940030967545895302959)
    ·
      refine ⟨37163910046451318842954439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24775940030967545895302959 37163910046451318842954439)
      ·
        refine ⟨55745865069676978264431659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37163910046451318842954439 55745865069676978264431659)
        ·
          refine ⟨83618797604515467396647489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55745865069676978264431659 83618797604515467396647489)
          ·
            refine ⟨62714098203386600547485617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83618797604515467396647489 62714098203386600547485617)
            ·
              refine ⟨47035573652539950410614213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62714098203386600547485617 47035573652539950410614213)
              ·
                refine ⟨8819170059851240701990165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47035573652539950410614213 8819170059851240701990165)
                ·
                  refine ⟨413398596555526907905789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8819170059851240701990165 413398596555526907905789)
                  ·
                    rfl

theorem cell22_3622909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3622909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622909 prefixEnd_3622909 := by exact prefixLift 3622909
  have htrace : WordTrace (prefixWord ++ tailWord_3622909) baseStart_3622909 baseEnd_3622909 := by
    simpa [prefixWord, tailWord_3622909, baseEnd_3622909] using wordTrace_append hprefix tailTrace_3622909
  have hstable : (prefixWord ++ tailWord_3622909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622909).length < 2 ^ (prefixWord ++ tailWord_3622909).sum := by decide
  have hdescent : baseEnd_3622909 < baseStart_3622909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_3622939 : Nat := 118140960795 + 3622939 * 2 ^ 59
def prefixEnd_3622939 : Nat := 4983230072969 + 3 ^ 40 * 3622939 * 2
def baseEnd_3622939 : Nat := 1240206059279670645467275

theorem tailTrace_3622939 : CollatzResearch.WordTrace tailWord_3622939 prefixEnd_3622939 1240206059279670645467275 := by
  unfold tailWord_3622939
  simp only [CollatzResearch.WordTrace]
  refine ⟨132139441021718226565207871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88092960681145484376805247 132139441021718226565207871)
  ·
    refine ⟨198209161532577339847811807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132139441021718226565207871 198209161532577339847811807)
    ·
      refine ⟨297313742298866009771717711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198209161532577339847811807 297313742298866009771717711)
      ·
        refine ⟨445970613448299014657576567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297313742298866009771717711 445970613448299014657576567)
        ·
          refine ⟨668955920172448521986364851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445970613448299014657576567 668955920172448521986364851)
          ·
            refine ⟨1003433880258672782979547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668955920172448521986364851 1003433880258672782979547277)
            ·
              refine ⟨376287705097002293617330229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1003433880258672782979547277 376287705097002293617330229)
              ·
                refine ⟨35276972352843965026624709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376287705097002293617330229 35276972352843965026624709)
                ·
                  refine ⟨6614432316158243442492133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35276972352843965026624709 6614432316158243442492133)
                  ·
                    refine ⟨1240206059279670645467275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6614432316158243442492133 1240206059279670645467275)
                    ·
                      rfl

theorem cell22_3622939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_3622939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622939 prefixEnd_3622939 := by exact prefixLift 3622939
  have htrace : WordTrace (prefixWord ++ tailWord_3622939) baseStart_3622939 baseEnd_3622939 := by
    simpa [prefixWord, tailWord_3622939, baseEnd_3622939] using wordTrace_append hprefix tailTrace_3622939
  have hstable : (prefixWord ++ tailWord_3622939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622939).length < 2 ^ (prefixWord ++ tailWord_3622939).sum := by decide
  have hdescent : baseEnd_3622939 < baseStart_3622939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622958 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3622958 : Nat := 118140960795 + 3622958 * 2 ^ 59
def prefixEnd_3622958 : Nat := 4983230072969 + 3 ^ 40 * 3622958 * 2
def baseEnd_3622958 : Nat := 1240212563367960929242217

theorem tailTrace_3622958 : CollatzResearch.WordTrace tailWord_3622958 prefixEnd_3622958 1240212563367960929242217 := by
  unfold tailWord_3622958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517516751081174101268691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88093422672432928540099685 16517516751081174101268691)
  ·
    refine ⟨24776275126621761151903037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16517516751081174101268691 24776275126621761151903037)
    ·
      refine ⟨9291103172483160431963639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24776275126621761151903037 9291103172483160431963639)
      ·
        refine ⟨13936654758724740647945459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9291103172483160431963639 13936654758724740647945459)
        ·
          refine ⟨20904982138087110971918189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13936654758724740647945459 20904982138087110971918189)
          ·
            refine ⟨7839368301782666614469321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20904982138087110971918189 7839368301782666614469321)
            ·
              refine ⟨5879526226336999960851991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839368301782666614469321 5879526226336999960851991)
              ·
                refine ⟨8819289339505499941277987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879526226336999960851991 8819289339505499941277987)
                ·
                  refine ⟨13228934009258249911916981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819289339505499941277987 13228934009258249911916981)
                  ·
                    refine ⟨1240212563367960929242217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13228934009258249911916981 1240212563367960929242217)
                    ·
                      rfl

theorem cell22_3622958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3622958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622958 prefixEnd_3622958 := by exact prefixLift 3622958
  have htrace : WordTrace (prefixWord ++ tailWord_3622958) baseStart_3622958 baseEnd_3622958 := by
    simpa [prefixWord, tailWord_3622958, baseEnd_3622958] using wordTrace_append hprefix tailTrace_3622958
  have hstable : (prefixWord ++ tailWord_3622958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622958).length < 2 ^ (prefixWord ++ tailWord_3622958).sum := by decide
  have hdescent : baseEnd_3622958 < baseStart_3622958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622984 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3622984 : Nat := 118140960795 + 3622984 * 2 ^ 59
def prefixEnd_3622984 : Nat := 4983230072969 + 3 ^ 40 * 3622984 * 2
def baseEnd_3622984 : Nat := 1240221463699305528092137

theorem tailTrace_3622984 : CollatzResearch.WordTrace tailWord_3622984 prefixEnd_3622984 1240221463699305528092137 := by
  unfold tailWord_3622984
  simp only [CollatzResearch.WordTrace]
  refine ⟨66070541153277599625298003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88094054871036799500397337 66070541153277599625298003)
  ·
    refine ⟨99105811729916399437947005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66070541153277599625298003 99105811729916399437947005)
    ·
      refine ⟨37164679398718649789230127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99105811729916399437947005 37164679398718649789230127)
      ·
        refine ⟨55747019098077974683845191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37164679398718649789230127 55747019098077974683845191)
        ·
          refine ⟨83620528647116962025767787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747019098077974683845191 83620528647116962025767787)
          ·
            refine ⟨125430792970675443038651681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83620528647116962025767787 125430792970675443038651681)
            ·
              refine ⟨94073094728006582278988761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125430792970675443038651681 94073094728006582278988761)
              ·
                refine ⟨70554821046004936709241571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94073094728006582278988761 70554821046004936709241571)
                ·
                  refine ⟨105832231569007405063862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70554821046004936709241571 105832231569007405063862357)
                  ·
                    refine ⟨1240221463699305528092137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105832231569007405063862357 1240221463699305528092137)
                    ·
                      rfl

theorem cell22_3622984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3622984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622984 prefixEnd_3622984 := by exact prefixLift 3622984
  have htrace : WordTrace (prefixWord ++ tailWord_3622984) baseStart_3622984 baseEnd_3622984 := by
    simpa [prefixWord, tailWord_3622984, baseEnd_3622984] using wordTrace_append hprefix tailTrace_3622984
  have hstable : (prefixWord ++ tailWord_3622984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622984).length < 2 ^ (prefixWord ++ tailWord_3622984).sum := by decide
  have hdescent : baseEnd_3622984 < baseStart_3622984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622986 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3622986 : Nat := 118140960795 + 3622986 * 2 ^ 59
def prefixEnd_3622986 : Nat := 4983230072969 + 3 ^ 40 * 3622986 * 2
def baseEnd_3622986 : Nat := 1240222148340178189542131

theorem tailTrace_3622986 : CollatzResearch.WordTrace tailWord_3622986 prefixEnd_3622986 1240222148340178189542131 := by
  unfold tailWord_3622986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035288813136988398042203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88094103501698635728112541 33035288813136988398042203)
  ·
    refine ⟨49552933219705482597063305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33035288813136988398042203 49552933219705482597063305)
    ·
      refine ⟨37164699914779111947797479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49552933219705482597063305 37164699914779111947797479)
      ·
        refine ⟨55747049872168667921696219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37164699914779111947797479 55747049872168667921696219)
        ·
          refine ⟨83620574808253001882544329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747049872168667921696219 83620574808253001882544329)
          ·
            refine ⟨62715431106189751411908247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83620574808253001882544329 62715431106189751411908247)
            ·
              refine ⟨94073146659284627117862371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62715431106189751411908247 94073146659284627117862371)
              ·
                refine ⟨141109719988926940676793557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94073146659284627117862371 141109719988926940676793557)
                ·
                  refine ⟨3307259062240475172112349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141109719988926940676793557 3307259062240475172112349)
                  ·
                    refine ⟨1240222148340178189542131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307259062240475172112349 1240222148340178189542131)
                    ·
                      rfl

theorem cell22_3622986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3622986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3622986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3622986 prefixEnd_3622986 := by exact prefixLift 3622986
  have htrace : WordTrace (prefixWord ++ tailWord_3622986) baseStart_3622986 baseEnd_3622986 := by
    simpa [prefixWord, tailWord_3622986, baseEnd_3622986] using wordTrace_append hprefix tailTrace_3622986
  have hstable : (prefixWord ++ tailWord_3622986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622986).length < 2 ^ (prefixWord ++ tailWord_3622986).sum := by decide
  have hdescent : baseEnd_3622986 < baseStart_3622986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623037 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3623037 : Nat := 118140960795 + 3623037 * 2 ^ 59
def prefixEnd_3623037 : Nat := 4983230072969 + 3 ^ 40 * 3623037 * 2
def baseEnd_3623037 : Nat := 1240239606682431056516975

theorem tailTrace_3623037 : CollatzResearch.WordTrace tailWord_3623037 prefixEnd_3623037 1240239606682431056516975 := by
  unfold tailWord_3623037
  simp only [CollatzResearch.WordTrace]
  refine ⟨132143015375363189302275365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88095343583575459534850243 132143015375363189302275365)
  ·
    refine ⟨24776815382880597994176631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132143015375363189302275365 24776815382880597994176631)
    ·
      refine ⟨37165223074320896991264947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24776815382880597994176631 37165223074320896991264947)
      ·
        refine ⟨55747834611481345486897421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37165223074320896991264947 55747834611481345486897421)
        ·
          refine ⟨20905437979305504557586533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55747834611481345486897421 20905437979305504557586533)
          ·
            refine ⟨3919769621119782104547475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20905437979305504557586533 3919769621119782104547475)
            ·
              refine ⟨5879654431679673156821213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919769621119782104547475 5879654431679673156821213)
              ·
                refine ⟨2204870411879877433807955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5879654431679673156821213 2204870411879877433807955)
                ·
                  refine ⟨3307305617819816150711933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204870411879877433807955 3307305617819816150711933)
                  ·
                    refine ⟨1240239606682431056516975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307305617819816150711933 1240239606682431056516975)
                    ·
                      rfl

theorem cell22_3623037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3623037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623037 prefixEnd_3623037 := by exact prefixLift 3623037
  have htrace : WordTrace (prefixWord ++ tailWord_3623037) baseStart_3623037 baseEnd_3623037 := by
    simpa [prefixWord, tailWord_3623037, baseEnd_3623037] using wordTrace_append hprefix tailTrace_3623037
  have hstable : (prefixWord ++ tailWord_3623037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623037).length < 2 ^ (prefixWord ++ tailWord_3623037).sum := by decide
  have hdescent : baseEnd_3623037 < baseStart_3623037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623054 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3623054 : Nat := 118140960795 + 3623054 * 2 ^ 59
def prefixEnd_3623054 : Nat := 4983230072969 + 3 ^ 40 * 3623054 * 2
def baseEnd_3623054 : Nat := 1240245426129848678841923

theorem tailTrace_3623054 : CollatzResearch.WordTrace tailWord_3623054 prefixEnd_3623054 1240245426129848678841923 := by
  unfold tailWord_3623054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517954427037700150705527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88095756944201067470429477 16517954427037700150705527)
  ·
    refine ⟨24776931640556550226058291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16517954427037700150705527 24776931640556550226058291)
    ·
      refine ⟨37165397460834825339087437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24776931640556550226058291 37165397460834825339087437)
      ·
        refine ⟨13937024047813059502157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37165397460834825339087437 13937024047813059502157789)
        ·
          refine ⟨5226384017929897313309171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13937024047813059502157789 5226384017929897313309171)
          ·
            refine ⟨7839576026894845969963757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226384017929897313309171 7839576026894845969963757)
            ·
              refine ⟨2939841010085567238736409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7839576026894845969963757 2939841010085567238736409)
              ·
                refine ⟨2204880757564175429052307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939841010085567238736409 2204880757564175429052307)
                ·
                  refine ⟨3307321136346263143578461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204880757564175429052307 3307321136346263143578461)
                  ·
                    refine ⟨1240245426129848678841923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307321136346263143578461 1240245426129848678841923)
                    ·
                      rfl

theorem cell22_3623054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3623054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623054 prefixEnd_3623054 := by exact prefixLift 3623054
  have htrace : WordTrace (prefixWord ++ tailWord_3623054) baseStart_3623054 baseEnd_3623054 := by
    simpa [prefixWord, tailWord_3623054, baseEnd_3623054] using wordTrace_append hprefix tailTrace_3623054
  have hstable : (prefixWord ++ tailWord_3623054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623054).length < 2 ^ (prefixWord ++ tailWord_3623054).sum := by decide
  have hdescent : baseEnd_3623054 < baseStart_3623054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623136 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_3623136 : Nat := 118140960795 + 3623136 * 2 ^ 59
def prefixEnd_3623136 : Nat := 4983230072969 + 3 ^ 40 * 3623136 * 2
def baseEnd_3623136 : Nat := 1240273496405627798291671

theorem tailTrace_3623136 : CollatzResearch.WordTrace tailWord_3623136 prefixEnd_3623136 1240273496405627798291671 := by
  unfold tailWord_3623136
  simp only [CollatzResearch.WordTrace]
  refine ⟨66073313101002264605064631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88097750801336352806752841 66073313101002264605064631)
  ·
    refine ⟨99109969651503396907596947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66073313101002264605064631 99109969651503396907596947)
    ·
      refine ⟨148664954477255095361395421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99109969651503396907596947 148664954477255095361395421)
      ·
        refine ⟨55749357928970660760523283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148664954477255095361395421 55749357928970660760523283)
        ·
          refine ⟨83624036893455991140784925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55749357928970660760523283 83624036893455991140784925)
          ·
            refine ⟨31359013835045996677794347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83624036893455991140784925 31359013835045996677794347)
            ·
              refine ⟨47038520752568995016691521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31359013835045996677794347 47038520752568995016691521)
              ·
                refine ⟨35278890564426746262518641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47038520752568995016691521 35278890564426746262518641)
                ·
                  refine ⟨26459167923320059696888981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35278890564426746262518641 26459167923320059696888981)
                  ·
                    refine ⟨1240273496405627798291671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26459167923320059696888981 1240273496405627798291671)
                    ·
                      rfl

theorem cell22_3623136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_3623136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623136 prefixEnd_3623136 := by exact prefixLift 3623136
  have htrace : WordTrace (prefixWord ++ tailWord_3623136) baseStart_3623136 baseEnd_3623136 := by
    simpa [prefixWord, tailWord_3623136, baseEnd_3623136] using wordTrace_append hprefix tailTrace_3623136
  have hstable : (prefixWord ++ tailWord_3623136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623136).length < 2 ^ (prefixWord ++ tailWord_3623136).sum := by decide
  have hdescent : baseEnd_3623136 < baseStart_3623136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623168 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_3623168 : Nat := 118140960795 + 3623168 * 2 ^ 59
def prefixEnd_3623168 : Nat := 4983230072969 + 3 ^ 40 * 3623168 * 2
def baseEnd_3623168 : Nat := 413428150219863460497191

theorem tailTrace_3623168 : CollatzResearch.WordTrace tailWord_3623168 prefixEnd_3623168 413428150219863460497191 := by
  unfold tailWord_3623168
  simp only [CollatzResearch.WordTrace]
  refine ⟨66073896668944299337647079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88098528891925732450196105 66073896668944299337647079)
  ·
    refine ⟨99110845003416449006470619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66073896668944299337647079 99110845003416449006470619)
    ·
      refine ⟨148666267505124673509705929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99110845003416449006470619 148666267505124673509705929)
      ·
        refine ⟨111499700628843505132279447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148666267505124673509705929 111499700628843505132279447)
        ·
          refine ⟨167249550943265257698419171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111499700628843505132279447 167249550943265257698419171)
          ·
            refine ⟨250874326414897886547628757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167249550943265257698419171 250874326414897886547628757)
            ·
              refine ⟨5879867025349169215960049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 250874326414897886547628757 5879867025349169215960049)
              ·
                refine ⟨4409900269011876911970037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5879867025349169215960049 4409900269011876911970037)
                ·
                  refine ⟨413428150219863460497191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409900269011876911970037 413428150219863460497191)
                  ·
                    rfl

theorem cell22_3623168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_3623168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623168 prefixEnd_3623168 := by exact prefixLift 3623168
  have htrace : WordTrace (prefixWord ++ tailWord_3623168) baseStart_3623168 baseEnd_3623168 := by
    simpa [prefixWord, tailWord_3623168, baseEnd_3623168] using wordTrace_append hprefix tailTrace_3623168
  have hstable : (prefixWord ++ tailWord_3623168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623168).length < 2 ^ (prefixWord ++ tailWord_3623168).sum := by decide
  have hdescent : baseEnd_3623168 < baseStart_3623168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623172 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3623172 : Nat := 118140960795 + 3623172 * 2 ^ 59
def prefixEnd_3623172 : Nat := 4983230072969 + 3 ^ 40 * 3623172 * 2
def baseEnd_3623172 : Nat := 1240285819941335704391561

theorem tailTrace_3623172 : CollatzResearch.WordTrace tailWord_3623172 prefixEnd_3623172 1240285819941335704391561 := by
  unfold tailWord_3623172
  simp only [CollatzResearch.WordTrace]
  refine ⟨66073969614937053679219885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88098626153249404905626513 66073969614937053679219885)
  ·
    refine ⟨24777738605601395129707457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66073969614937053679219885 24777738605601395129707457)
    ·
      refine ⟨18583303954201046347280593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24777738605601395129707457 18583303954201046347280593)
      ·
        refine ⟨13937477965650784760460445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18583303954201046347280593 13937477965650784760460445)
        ·
          refine ⟨5226554237119044285172667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13937477965650784760460445 5226554237119044285172667)
          ·
            refine ⟨7839831355678566427759001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226554237119044285172667 7839831355678566427759001)
            ·
              refine ⟨5879873516758924820819251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839831355678566427759001 5879873516758924820819251)
              ·
                refine ⟨8819810275138387231228877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879873516758924820819251 8819810275138387231228877)
                ·
                  refine ⟨3307428853176895211710829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8819810275138387231228877 3307428853176895211710829)
                  ·
                    refine ⟨1240285819941335704391561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307428853176895211710829 1240285819941335704391561)
                    ·
                      rfl

theorem cell22_3623172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3623172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623172 prefixEnd_3623172 := by exact prefixLift 3623172
  have htrace : WordTrace (prefixWord ++ tailWord_3623172) baseStart_3623172 baseEnd_3623172 := by
    simpa [prefixWord, tailWord_3623172, baseEnd_3623172] using wordTrace_append hprefix tailTrace_3623172
  have hstable : (prefixWord ++ tailWord_3623172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623172).length < 2 ^ (prefixWord ++ tailWord_3623172).sum := by decide
  have hdescent : baseEnd_3623172 < baseStart_3623172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623185 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 5]
def baseStart_3623185 : Nat := 118140960795 + 3623185 * 2 ^ 59
def prefixEnd_3623185 : Nat := 4983230072969 + 3 ^ 40 * 3623185 * 2
def baseEnd_3623185 : Nat := 413430090035669334605507

theorem tailTrace_3623185 : CollatzResearch.WordTrace tailWord_3623185 prefixEnd_3623185 413430090035669334605507 := by
  unfold tailWord_3623185
  simp only [CollatzResearch.WordTrace]
  refine ⟨132148413378827010578663009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88098942252551340385775339 132148413378827010578663009)
  ·
    refine ⟨99111310034120257933997257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132148413378827010578663009 99111310034120257933997257)
    ·
      refine ⟨74333482525590193450497943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99111310034120257933997257 74333482525590193450497943)
      ·
        refine ⟨111500223788385290175746915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74333482525590193450497943 111500223788385290175746915)
        ·
          refine ⟨167250335682577935263620373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111500223788385290175746915 167250335682577935263620373)
          ·
            refine ⟨7839859485120840715482205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167250335682577935263620373 7839859485120840715482205)
            ·
              refine ⟨2939947306920315268305827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7839859485120840715482205 2939947306920315268305827)
              ·
                refine ⟨4409920960380472902458741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939947306920315268305827 4409920960380472902458741)
                ·
                  refine ⟨413430090035669334605507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409920960380472902458741 413430090035669334605507)
                  ·
                    rfl

theorem cell22_3623185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_3623185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623185 prefixEnd_3623185 := by exact prefixLift 3623185
  have htrace : WordTrace (prefixWord ++ tailWord_3623185) baseStart_3623185 baseEnd_3623185 := by
    simpa [prefixWord, tailWord_3623185, baseEnd_3623185] using wordTrace_append hprefix tailTrace_3623185
  have hstable : (prefixWord ++ tailWord_3623185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623185).length < 2 ^ (prefixWord ++ tailWord_3623185).sum := by decide
  have hdescent : baseEnd_3623185 < baseStart_3623185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623230 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3623230 : Nat := 118140960795 + 3623230 * 2 ^ 59
def prefixEnd_3623230 : Nat := 4983230072969 + 3 ^ 40 * 3623230 * 2
def baseEnd_3623230 : Nat := 413435224842214295480461

theorem tailTrace_3623230 : CollatzResearch.WordTrace tailWord_3623230 prefixEnd_3623230 413435224842214295480461 := by
  unfold tailWord_3623230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16518756832957997908006393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88100036442442655509367429 16518756832957997908006393)
  ·
    refine ⟨12389067624718498431004795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16518756832957997908006393 12389067624718498431004795)
    ·
      refine ⟨18583601437077747646507193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389067624718498431004795 18583601437077747646507193)
      ·
        refine ⟨13937701077808310734880395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18583601437077747646507193 13937701077808310734880395)
        ·
          refine ⟨20906551616712466102320593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13937701077808310734880395 20906551616712466102320593)
          ·
            refine ⟨15679913712534349576740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20906551616712466102320593 15679913712534349576740445)
            ·
              refine ⟨5879967642200381091277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15679913712534349576740445 5879967642200381091277667)
              ·
                refine ⟨8819951463300571636916501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879967642200381091277667 8819951463300571636916501)
                ·
                  refine ⟨413435224842214295480461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8819951463300571636916501 413435224842214295480461)
                  ·
                    rfl

theorem cell22_3623230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3623230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623230 prefixEnd_3623230 := by exact prefixLift 3623230
  have htrace : WordTrace (prefixWord ++ tailWord_3623230) baseStart_3623230 baseEnd_3623230 := by
    simpa [prefixWord, tailWord_3623230, baseEnd_3623230] using wordTrace_append hprefix tailTrace_3623230
  have hstable : (prefixWord ++ tailWord_3623230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623230).length < 2 ^ (prefixWord ++ tailWord_3623230).sum := by decide
  have hdescent : baseEnd_3623230 < baseStart_3623230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623236 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3623236 : Nat := 118140960795 + 3623236 * 2 ^ 59
def prefixEnd_3623236 : Nat := 4983230072969 + 3 ^ 40 * 3623236 * 2
def baseEnd_3623236 : Nat := 413435909483086956930455

theorem tailTrace_3623236 : CollatzResearch.WordTrace tailWord_3623236 prefixEnd_3623236 413435909483086956930455 := by
  unfold tailWord_3623236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66075136750821123144384781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88100182334428164192513041 66075136750821123144384781)
  ·
    refine ⟨24778176281557921179144293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66075136750821123144384781 24778176281557921179144293)
    ·
      refine ⟨4645908052792110221089555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24778176281557921179144293 4645908052792110221089555)
      ·
        refine ⟨6968862079188165331634333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645908052792110221089555 6968862079188165331634333)
        ·
          refine ⟨2613323279695561999362875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6968862079188165331634333 2613323279695561999362875)
          ·
            refine ⟨3919984919543342999044313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613323279695561999362875 3919984919543342999044313)
            ·
              refine ⟨2939988689657507249283235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919984919543342999044313 2939988689657507249283235)
              ·
                refine ⟨4409983034486260873924853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939988689657507249283235 4409983034486260873924853)
                ·
                  refine ⟨413435909483086956930455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409983034486260873924853 413435909483086956930455)
                  ·
                    rfl

theorem cell22_3623236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3623236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623236 prefixEnd_3623236 := by exact prefixLift 3623236
  have htrace : WordTrace (prefixWord ++ tailWord_3623236) baseStart_3623236 baseEnd_3623236 := by
    simpa [prefixWord, tailWord_3623236, baseEnd_3623236] using wordTrace_append hprefix tailTrace_3623236
  have hstable : (prefixWord ++ tailWord_3623236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623236).length < 2 ^ (prefixWord ++ tailWord_3623236).sum := by decide
  have hdescent : baseEnd_3623236 < baseStart_3623236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623335 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3623335 : Nat := 118140960795 + 3623335 * 2 ^ 59
def prefixEnd_3623335 : Nat := 4983230072969 + 3 ^ 40 * 3623335 * 2
def baseEnd_3623335 : Nat := 1240341618172457612566061

theorem tailTrace_3623335 : CollatzResearch.WordTrace tailWord_3623335 prefixEnd_3623335 1240341618172457612566061 := by
  unfold tailWord_3623335
  simp only [CollatzResearch.WordTrace]
  refine ⟨132153884328283586196623459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88102589552189057464415639 132153884328283586196623459)
  ·
    refine ⟨198230826492425379294935189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132153884328283586196623459 198230826492425379294935189)
    ·
      refine ⟨9292069991832439654450087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198230826492425379294935189 9292069991832439654450087)
      ·
        refine ⟨13938104987748659481675131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292069991832439654450087 13938104987748659481675131)
        ·
          refine ⟨20907157481622989222512697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13938104987748659481675131 20907157481622989222512697)
          ·
            refine ⟨15680368111217241916884523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20907157481622989222512697 15680368111217241916884523)
            ·
              refine ⟨23520552166825862875326785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680368111217241916884523 23520552166825862875326785)
              ·
                refine ⟨17640414125119397156495089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23520552166825862875326785 17640414125119397156495089)
                ·
                  refine ⟨13230310593839547867371317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17640414125119397156495089 13230310593839547867371317)
                  ·
                    refine ⟨1240341618172457612566061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13230310593839547867371317 1240341618172457612566061)
                    ·
                      rfl

theorem cell22_3623335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3623335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623335 prefixEnd_3623335 := by exact prefixLift 3623335
  have htrace : WordTrace (prefixWord ++ tailWord_3623335) baseStart_3623335 baseEnd_3623335 := by
    simpa [prefixWord, tailWord_3623335, baseEnd_3623335] using wordTrace_append hprefix tailTrace_3623335
  have hstable : (prefixWord ++ tailWord_3623335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623335).length < 2 ^ (prefixWord ++ tailWord_3623335).sum := by decide
  have hdescent : baseEnd_3623335 < baseStart_3623335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623367 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3623367 : Nat := 118140960795 + 3623367 * 2 ^ 59
def prefixEnd_3623367 : Nat := 4983230072969 + 3 ^ 40 * 3623367 * 2
def baseEnd_3623367 : Nat := 1240352572426420195765963

theorem tailTrace_3623367 : CollatzResearch.WordTrace tailWord_3623367 prefixEnd_3623367 1240352572426420195765963 := by
  unfold tailWord_3623367
  simp only [CollatzResearch.WordTrace]
  refine ⟨132155051464167655661788355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88103367642778437107858903 132155051464167655661788355)
  ·
    refine ⟨198232577196251483492682533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132155051464167655661788355 198232577196251483492682533)
    ·
      refine ⟨37168608224297153154877975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198232577196251483492682533 37168608224297153154877975)
      ·
        refine ⟨55752912336445729732316963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37168608224297153154877975 55752912336445729732316963)
        ·
          refine ⟨83629368504668594598475445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55752912336445729732316963 83629368504668594598475445)
          ·
            refine ⟨7840253297312680743607073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83629368504668594598475445 7840253297312680743607073)
            ·
              refine ⟨5880189972984510557705305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840253297312680743607073 5880189972984510557705305)
              ·
                refine ⟨4410142479738382918278979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880189972984510557705305 4410142479738382918278979)
                ·
                  refine ⟨6615213719607574377418469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410142479738382918278979 6615213719607574377418469)
                  ·
                    refine ⟨1240352572426420195765963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615213719607574377418469 1240352572426420195765963)
                    ·
                      rfl

theorem cell22_3623367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3623367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623367 prefixEnd_3623367 := by exact prefixLift 3623367
  have htrace : WordTrace (prefixWord ++ tailWord_3623367) baseStart_3623367 baseEnd_3623367 := by
    simpa [prefixWord, tailWord_3623367, baseEnd_3623367] using wordTrace_append hprefix tailTrace_3623367
  have hstable : (prefixWord ++ tailWord_3623367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623367).length < 2 ^ (prefixWord ++ tailWord_3623367).sum := by decide
  have hdescent : baseEnd_3623367 < baseStart_3623367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623399 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 4]
def baseStart_3623399 : Nat := 118140960795 + 3623399 * 2 ^ 59
def prefixEnd_3623399 : Nat := 4983230072969 + 3 ^ 40 * 3623399 * 2
def baseEnd_3623399 : Nat := 413454508893460926321955

theorem tailTrace_3623399 : CollatzResearch.WordTrace tailWord_3623399 prefixEnd_3623399 413454508893460926321955 := by
  unfold tailWord_3623399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132156218600051725126953251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88104145733367816751302167 132156218600051725126953251)
  ·
    refine ⟨198234327900077587690429877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132156218600051725126953251 198234327900077587690429877)
    ·
      refine ⟨18584468240632273845977801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198234327900077587690429877 18584468240632273845977801)
      ·
        refine ⟨13938351180474205384483351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18584468240632273845977801 13938351180474205384483351)
        ·
          refine ⟨20907526770711308076725027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13938351180474205384483351 20907526770711308076725027)
          ·
            refine ⟨31361290156066962115087541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907526770711308076725027 31361290156066962115087541)
            ·
              refine ⟨2940120952131277698289457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31361290156066962115087541 2940120952131277698289457)
              ·
                refine ⟨2205090714098458273717093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940120952131277698289457 2205090714098458273717093)
                ·
                  refine ⟨413454508893460926321955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205090714098458273717093 413454508893460926321955)
                  ·
                    rfl

theorem cell22_3623399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 4].length) (baseStart_3623399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623399 prefixEnd_3623399 := by exact prefixLift 3623399
  have htrace : WordTrace (prefixWord ++ tailWord_3623399) baseStart_3623399 baseEnd_3623399 := by
    simpa [prefixWord, tailWord_3623399, baseEnd_3623399] using wordTrace_append hprefix tailTrace_3623399
  have hstable : (prefixWord ++ tailWord_3623399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623399).length < 2 ^ (prefixWord ++ tailWord_3623399).sum := by decide
  have hdescent : baseEnd_3623399 < baseStart_3623399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623414 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3623414 : Nat := 118140960795 + 3623414 * 2 ^ 59
def prefixEnd_3623414 : Nat := 4983230072969 + 3 ^ 40 * 3623414 * 2
def baseEnd_3623414 : Nat := 1240368661486927739840819

theorem tailTrace_3623414 : CollatzResearch.WordTrace tailWord_3623414 prefixEnd_3623414 1240368661486927739840819 := by
  unfold tailWord_3623414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259797855937336418046831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88104510463331588459166197 8259797855937336418046831)
  ·
    refine ⟨12389696783906004627070247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8259797855937336418046831 12389696783906004627070247)
    ·
      refine ⟨18584545175859006940605371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389696783906004627070247 18584545175859006940605371)
      ·
        refine ⟨27876817763788510410908057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584545175859006940605371 27876817763788510410908057)
        ·
          refine ⟨20907613322841382808181043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27876817763788510410908057 20907613322841382808181043)
          ·
            refine ⟨31361419984262074212271565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907613322841382808181043 31361419984262074212271565)
            ·
              refine ⟨11760532494098277829601837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31361419984262074212271565 11760532494098277829601837)
              ·
                refine ⟨4410199685286854186100689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11760532494098277829601837 4410199685286854186100689)
                ·
                  refine ⟨3307649763965140639575517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410199685286854186100689 3307649763965140639575517)
                  ·
                    refine ⟨1240368661486927739840819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307649763965140639575517 1240368661486927739840819)
                    ·
                      rfl

theorem cell22_3623414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3623414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623414 prefixEnd_3623414 := by exact prefixLift 3623414
  have htrace : WordTrace (prefixWord ++ tailWord_3623414) baseStart_3623414 baseEnd_3623414 := by
    simpa [prefixWord, tailWord_3623414, baseEnd_3623414] using wordTrace_append hprefix tailTrace_3623414
  have hstable : (prefixWord ++ tailWord_3623414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623414).length < 2 ^ (prefixWord ++ tailWord_3623414).sum := by decide
  have hdescent : baseEnd_3623414 < baseStart_3623414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623500 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_3623500 : Nat := 118140960795 + 3623500 * 2 ^ 59
def prefixEnd_3623500 : Nat := 4983230072969 + 3 ^ 40 * 3623500 * 2
def baseEnd_3623500 : Nat := 413466033681484060730185

theorem tailTrace_3623500 : CollatzResearch.WordTrace tailWord_3623500 prefixEnd_3623500 413466033681484060730185 := by
  unfold tailWord_3623500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66079951186342909688189977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88106601581790546250919969 66079951186342909688189977)
  ·
    refine ⟨49559963389757182266142483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66079951186342909688189977 49559963389757182266142483)
    ·
      refine ⟨74339945084635773399213725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49559963389757182266142483 74339945084635773399213725)
      ·
        refine ⟨27877479406738415024705147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74339945084635773399213725 27877479406738415024705147)
        ·
          refine ⟨41816219110107622537057721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27877479406738415024705147 41816219110107622537057721)
          ·
            refine ⟨31362164332580716902793291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41816219110107622537057721 31362164332580716902793291)
            ·
              refine ⟨47043246498871075354189937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31362164332580716902793291 47043246498871075354189937)
              ·
                refine ⟨35282434874153306515642453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47043246498871075354189937 35282434874153306515642453)
                ·
                  refine ⟨413466033681484060730185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35282434874153306515642453 413466033681484060730185)
                  ·
                    rfl

theorem cell22_3623500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_3623500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623500 prefixEnd_3623500 := by exact prefixLift 3623500
  have htrace : WordTrace (prefixWord ++ tailWord_3623500) baseStart_3623500 baseEnd_3623500 := by
    simpa [prefixWord, tailWord_3623500, baseEnd_3623500] using wordTrace_append hprefix tailTrace_3623500
  have hstable : (prefixWord ++ tailWord_3623500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623500).length < 2 ^ (prefixWord ++ tailWord_3623500).sum := by decide
  have hdescent : baseEnd_3623500 < baseStart_3623500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623532 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3623532 : Nat := 118140960795 + 3623532 * 2 ^ 59
def prefixEnd_3623532 : Nat := 4983230072969 + 3 ^ 40 * 3623532 * 2
def baseEnd_3623532 : Nat := 1240409055298414765390457

theorem tailTrace_3623532 : CollatzResearch.WordTrace tailWord_3623532 prefixEnd_3623532 1240409055298414765390457 := by
  unfold tailWord_3623532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66080534754284944420772425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88107379672379925894363233 66080534754284944420772425)
  ·
    refine ⟨49560401065713708315579319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66080534754284944420772425 49560401065713708315579319)
    ·
      refine ⟨74340601598570562473368979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49560401065713708315579319 74340601598570562473368979)
      ·
        refine ⟨111510902397855843710053469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74340601598570562473368979 111510902397855843710053469)
        ·
          refine ⟨41816588399195941391270051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111510902397855843710053469 41816588399195941391270051)
          ·
            refine ⟨62724882598793912086905077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41816588399195941391270051 62724882598793912086905077)
            ·
              refine ⟨5880457743636929258147351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62724882598793912086905077 5880457743636929258147351)
              ·
                refine ⟨8820686615455393887221027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880457743636929258147351 8820686615455393887221027)
                ·
                  refine ⟨13231029923183090830831541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8820686615455393887221027 13231029923183090830831541)
                  ·
                    refine ⟨1240409055298414765390457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13231029923183090830831541 1240409055298414765390457)
                    ·
                      rfl

theorem cell22_3623532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3623532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623532 prefixEnd_3623532 := by exact prefixLift 3623532
  have htrace : WordTrace (prefixWord ++ tailWord_3623532) baseStart_3623532 baseEnd_3623532 := by
    simpa [prefixWord, tailWord_3623532, baseEnd_3623532] using wordTrace_append hprefix tailTrace_3623532
  have hstable : (prefixWord ++ tailWord_3623532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623532).length < 2 ^ (prefixWord ++ tailWord_3623532).sum := by decide
  have hdescent : baseEnd_3623532 < baseStart_3623532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623624 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_3623624 : Nat := 118140960795 + 3623624 * 2 ^ 59
def prefixEnd_3623624 : Nat := 4983230072969 + 3 ^ 40 * 3623624 * 2
def baseEnd_3623624 : Nat := 413480182926185730696725

theorem tailTrace_3623624 : CollatzResearch.WordTrace tailWord_3623624 prefixEnd_3623624 413480182926185730696725 := by
  unfold tailWord_3623624
  simp only [CollatzResearch.WordTrace]
  refine ⟨66082212512118294276946963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88109616682824392369262617 66082212512118294276946963)
  ·
    refine ⟨99123318768177441415420445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66082212512118294276946963 99123318768177441415420445)
    ·
      refine ⟨37171244538066540530782667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99123318768177441415420445 37171244538066540530782667)
      ·
        refine ⟨55756866807099810796174001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37171244538066540530782667 55756866807099810796174001)
        ·
          refine ⟨41817650105324858097130501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55756866807099810796174001 41817650105324858097130501)
          ·
            refine ⟨7840809394748410893211969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41817650105324858097130501 7840809394748410893211969)
            ·
              refine ⟨5880607046061308169908977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840809394748410893211969 5880607046061308169908977)
              ·
                refine ⟨4410455284545981127431733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880607046061308169908977 4410455284545981127431733)
                ·
                  refine ⟨413480182926185730696725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4410455284545981127431733 413480182926185730696725)
                  ·
                    rfl

theorem cell22_3623624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_3623624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623624 prefixEnd_3623624 := by exact prefixLift 3623624
  have htrace : WordTrace (prefixWord ++ tailWord_3623624) baseStart_3623624 baseEnd_3623624 := by
    simpa [prefixWord, tailWord_3623624, baseEnd_3623624] using wordTrace_append hprefix tailTrace_3623624
  have hstable : (prefixWord ++ tailWord_3623624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623624).length < 2 ^ (prefixWord ++ tailWord_3623624).sum := by decide
  have hdescent : baseEnd_3623624 < baseStart_3623624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623628 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_3623628 : Nat := 118140960795 + 3623628 * 2 ^ 59
def prefixEnd_3623628 : Nat := 4983230072969 + 3 ^ 40 * 3623628 * 2
def baseEnd_3623628 : Nat := 1240441918060302514990163

theorem tailTrace_3623628 : CollatzResearch.WordTrace tailWord_3623628 prefixEnd_3623628 1240441918060302514990163 := by
  unfold tailWord_3623628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66082285458111048618519769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88109713944148064824693025 66082285458111048618519769)
  ·
    refine ⟨49561714093583286463889827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66082285458111048618519769 49561714093583286463889827)
    ·
      refine ⟨74342571140374929695834741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49561714093583286463889827 74342571140374929695834741)
      ·
        refine ⟨6969616044410149658984507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74342571140374929695834741 6969616044410149658984507)
        ·
          refine ⟨10454424066615224488476761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969616044410149658984507 10454424066615224488476761)
          ·
            refine ⟨7840818049961418366357571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10454424066615224488476761 7840818049961418366357571)
            ·
              refine ⟨11761227074942127549536357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840818049961418366357571 11761227074942127549536357)
              ·
                refine ⟨2205230076551648915538067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11761227074942127549536357 2205230076551648915538067)
                ·
                  refine ⟨3307845114827473373307101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205230076551648915538067 3307845114827473373307101)
                  ·
                    refine ⟨1240441918060302514990163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307845114827473373307101 1240441918060302514990163)
                    ·
                      rfl

theorem cell22_3623628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_3623628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623628 prefixEnd_3623628 := by exact prefixLift 3623628
  have htrace : WordTrace (prefixWord ++ tailWord_3623628) baseStart_3623628 baseEnd_3623628 := by
    simpa [prefixWord, tailWord_3623628, baseEnd_3623628] using wordTrace_append hprefix tailTrace_3623628
  have hstable : (prefixWord ++ tailWord_3623628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623628).length < 2 ^ (prefixWord ++ tailWord_3623628).sum := by decide
  have hdescent : baseEnd_3623628 < baseStart_3623628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623652 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3623652 : Nat := 118140960795 + 3623652 * 2 ^ 59
def prefixEnd_3623652 : Nat := 4983230072969 + 3 ^ 40 * 3623652 * 2
def baseEnd_3623652 : Nat := 413483377916924817463363

theorem tailTrace_3623652 : CollatzResearch.WordTrace tailWord_3623652 prefixEnd_3623652 413483377916924817463363 := by
  unfold tailWord_3623652
  simp only [CollatzResearch.WordTrace]
  refine ⟨66082723134067574667956605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88110297512090099557275473 66082723134067574667956605)
  ·
    refine ⟨24781021175275340500483727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66082723134067574667956605 24781021175275340500483727)
    ·
      refine ⟨37171531762913010750725591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781021175275340500483727 37171531762913010750725591)
      ·
        refine ⟨55757297644369516126088387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37171531762913010750725591 55757297644369516126088387)
        ·
          refine ⟨83635946466554274189132581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55757297644369516126088387 83635946466554274189132581)
          ·
            refine ⟨15681739962478926410462359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83635946466554274189132581 15681739962478926410462359)
            ·
              refine ⟨23522609943718389615693539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681739962478926410462359 23522609943718389615693539)
              ·
                refine ⟨35283914915577584423540309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23522609943718389615693539 35283914915577584423540309)
                ·
                  refine ⟨413483377916924817463363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35283914915577584423540309 413483377916924817463363)
                  ·
                    rfl

theorem cell22_3623652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3623652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623652 prefixEnd_3623652 := by exact prefixLift 3623652
  have htrace : WordTrace (prefixWord ++ tailWord_3623652) baseStart_3623652 baseEnd_3623652 := by
    simpa [prefixWord, tailWord_3623652, baseEnd_3623652] using wordTrace_append hprefix tailTrace_3623652
  have hstable : (prefixWord ++ tailWord_3623652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623652).length < 2 ^ (prefixWord ++ tailWord_3623652).sum := by decide
  have hdescent : baseEnd_3623652 < baseStart_3623652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623714 : List Nat := [3, 3, 1, 1, 2, 3, 1, 8]
def baseStart_3623714 : Nat := 118140960795 + 3623714 * 2 ^ 59
def prefixEnd_3623714 : Nat := 4983230072969 + 3 ^ 40 * 3623714 * 2
def baseEnd_3623714 : Nat := 137830150846425217482211

theorem tailTrace_3623714 : CollatzResearch.WordTrace tailWord_3623714 prefixEnd_3623714 137830150846425217482211 := by
  unfold tailWord_3623714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041926898477633481167549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88111805062607022616446797 33041926898477633481167549)
  ·
    refine ⟨12390722586929112555437831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33041926898477633481167549 12390722586929112555437831)
    ·
      refine ⟨18586083880393668833156747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390722586929112555437831 18586083880393668833156747)
      ·
        refine ⟨27879125820590503249735121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18586083880393668833156747 27879125820590503249735121)
        ·
          refine ⟨20909344365442877437301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27879125820590503249735121 20909344365442877437301341)
          ·
            refine ⟨7841004137041079038988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20909344365442877437301341 7841004137041079038988003)
            ·
              refine ⟨11761506205561618558482005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841004137041079038988003 11761506205561618558482005)
              ·
                refine ⟨137830150846425217482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11761506205561618558482005 137830150846425217482211)
                ·
                  rfl

theorem cell22_3623714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_3623714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623714 prefixEnd_3623714 := by exact prefixLift 3623714
  have htrace : WordTrace (prefixWord ++ tailWord_3623714) baseStart_3623714 baseEnd_3623714 := by
    simpa [prefixWord, tailWord_3623714, baseEnd_3623714] using wordTrace_append hprefix tailTrace_3623714
  have hstable : (prefixWord ++ tailWord_3623714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623714).length < 2 ^ (prefixWord ++ tailWord_3623714).sum := by decide
  have hdescent : baseEnd_3623714 < baseStart_3623714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623748 : List Nat := [2, 3, 4, 2, 1, 1, 2, 7]
def baseStart_3623748 : Nat := 118140960795 + 3623748 * 2 ^ 59
def prefixEnd_3623748 : Nat := 4983230072969 + 3 ^ 40 * 3623748 * 2
def baseEnd_3623748 : Nat := 137831444056962466887755

theorem tailTrace_3623748 : CollatzResearch.WordTrace tailWord_3623748 prefixEnd_3623748 137831444056962466887755 := by
  unfold tailWord_3623748
  simp only [CollatzResearch.WordTrace]
  refine ⟨66084473837893678865703949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88112631783858238487605265 66084473837893678865703949)
  ·
    refine ⟨24781677689210129574638981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66084473837893678865703949 24781677689210129574638981)
    ·
      refine ⟨4646564566726899295244809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24781677689210129574638981 4646564566726899295244809)
      ·
        refine ⟨3484923425045174471433607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4646564566726899295244809 3484923425045174471433607)
        ·
          refine ⟨5227385137567761707150411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484923425045174471433607 5227385137567761707150411)
          ·
            refine ⟨7841077706351642560725617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227385137567761707150411 7841077706351642560725617)
            ·
              refine ⟨5880808279763731920544213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841077706351642560725617 5880808279763731920544213)
              ·
                refine ⟨137831444056962466887755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5880808279763731920544213 137831444056962466887755)
                ·
                  rfl

theorem cell22_3623748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_3623748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623748 prefixEnd_3623748 := by exact prefixLift 3623748
  have htrace : WordTrace (prefixWord ++ tailWord_3623748) baseStart_3623748 baseEnd_3623748 := by
    simpa [prefixWord, tailWord_3623748, baseEnd_3623748] using wordTrace_append hprefix tailTrace_3623748
  have hstable : (prefixWord ++ tailWord_3623748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623748).length < 2 ^ (prefixWord ++ tailWord_3623748).sum := by decide
  have hdescent : baseEnd_3623748 < baseStart_3623748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623797 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3623797 : Nat := 118140960795 + 3623797 * 2 ^ 59
def prefixEnd_3623797 : Nat := 4983230072969 + 3 ^ 40 * 3623797 * 2
def baseEnd_3623797 : Nat := 1240499770214042407514645

theorem tailTrace_3623797 : CollatzResearch.WordTrace tailWord_3623797 prefixEnd_3623797 1240499770214042407514645 := by
  unfold tailWord_3623797
  simp only [CollatzResearch.WordTrace]
  refine ⟨132170734852609839099941645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88113823235073226066627763 132170734852609839099941645)
  ·
    refine ⟨49564025569728689662478117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132170734852609839099941645 49564025569728689662478117)
    ·
      refine ⟨9293254794324129311714647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49564025569728689662478117 9293254794324129311714647)
      ·
        refine ⟨13939882191486193967571971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293254794324129311714647 13939882191486193967571971)
        ·
          refine ⟨20909823287229290951357957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13939882191486193967571971 20909823287229290951357957)
          ·
            refine ⟨3920591866355492053379617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20909823287229290951357957 3920591866355492053379617)
            ·
              refine ⟨2940443899766619040034713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920591866355492053379617 2940443899766619040034713)
              ·
                refine ⟨2205332924824964280026035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940443899766619040034713 2205332924824964280026035)
                ·
                  refine ⟨3307999387237446420039053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205332924824964280026035 3307999387237446420039053)
                  ·
                    refine ⟨1240499770214042407514645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307999387237446420039053 1240499770214042407514645)
                    ·
                      rfl

theorem cell22_3623797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3623797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623797 prefixEnd_3623797 := by exact prefixLift 3623797
  have htrace : WordTrace (prefixWord ++ tailWord_3623797) baseStart_3623797 baseEnd_3623797 := by
    simpa [prefixWord, tailWord_3623797, baseEnd_3623797] using wordTrace_append hprefix tailTrace_3623797
  have hstable : (prefixWord ++ tailWord_3623797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623797).length < 2 ^ (prefixWord ++ tailWord_3623797).sum := by decide
  have hdescent : baseEnd_3623797 < baseStart_3623797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623819 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_3623819 : Nat := 118140960795 + 3623819 * 2 ^ 59
def prefixEnd_3623819 : Nat := 4983230072969 + 3 ^ 40 * 3623819 * 2
def baseEnd_3623819 : Nat := 1240507301263641683464577

theorem tailTrace_3623819 : CollatzResearch.WordTrace tailWord_3623819 prefixEnd_3623819 1240507301263641683464577 := by
  unfold tailWord_3623819
  simp only [CollatzResearch.WordTrace]
  refine ⟨132171537258530136857242511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88114358172353424571495007 132171537258530136857242511)
  ·
    refine ⟨198257305887795205285863767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132171537258530136857242511 198257305887795205285863767)
    ·
      refine ⟨297385958831692807928795651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198257305887795205285863767 297385958831692807928795651)
      ·
        refine ⟨446078938247539211893193477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297385958831692807928795651 446078938247539211893193477)
        ·
          refine ⟨83639800921413602229973777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446078938247539211893193477 83639800921413602229973777)
          ·
            refine ⟨62729850691060201672480333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83639800921413602229973777 62729850691060201672480333)
            ·
              refine ⟨23523694009147575627180125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62729850691060201672480333 23523694009147575627180125)
              ·
                refine ⟨8821385253430340860192547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23523694009147575627180125 8821385253430340860192547)
                ·
                  refine ⟨13232077880145511290288821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8821385253430340860192547 13232077880145511290288821)
                  ·
                    refine ⟨1240507301263641683464577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13232077880145511290288821 1240507301263641683464577)
                    ·
                      rfl

theorem cell22_3623819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_3623819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623819 prefixEnd_3623819 := by exact prefixLift 3623819
  have htrace : WordTrace (prefixWord ++ tailWord_3623819) baseStart_3623819 baseEnd_3623819 := by
    simpa [prefixWord, tailWord_3623819, baseEnd_3623819] using wordTrace_append hprefix tailTrace_3623819
  have hstable : (prefixWord ++ tailWord_3623819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623819).length < 2 ^ (prefixWord ++ tailWord_3623819).sum := by decide
  have hdescent : baseEnd_3623819 < baseStart_3623819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623870 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3623870 : Nat := 118140960795 + 3623870 * 2 ^ 59
def prefixEnd_3623870 : Nat := 4983230072969 + 3 ^ 40 * 3623870 * 2
def baseEnd_3623870 : Nat := 1240524759605894550439421

theorem tailTrace_3623870 : CollatzResearch.WordTrace tailWord_3623870 prefixEnd_3623870 1240524759605894550439421 := by
  unfold tailWord_3623870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521674672668171570918633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88115598254230248378232709 16521674672668171570918633)
  ·
    refine ⟨12391256004501128678188975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16521674672668171570918633 12391256004501128678188975)
    ·
      refine ⟨18586884006751693017283463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391256004501128678188975 18586884006751693017283463)
      ·
        refine ⟨27880326010127539525925195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18586884006751693017283463 27880326010127539525925195)
        ·
          refine ⟨41820489015191309288887793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27880326010127539525925195 41820489015191309288887793)
          ·
            refine ⟨31365366761393481966665845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41820489015191309288887793 31365366761393481966665845)
            ·
              refine ⟨2940503133880638934374923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31365366761393481966665845 2940503133880638934374923)
              ·
                refine ⟨4410754700820958401562385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940503133880638934374923 4410754700820958401562385)
                ·
                  refine ⟨3308066025615718801171789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410754700820958401562385 3308066025615718801171789)
                  ·
                    refine ⟨1240524759605894550439421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308066025615718801171789 1240524759605894550439421)
                    ·
                      rfl

theorem cell22_3623870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3623870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623870 prefixEnd_3623870 := by exact prefixLift 3623870
  have htrace : WordTrace (prefixWord ++ tailWord_3623870) baseStart_3623870 baseEnd_3623870 := by
    simpa [prefixWord, tailWord_3623870, baseEnd_3623870] using wordTrace_append hprefix tailTrace_3623870
  have hstable : (prefixWord ++ tailWord_3623870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623870).length < 2 ^ (prefixWord ++ tailWord_3623870).sum := by decide
  have hdescent : baseEnd_3623870 < baseStart_3623870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623879 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3623879 : Nat := 118140960795 + 3623879 * 2 ^ 59
def prefixEnd_3623879 : Nat := 4983230072969 + 3 ^ 40 * 3623879 * 2
def baseEnd_3623879 : Nat := 1240527840489821526964393

theorem tailTrace_3623879 : CollatzResearch.WordTrace tailWord_3623879 prefixEnd_3623879 1240527840489821526964393 := by
  unfold tailWord_3623879
  simp only [CollatzResearch.WordTrace]
  refine ⟨132173725638312767104426691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88115817092208511402951127 132173725638312767104426691)
  ·
    refine ⟨198260588457469150656640037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132173725638312767104426691 198260588457469150656640037)
    ·
      refine ⟨37173860335775465748120007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198260588457469150656640037 37173860335775465748120007)
      ·
        refine ⟨55760790503663198622180011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37173860335775465748120007 55760790503663198622180011)
        ·
          refine ⟨83641185755494797933270017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55760790503663198622180011 83641185755494797933270017)
          ·
            refine ⟨62730889316621098449952513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83641185755494797933270017 62730889316621098449952513)
            ·
              refine ⟨47048166987465823837464385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62730889316621098449952513 47048166987465823837464385)
              ·
                refine ⟨35286125240599367878098289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47048166987465823837464385 35286125240599367878098289)
                ·
                  refine ⟨26464593930449525908573717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35286125240599367878098289 26464593930449525908573717)
                  ·
                    refine ⟨1240527840489821526964393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26464593930449525908573717 1240527840489821526964393)
                    ·
                      rfl

theorem cell22_3623879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3623879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623879 prefixEnd_3623879 := by exact prefixLift 3623879
  have htrace : WordTrace (prefixWord ++ tailWord_3623879) baseStart_3623879 baseEnd_3623879 := by
    simpa [prefixWord, tailWord_3623879, baseEnd_3623879] using wordTrace_append hprefix tailTrace_3623879
  have hstable : (prefixWord ++ tailWord_3623879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623879).length < 2 ^ (prefixWord ++ tailWord_3623879).sum := by decide
  have hdescent : baseEnd_3623879 < baseStart_3623879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623911 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 7]
def baseStart_3623911 : Nat := 118140960795 + 3623911 * 2 ^ 59
def prefixEnd_3623911 : Nat := 4983230072969 + 3 ^ 40 * 3623911 * 2
def baseEnd_3623911 : Nat := 413512931581261370054765

theorem tailTrace_3623911 : CollatzResearch.WordTrace tailWord_3623911 prefixEnd_3623911 413512931581261370054765 := by
  unfold tailWord_3623911
  simp only [CollatzResearch.WordTrace]
  refine ⟨132174892774196836569591587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88116595182797891046394391 132174892774196836569591587)
  ·
    refine ⟨198262339161295254854387381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132174892774196836569591587 198262339161295254854387381)
    ·
      refine ⟨18587094296371430142598817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198262339161295254854387381 18587094296371430142598817)
      ·
        refine ⟨13940320722278572606949113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18587094296371430142598817 13940320722278572606949113)
        ·
          refine ⟨10455240541708929455211835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13940320722278572606949113 10455240541708929455211835)
          ·
            refine ⟨15682860812563394182817753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10455240541708929455211835 15682860812563394182817753)
            ·
              refine ⟨11762145609422545637113315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15682860812563394182817753 11762145609422545637113315)
              ·
                refine ⟨17643218414133818455669973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11762145609422545637113315 17643218414133818455669973)
                ·
                  refine ⟨413512931581261370054765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17643218414133818455669973 413512931581261370054765)
                  ·
                    rfl

theorem cell22_3623911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_3623911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623911 prefixEnd_3623911 := by exact prefixLift 3623911
  have htrace : WordTrace (prefixWord ++ tailWord_3623911) baseStart_3623911 baseEnd_3623911 := by
    simpa [prefixWord, tailWord_3623911, baseEnd_3623911] using wordTrace_append hprefix tailTrace_3623911
  have hstable : (prefixWord ++ tailWord_3623911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623911).length < 2 ^ (prefixWord ++ tailWord_3623911).sum := by decide
  have hdescent : baseEnd_3623911 < baseStart_3623911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623941 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3623941 : Nat := 118140960795 + 3623941 * 2 ^ 59
def prefixEnd_3623941 : Nat := 4983230072969 + 3 ^ 40 * 3623941 * 2
def baseEnd_3623941 : Nat := 1240549064356874031914203

theorem tailTrace_3623941 : CollatzResearch.WordTrace tailWord_3623941 prefixEnd_3623941 1240549064356874031914203 := by
  unfold tailWord_3623941
  simp only [CollatzResearch.WordTrace]
  refine ⟨132175986964088151693183677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88117324642725434462122451 132175986964088151693183677)
  ·
    refine ⟨49565995111533056884943879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132175986964088151693183677 49565995111533056884943879)
    ·
      refine ⟨74348992667299585327415819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49565995111533056884943879 74348992667299585327415819)
      ·
        refine ⟨111523489000949377991123729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74348992667299585327415819 111523489000949377991123729)
        ·
          refine ⟨83642616750712033493342797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111523489000949377991123729 83642616750712033493342797)
          ·
            refine ⟨31365981281517012560003549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83642616750712033493342797 31365981281517012560003549)
            ·
              refine ⟨11762242980568879710001331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31365981281517012560003549 11762242980568879710001331)
              ·
                refine ⟨17643364470853319565001997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11762242980568879710001331 17643364470853319565001997)
                ·
                  refine ⟨6616261676569994836875749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17643364470853319565001997 6616261676569994836875749)
                  ·
                    refine ⟨1240549064356874031914203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616261676569994836875749 1240549064356874031914203)
                    ·
                      rfl

theorem cell22_3623941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3623941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623941 prefixEnd_3623941 := by exact prefixLift 3623941
  have htrace : WordTrace (prefixWord ++ tailWord_3623941) baseStart_3623941 baseEnd_3623941 := by
    simpa [prefixWord, tailWord_3623941, baseEnd_3623941] using wordTrace_append hprefix tailTrace_3623941
  have hstable : (prefixWord ++ tailWord_3623941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623941).length < 2 ^ (prefixWord ++ tailWord_3623941).sum := by decide
  have hdescent : baseEnd_3623941 < baseStart_3623941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623973 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 4]
def baseStart_3623973 : Nat := 118140960795 + 3623973 * 2 ^ 59
def prefixEnd_3623973 : Nat := 4983230072969 + 3 ^ 40 * 3623973 * 2
def baseEnd_3623973 : Nat := 413520006203612205038035

theorem tailTrace_3623973 : CollatzResearch.WordTrace tailWord_3623973 prefixEnd_3623973 413520006203612205038035 := by
  unfold tailWord_3623973
  simp only [CollatzResearch.WordTrace]
  refine ⟨132177154099972221158348573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88118102733314814105565715 132177154099972221158348573)
  ·
    refine ⟨49566432787489582934380715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132177154099972221158348573 49566432787489582934380715)
    ·
      refine ⟨74349649181234374401571073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49566432787489582934380715 74349649181234374401571073)
      ·
        refine ⟨55762236885925780801178305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74349649181234374401571073 55762236885925780801178305)
        ·
          refine ⟨41821677664444335600883729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55762236885925780801178305 41821677664444335600883729)
          ·
            refine ⟨31366258248333251700662797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41821677664444335600883729 31366258248333251700662797)
            ·
              refine ⟨11762346843124969387748549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31366258248333251700662797 11762346843124969387748549)
              ·
                refine ⟨2205440033085931760202853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11762346843124969387748549 2205440033085931760202853)
                ·
                  refine ⟨413520006203612205038035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205440033085931760202853 413520006203612205038035)
                  ·
                    rfl

theorem cell22_3623973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_3623973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623973 prefixEnd_3623973 := by exact prefixLift 3623973
  have htrace : WordTrace (prefixWord ++ tailWord_3623973) baseStart_3623973 baseEnd_3623973 := by
    simpa [prefixWord, tailWord_3623973, baseEnd_3623973] using wordTrace_append hprefix tailTrace_3623973
  have hstable : (prefixWord ++ tailWord_3623973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623973).length < 2 ^ (prefixWord ++ tailWord_3623973).sum := by decide
  have hdescent : baseEnd_3623973 < baseStart_3623973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623986 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3623986 : Nat := 118140960795 + 3623986 * 2 ^ 59
def prefixEnd_3623986 : Nat := 4983230072969 + 3 ^ 40 * 3623986 * 2
def baseEnd_3623986 : Nat := 1240564468776508914539065

theorem tailTrace_3623986 : CollatzResearch.WordTrace tailWord_3623986 prefixEnd_3623986 1240564468776508914539065 := by
  unfold tailWord_3623986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33044407062231281094642953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88118418832616749585714541 33044407062231281094642953)
  ·
    refine ⟨24783305296673460820982215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33044407062231281094642953 24783305296673460820982215)
    ·
      refine ⟨37174957945010191231473323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24783305296673460820982215 37174957945010191231473323)
      ·
        refine ⟨55762436917515286847209985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37174957945010191231473323 55762436917515286847209985)
        ·
          refine ⟨41821827688136465135407489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55762436917515286847209985 41821827688136465135407489)
          ·
            refine ⟨31366370766102348851555617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41821827688136465135407489 31366370766102348851555617)
            ·
              refine ⟨23524778074576761638666713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31366370766102348851555617 23524778074576761638666713)
              ·
                refine ⟨17643583555932571229000035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23524778074576761638666713 17643583555932571229000035)
                ·
                  refine ⟨26465375333898856843500053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17643583555932571229000035 26465375333898856843500053)
                  ·
                    refine ⟨1240564468776508914539065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26465375333898856843500053 1240564468776508914539065)
                    ·
                      rfl

theorem cell22_3623986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3623986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3623986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3623986 prefixEnd_3623986 := by exact prefixLift 3623986
  have htrace : WordTrace (prefixWord ++ tailWord_3623986) baseStart_3623986 baseEnd_3623986 := by
    simpa [prefixWord, tailWord_3623986, baseEnd_3623986] using wordTrace_append hprefix tailTrace_3623986
  have hstable : (prefixWord ++ tailWord_3623986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623986).length < 2 ^ (prefixWord ++ tailWord_3623986).sum := by decide
  have hdescent : baseEnd_3623986 < baseStart_3623986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624033 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3624033 : Nat := 118140960795 + 3624033 * 2 ^ 59
def prefixEnd_3624033 : Nat := 4983230072969 + 3 ^ 40 * 3624033 * 2
def baseEnd_3624033 : Nat := 1240580557837016458613921

theorem tailTrace_3624033 : CollatzResearch.WordTrace tailWord_3624033 prefixEnd_3624033 1240580557837016458613921 := by
  unfold tailWord_3624033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132179342479754851405532753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88119561653169900937021835 132179342479754851405532753)
  ·
    refine ⟨99134506859816138554149565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132179342479754851405532753 99134506859816138554149565)
    ·
      refine ⟨37175440072431051957806087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99134506859816138554149565 37175440072431051957806087)
      ·
        refine ⟨55763160108646577936709131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37175440072431051957806087 55763160108646577936709131)
        ·
          refine ⟨83644740162969866905063697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55763160108646577936709131 83644740162969866905063697)
          ·
            refine ⟨62733555122227400178797773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83644740162969866905063697 62733555122227400178797773)
            ·
              refine ⟨23525083170835275067049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62733555122227400178797773 23525083170835275067049165)
              ·
                refine ⟨8821906189063228150143437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23525083170835275067049165 8821906189063228150143437)
                ·
                  refine ⟨3308214820898710556303789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8821906189063228150143437 3308214820898710556303789)
                  ·
                    refine ⟨1240580557837016458613921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308214820898710556303789 1240580557837016458613921)
                    ·
                      rfl

theorem cell22_3624033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3624033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624033 prefixEnd_3624033 := by exact prefixLift 3624033
  have htrace : WordTrace (prefixWord ++ tailWord_3624033) baseStart_3624033 baseEnd_3624033 := by
    simpa [prefixWord, tailWord_3624033, baseEnd_3624033] using wordTrace_append hprefix tailTrace_3624033
  have hstable : (prefixWord ++ tailWord_3624033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624033).length < 2 ^ (prefixWord ++ tailWord_3624033).sum := by decide
  have hdescent : baseEnd_3624033 < baseStart_3624033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624093 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3624093 : Nat := 118140960795 + 3624093 * 2 ^ 59
def prefixEnd_3624093 : Nat := 4983230072969 + 3 ^ 40 * 3624093 * 2
def baseEnd_3624093 : Nat := 1240601097063196302113737

theorem tailTrace_3624093 : CollatzResearch.WordTrace tailWord_3624093 prefixEnd_3624093 1240601097063196302113737 := by
  unfold tailWord_3624093
  simp only [CollatzResearch.WordTrace]
  refine ⟨132181530859537481652716933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88121020573024987768477955 132181530859537481652716933)
  ·
    refine ⟨24784037036163277809884425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132181530859537481652716933 24784037036163277809884425)
    ·
      refine ⟨18588027777122458357413319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24784037036163277809884425 18588027777122458357413319)
      ·
        refine ⟨27882041665683687536119979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588027777122458357413319 27882041665683687536119979)
        ·
          refine ⟨41823062498525531304179969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27882041665683687536119979 41823062498525531304179969)
          ·
            refine ⟨31367296873894148478134977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41823062498525531304179969 31367296873894148478134977)
            ·
              refine ⟨23525472655420611358601233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31367296873894148478134977 23525472655420611358601233)
              ·
                refine ⟨17644104491565458518950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23525472655420611358601233 17644104491565458518950925)
                ·
                  refine ⟨6616539184337046944606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17644104491565458518950925 6616539184337046944606597)
                  ·
                    refine ⟨1240601097063196302113737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616539184337046944606597 1240601097063196302113737)
                    ·
                      rfl

theorem cell22_3624093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3624093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624093 prefixEnd_3624093 := by exact prefixLift 3624093
  have htrace : WordTrace (prefixWord ++ tailWord_3624093) baseStart_3624093 baseEnd_3624093 := by
    simpa [prefixWord, tailWord_3624093, baseEnd_3624093] using wordTrace_append hprefix tailTrace_3624093
  have hstable : (prefixWord ++ tailWord_3624093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624093).length < 2 ^ (prefixWord ++ tailWord_3624093).sum := by decide
  have hdescent : baseEnd_3624093 < baseStart_3624093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624123 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 4, 3]
def baseStart_3624123 : Nat := 118140960795 + 3624123 * 2 ^ 59
def prefixEnd_3624123 : Nat := 4983230072969 + 3 ^ 40 * 3624123 * 2
def baseEnd_3624123 : Nat := 1240611366676286223863645

theorem tailTrace_3624123 : CollatzResearch.WordTrace tailWord_3624123 prefixEnd_3624123 1240611366676286223863645 := by
  unfold tailWord_3624123
  simp only [CollatzResearch.WordTrace]
  refine ⟨132182625049428796776309023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88121750032952531184206015 132182625049428796776309023)
  ·
    refine ⟨198273937574143195164463535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132182625049428796776309023 198273937574143195164463535)
    ·
      refine ⟨297410906361214792746695303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198273937574143195164463535 297410906361214792746695303)
      ·
        refine ⟨446116359541822189120042955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297410906361214792746695303 446116359541822189120042955)
        ·
          refine ⟨669174539312733283680064433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446116359541822189120042955 669174539312733283680064433)
          ·
            refine ⟨501880904484549962760048325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669174539312733283680064433 501880904484549962760048325)
            ·
              refine ⟨94102669590853118017509061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 501880904484549962760048325 94102669590853118017509061)
              ·
                refine ⟨17644250548284959628282949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94102669590853118017509061 17644250548284959628282949)
                ·
                  refine ⟨3308296977803429930303053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17644250548284959628282949 3308296977803429930303053)
                  ·
                    refine ⟨1240611366676286223863645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308296977803429930303053 1240611366676286223863645)
                    ·
                      rfl

theorem cell22_3624123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].length) (baseStart_3624123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624123 prefixEnd_3624123 := by exact prefixLift 3624123
  have htrace : WordTrace (prefixWord ++ tailWord_3624123) baseStart_3624123 baseEnd_3624123 := by
    simpa [prefixWord, tailWord_3624123, baseEnd_3624123] using wordTrace_append hprefix tailTrace_3624123
  have hstable : (prefixWord ++ tailWord_3624123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624123).length < 2 ^ (prefixWord ++ tailWord_3624123).sum := by decide
  have hdescent : baseEnd_3624123 < baseStart_3624123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624142 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3624142 : Nat := 118140960795 + 3624142 * 2 ^ 59
def prefixEnd_3624142 : Nat := 4983230072969 + 3 ^ 40 * 3624142 * 2
def baseEnd_3624142 : Nat := 413539290254858835879529

theorem tailTrace_3624142 : CollatzResearch.WordTrace tailWord_3624142 prefixEnd_3624142 413539290254858835879529 := by
  unfold tailWord_3624142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522914754544995377656335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88122212024239975347500453 16522914754544995377656335)
  ·
    refine ⟨24784372131817493066484503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16522914754544995377656335 24784372131817493066484503)
    ·
      refine ⟨37176558197726239599726755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24784372131817493066484503 37176558197726239599726755)
      ·
        refine ⟨55764837296589359399590133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37176558197726239599726755 55764837296589359399590133)
        ·
          refine ⟨5227953496555252443711575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55764837296589359399590133 5227953496555252443711575)
          ·
            refine ⟨7841930244832878665567363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227953496555252443711575 7841930244832878665567363)
            ·
              refine ⟨11762895367249317998351045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841930244832878665567363 11762895367249317998351045)
              ·
                refine ⟨2205542881359247124690821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11762895367249317998351045 2205542881359247124690821)
                ·
                  refine ⟨413539290254858835879529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205542881359247124690821 413539290254858835879529)
                  ·
                    rfl

theorem cell22_3624142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3624142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624142 prefixEnd_3624142 := by exact prefixLift 3624142
  have htrace : WordTrace (prefixWord ++ tailWord_3624142) baseStart_3624142 baseEnd_3624142 := by
    simpa [prefixWord, tailWord_3624142, baseEnd_3624142] using wordTrace_append hprefix tailTrace_3624142
  have hstable : (prefixWord ++ tailWord_3624142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624142).length < 2 ^ (prefixWord ++ tailWord_3624142).sum := by decide
  have hdescent : baseEnd_3624142 < baseStart_3624142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624157 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3624157 : Nat := 118140960795 + 3624157 * 2 ^ 59
def prefixEnd_3624157 : Nat := 4983230072969 + 3 ^ 40 * 3624157 * 2
def baseEnd_3624157 : Nat := 1240623005571121468513541

theorem tailTrace_3624157 : CollatzResearch.WordTrace tailWord_3624157 prefixEnd_3624157 1240623005571121468513541 := by
  unfold tailWord_3624157
  simp only [CollatzResearch.WordTrace]
  refine ⟨132183865131305620583046725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88122576754203747055364483 132183865131305620583046725)
  ·
    refine ⟨24784474712119803859321261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132183865131305620583046725 24784474712119803859321261)
    ·
      refine ⟨9294178017044926447245473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24784474712119803859321261 9294178017044926447245473)
      ·
        refine ⟨6970633512783694835434105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294178017044926447245473 6970633512783694835434105)
        ·
          refine ⟨5227975134587771126575579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970633512783694835434105 5227975134587771126575579)
          ·
            refine ⟨7841962701881656689863369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227975134587771126575579 7841962701881656689863369)
            ·
              refine ⟨5881472026411242517397527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841962701881656689863369 5881472026411242517397527)
              ·
                refine ⟨8822208039616863776096291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881472026411242517397527 8822208039616863776096291)
                ·
                  refine ⟨13233312059425295664144437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822208039616863776096291 13233312059425295664144437)
                  ·
                    refine ⟨1240623005571121468513541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13233312059425295664144437 1240623005571121468513541)
                    ·
                      rfl

theorem cell22_3624157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3624157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624157 prefixEnd_3624157 := by exact prefixLift 3624157
  have htrace : WordTrace (prefixWord ++ tailWord_3624157) baseStart_3624157 baseEnd_3624157 := by
    simpa [prefixWord, tailWord_3624157, baseEnd_3624157] using wordTrace_append hprefix tailTrace_3624157
  have hstable : (prefixWord ++ tailWord_3624157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624157).length < 2 ^ (prefixWord ++ tailWord_3624157).sum := by decide
  have hdescent : baseEnd_3624157 < baseStart_3624157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624170 : List Nat := [3, 1, 3, 1, 1, 4, 3, 6]
def baseStart_3624170 : Nat := 118140960795 + 3624170 * 2 ^ 59
def prefixEnd_3624170 : Nat := 4983230072969 + 3 ^ 40 * 3624170 * 2
def baseEnd_3624170 : Nat := 137847495081865974215389

theorem tailTrace_3624170 : CollatzResearch.WordTrace tailWord_3624170 prefixEnd_3624170 137847495081865974215389 := by
  unfold tailWord_3624170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33046084820064630950817491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88122892853505682535513309 33046084820064630950817491)
  ·
    refine ⟨49569127230096946426226237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33046084820064630950817491 49569127230096946426226237)
    ·
      refine ⟨18588422711286354909834839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49569127230096946426226237 18588422711286354909834839)
      ·
        refine ⟨27882634066929532364752259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588422711286354909834839 27882634066929532364752259)
        ·
          refine ⟨41823951100394298547128389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27882634066929532364752259 41823951100394298547128389)
          ·
            refine ⟨7841990831323930977586573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41823951100394298547128389 7841990831323930977586573)
            ·
              refine ⟨2940746561746474116594965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7841990831323930977586573 2940746561746474116594965)
              ·
                refine ⟨137847495081865974215389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2940746561746474116594965 137847495081865974215389)
                ·
                  rfl

theorem cell22_3624170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_3624170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624170 prefixEnd_3624170 := by exact prefixLift 3624170
  have htrace : WordTrace (prefixWord ++ tailWord_3624170) baseStart_3624170 baseEnd_3624170 := by
    simpa [prefixWord, tailWord_3624170, baseEnd_3624170] using wordTrace_append hprefix tailTrace_3624170
  have hstable : (prefixWord ++ tailWord_3624170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624170).length < 2 ^ (prefixWord ++ tailWord_3624170).sum := by decide
  have hdescent : baseEnd_3624170 < baseStart_3624170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624253 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_3624253 : Nat := 118140960795 + 3624253 * 2 ^ 59
def prefixEnd_3624253 : Nat := 4983230072969 + 3 ^ 40 * 3624253 * 2
def baseEnd_3624253 : Nat := 1240655868333009218113247

theorem tailTrace_3624253 : CollatzResearch.WordTrace tailWord_3624253 prefixEnd_3624253 1240655868333009218113247 := by
  unfold tailWord_3624253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132187366538957828978541413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88124911025971885985694275 132187366538957828978541413)
  ·
    refine ⟨24785131226054592933476515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132187366538957828978541413 24785131226054592933476515)
    ·
      refine ⟨37177696839081889400214773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24785131226054592933476515 37177696839081889400214773)
      ·
        refine ⟨3485409078663927131270135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37177696839081889400214773 3485409078663927131270135)
        ·
          refine ⟨5228113617995890696905203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485409078663927131270135 5228113617995890696905203)
          ·
            refine ⟨7842170426993836045357805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228113617995890696905203 7842170426993836045357805)
            ·
              refine ⟨2940813910122688517009177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7842170426993836045357805 2940813910122688517009177)
              ·
                refine ⟨2205610432592016387756883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940813910122688517009177 2205610432592016387756883)
                ·
                  refine ⟨3308415648888024581635325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205610432592016387756883 3308415648888024581635325)
                  ·
                    refine ⟨1240655868333009218113247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308415648888024581635325 1240655868333009218113247)
                    ·
                      rfl

theorem cell22_3624253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_3624253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624253 prefixEnd_3624253 := by exact prefixLift 3624253
  have htrace : WordTrace (prefixWord ++ tailWord_3624253) baseStart_3624253 baseEnd_3624253 := by
    simpa [prefixWord, tailWord_3624253, baseEnd_3624253] using wordTrace_append hprefix tailTrace_3624253
  have hstable : (prefixWord ++ tailWord_3624253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624253).length < 2 ^ (prefixWord ++ tailWord_3624253).sum := by decide
  have hdescent : baseEnd_3624253 < baseStart_3624253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624320 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_3624320 : Nat := 118140960795 + 3624320 * 2 ^ 59
def prefixEnd_3624320 : Nat := 4983230072969 + 3 ^ 40 * 3624320 * 2
def baseEnd_3624320 : Nat := 1240678803802243376688041

theorem tailTrace_3624320 : CollatzResearch.WordTrace tailWord_3624320 prefixEnd_3624320 1240678803802243376688041 := by
  unfold tailWord_3624320
  simp only [CollatzResearch.WordTrace]
  refine ⟨66094905114857549710615207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88126540153143399614153609 66094905114857549710615207)
  ·
    refine ⟨99142357672286324565922811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66094905114857549710615207 99142357672286324565922811)
    ·
      refine ⟨148713536508429486848884217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99142357672286324565922811 148713536508429486848884217)
      ·
        refine ⟨111535152381322115136663163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148713536508429486848884217 111535152381322115136663163)
        ·
          refine ⟨167302728571983172704994745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111535152381322115136663163 167302728571983172704994745)
          ·
            refine ⟨125477046428987379528746059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167302728571983172704994745 125477046428987379528746059)
            ·
              refine ⟨188215569643481069293119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125477046428987379528746059 188215569643481069293119089)
              ·
                refine ⟨141161677232610801969839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188215569643481069293119089 141161677232610801969839317)
                ·
                  refine ⟨3308476810139315671168109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141161677232610801969839317 3308476810139315671168109)
                  ·
                    refine ⟨1240678803802243376688041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308476810139315671168109 1240678803802243376688041)
                    ·
                      rfl

theorem cell22_3624320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_3624320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624320 prefixEnd_3624320 := by exact prefixLift 3624320
  have htrace : WordTrace (prefixWord ++ tailWord_3624320) baseStart_3624320 baseEnd_3624320 := by
    simpa [prefixWord, tailWord_3624320, baseEnd_3624320] using wordTrace_append hprefix tailTrace_3624320
  have hstable : (prefixWord ++ tailWord_3624320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624320).length < 2 ^ (prefixWord ++ tailWord_3624320).sum := by decide
  have hdescent : baseEnd_3624320 < baseStart_3624320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624395 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 6]
def baseStart_3624395 : Nat := 118140960795 + 3624395 * 2 ^ 59
def prefixEnd_3624395 : Nat := 4983230072969 + 3 ^ 40 * 3624395 * 2
def baseEnd_3624395 : Nat := 413568159278322727020937

theorem tailTrace_3624395 : CollatzResearch.WordTrace tailWord_3624395 prefixEnd_3624395 413568159278322727020937 := by
  unfold tailWord_3624395
  simp only [CollatzResearch.WordTrace]
  refine ⟨132192545704443387230210639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88128363802962258153473759 132192545704443387230210639)
  ·
    refine ⟨198288818556665080845315959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132192545704443387230210639 198288818556665080845315959)
    ·
      refine ⟨297433227834997621267973939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198288818556665080845315959 297433227834997621267973939)
      ·
        refine ⟨446149841752496431901960909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297433227834997621267973939 446149841752496431901960909)
        ·
          refine ⟨167306190657186161963235341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446149841752496431901960909 167306190657186161963235341)
          ·
            refine ⟨62739821496444810736213253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167306190657186161963235341 62739821496444810736213253)
            ·
              refine ⟨11763716530583402013039985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62739821496444810736213253 11763716530583402013039985)
              ·
                refine ⟨8822787397937551509779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763716530583402013039985 8822787397937551509779989)
                ·
                  refine ⟨413568159278322727020937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8822787397937551509779989 413568159278322727020937)
                  ·
                    rfl

theorem cell22_3624395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_3624395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624395 prefixEnd_3624395 := by exact prefixLift 3624395
  have htrace : WordTrace (prefixWord ++ tailWord_3624395) baseStart_3624395 baseEnd_3624395 := by
    simpa [prefixWord, tailWord_3624395, baseEnd_3624395] using wordTrace_append hprefix tailTrace_3624395
  have hstable : (prefixWord ++ tailWord_3624395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624395).length < 2 ^ (prefixWord ++ tailWord_3624395).sum := by decide
  have hdescent : baseEnd_3624395 < baseStart_3624395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624440 : List Nat := [2, 1, 2, 1, 1, 5, 1, 9]
def baseStart_3624440 : Nat := 118140960795 + 3624440 * 2 ^ 59
def prefixEnd_3624440 : Nat := 4983230072969 + 3 ^ 40 * 3624440 * 2
def baseEnd_3624440 : Nat := 137857764694955895965297

theorem tailTrace_3624440 : CollatzResearch.WordTrace tailWord_3624440 prefixEnd_3624440 137857764694955895965297 := by
  unfold tailWord_3624440
  simp only [CollatzResearch.WordTrace]
  refine ⟨66097093494640179957799387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88129457992853573277065849 66097093494640179957799387)
  ·
    refine ⟨99145640241960269936699081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66097093494640179957799387 99145640241960269936699081)
    ·
      refine ⟨74359230181470202452524311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99145640241960269936699081 74359230181470202452524311)
      ·
        refine ⟨111538845272205303678786467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74359230181470202452524311 111538845272205303678786467)
        ·
          refine ⟨167308267908307955518179701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111538845272205303678786467 167308267908307955518179701)
          ·
            refine ⟨15685150116403870829829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167308267908307955518179701 15685150116403870829829347)
            ·
              refine ⟨23527725174605806244744021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685150116403870829829347 23527725174605806244744021)
              ·
                refine ⟨137857764694955895965297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23527725174605806244744021 137857764694955895965297)
                ·
                  rfl

theorem cell22_3624440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_3624440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624440 prefixEnd_3624440 := by exact prefixLift 3624440
  have htrace : WordTrace (prefixWord ++ tailWord_3624440) baseStart_3624440 baseEnd_3624440 := by
    simpa [prefixWord, tailWord_3624440, baseEnd_3624440] using wordTrace_append hprefix tailTrace_3624440
  have hstable : (prefixWord ++ tailWord_3624440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624440).length < 2 ^ (prefixWord ++ tailWord_3624440).sum := by decide
  have hdescent : baseEnd_3624440 < baseStart_3624440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624459 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_3624459 : Nat := 118140960795 + 3624459 * 2 ^ 59
def prefixEnd_3624459 : Nat := 4983230072969 + 3 ^ 40 * 3624459 * 2
def baseEnd_3624459 : Nat := 1240726386342893347462615

theorem tailTrace_3624459 : CollatzResearch.WordTrace tailWord_3624459 prefixEnd_3624459 1240726386342893347462615 := by
  unfold tailWord_3624459
  simp only [CollatzResearch.WordTrace]
  refine ⟨132194879976211526160540431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88129919984141017440360287 132194879976211526160540431)
  ·
    refine ⟨198292319964317289240810647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132194879976211526160540431 198292319964317289240810647)
    ·
      refine ⟨297438479946475933861215971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198292319964317289240810647 297438479946475933861215971)
      ·
        refine ⟨446157719919713900791823957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297438479946475933861215971 446157719919713900791823957)
        ·
          refine ⟨5228410780309147274904187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 446157719919713900791823957 5228410780309147274904187)
          ·
            refine ⟨7842616170463720912356281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228410780309147274904187 7842616170463720912356281)
            ·
              refine ⟨5881962127847790684267211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7842616170463720912356281 5881962127847790684267211)
              ·
                refine ⟨8822943191771686026400817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881962127847790684267211 8822943191771686026400817)
                ·
                  refine ⟨6617207393828764519800613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822943191771686026400817 6617207393828764519800613)
                  ·
                    refine ⟨1240726386342893347462615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617207393828764519800613 1240726386342893347462615)
                    ·
                      rfl

theorem cell22_3624459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_3624459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624459 prefixEnd_3624459 := by exact prefixLift 3624459
  have htrace : WordTrace (prefixWord ++ tailWord_3624459) baseStart_3624459 baseEnd_3624459 := by
    simpa [prefixWord, tailWord_3624459, baseEnd_3624459] using wordTrace_append hprefix tailTrace_3624459
  have hstable : (prefixWord ++ tailWord_3624459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624459).length < 2 ^ (prefixWord ++ tailWord_3624459).sum := by decide
  have hdescent : baseEnd_3624459 < baseStart_3624459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624547 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 6]
def baseStart_3624547 : Nat := 118140960795 + 3624547 * 2 ^ 59
def prefixEnd_3624547 : Nat := 4983230072969 + 3 ^ 40 * 3624547 * 2
def baseEnd_3624547 : Nat := 413585503513763483754115

theorem tailTrace_3624547 : CollatzResearch.WordTrace tailWord_3624547 prefixEnd_3624547 413585503513763483754115 := by
  unfold tailWord_3624547
  simp only [CollatzResearch.WordTrace]
  refine ⟨132198089599892717189743895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88132059733261811459829263 132198089599892717189743895)
  ·
    refine ⟨198297134399839075784615843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132198089599892717189743895 198297134399839075784615843)
    ·
      refine ⟨297445701599758613676923765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198297134399839075784615843 297445701599758613676923765)
      ·
        refine ⟨27885534524977370032211603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297445701599758613676923765 27885534524977370032211603)
        ·
          refine ⟨41828301787466055048317405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27885534524977370032211603 41828301787466055048317405)
          ·
            refine ⟨15685613170299770643119027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41828301787466055048317405 15685613170299770643119027)
            ·
              refine ⟨23528419755449655964678541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685613170299770643119027 23528419755449655964678541)
              ·
                refine ⟨8823157408293620986754453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23528419755449655964678541 8823157408293620986754453)
                ·
                  refine ⟨413585503513763483754115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8823157408293620986754453 413585503513763483754115)
                  ·
                    rfl

theorem cell22_3624547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_3624547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624547 prefixEnd_3624547 := by exact prefixLift 3624547
  have htrace : WordTrace (prefixWord ++ tailWord_3624547) baseStart_3624547 baseEnd_3624547 := by
    simpa [prefixWord, tailWord_3624547, baseEnd_3624547] using wordTrace_append hprefix tailTrace_3624547
  have hstable : (prefixWord ++ tailWord_3624547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624547).length < 2 ^ (prefixWord ++ tailWord_3624547).sum := by decide
  have hdescent : baseEnd_3624547 < baseStart_3624547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624566 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3624566 : Nat := 118140960795 + 3624566 * 2 ^ 59
def prefixEnd_3624566 : Nat := 4983230072969 + 3 ^ 40 * 3624566 * 2
def baseEnd_3624566 : Nat := 1240763014629580735037287

theorem tailTrace_3624566 : CollatzResearch.WordTrace tailWord_3624566 prefixEnd_3624566 1240763014629580735037287 := by
  unfold tailWord_3624566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262423911676492714667847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88132521724549255623123701 8262423911676492714667847)
  ·
    refine ⟨12393635867514739072001771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8262423911676492714667847 12393635867514739072001771)
    ·
      refine ⟨18590453801272108608002657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393635867514739072001771 18590453801272108608002657)
      ·
        refine ⟨13942840350954081456001993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18590453801272108608002657 13942840350954081456001993)
        ·
          refine ⟨10457130263215561092001495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13942840350954081456001993 10457130263215561092001495)
          ·
            refine ⟨15685695394823341638002243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457130263215561092001495 15685695394823341638002243)
            ·
              refine ⟨23528543092235012457003365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685695394823341638002243 23528543092235012457003365)
              ·
                refine ⟨4411601829794064835688131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23528543092235012457003365 4411601829794064835688131)
                ·
                  refine ⟨6617402744691097253532197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411601829794064835688131 6617402744691097253532197)
                  ·
                    refine ⟨1240763014629580735037287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617402744691097253532197 1240763014629580735037287)
                    ·
                      rfl

theorem cell22_3624566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3624566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624566 prefixEnd_3624566 := by exact prefixLift 3624566
  have htrace : WordTrace (prefixWord ++ tailWord_3624566) baseStart_3624566 baseEnd_3624566 := by
    simpa [prefixWord, tailWord_3624566, baseEnd_3624566] using wordTrace_append hprefix tailTrace_3624566
  have hstable : (prefixWord ++ tailWord_3624566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624566).length < 2 ^ (prefixWord ++ tailWord_3624566).sum := by decide
  have hdescent : baseEnd_3624566 < baseStart_3624566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624609 : List Nat := [1, 2, 3, 3, 2, 2, 2, 7]
def baseStart_3624609 : Nat := 118140960795 + 3624609 * 2 ^ 59
def prefixEnd_3624609 : Nat := 4983230072969 + 3 ^ 40 * 3624609 * 2
def baseEnd_3624609 : Nat := 137864192712038106245795

theorem tailTrace_3624609 : CollatzResearch.WordTrace tailWord_3624609 prefixEnd_3624609 137864192712038106245795 := by
  unfold tailWord_3624609
  simp only [CollatzResearch.WordTrace]
  refine ⟨132200350925668101778500881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88133567283778734519000587 132200350925668101778500881)
  ·
    refine ⟨99150263194251076333875661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132200350925668101778500881 99150263194251076333875661)
    ·
      refine ⟨37181348697844153625203373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99150263194251076333875661 37181348697844153625203373)
      ·
        refine ⟨13943005761691557609451265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37181348697844153625203373 13943005761691557609451265)
        ·
          refine ⟨10457254321268668207088449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13943005761691557609451265 10457254321268668207088449)
          ·
            refine ⟨7842940740951501155316337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457254321268668207088449 7842940740951501155316337)
            ·
              refine ⟨5882205555713625866487253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7842940740951501155316337 5882205555713625866487253)
              ·
                refine ⟨137864192712038106245795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5882205555713625866487253 137864192712038106245795)
                ·
                  rfl

theorem cell22_3624609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 7].length) (baseStart_3624609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624609 prefixEnd_3624609 := by exact prefixLift 3624609
  have htrace : WordTrace (prefixWord ++ tailWord_3624609) baseStart_3624609 baseEnd_3624609 := by
    simpa [prefixWord, tailWord_3624609, baseEnd_3624609] using wordTrace_append hprefix tailTrace_3624609
  have hstable : (prefixWord ++ tailWord_3624609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624609).length < 2 ^ (prefixWord ++ tailWord_3624609).sum := by decide
  have hdescent : baseEnd_3624609 < baseStart_3624609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624624 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_3624624 : Nat := 118140960795 + 3624624 * 2 ^ 59
def prefixEnd_3624624 : Nat := 4983230072969 + 3 ^ 40 * 3624624 * 2
def baseEnd_3624624 : Nat := 1240782869214887917087109

theorem tailTrace_3624624 : CollatzResearch.WordTrace tailWord_3624624 prefixEnd_3624624 1240782869214887917087109 := by
  unfold tailWord_3624624
  simp only [CollatzResearch.WordTrace]
  refine ⟨66100449010306879670148463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88133932013742506226864617 66100449010306879670148463)
  ·
    refine ⟨99150673515460319505222695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66100449010306879670148463 99150673515460319505222695)
    ·
      refine ⟨148726010273190479257834043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99150673515460319505222695 148726010273190479257834043)
      ·
        refine ⟨223089015409785718886751065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148726010273190479257834043 223089015409785718886751065)
        ·
          refine ⟨167316761557339289165063299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223089015409785718886751065 167316761557339289165063299)
          ·
            refine ⟨250975142336008933747594949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167316761557339289165063299 250975142336008933747594949)
            ·
              refine ⟨47057839188001675077674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250975142336008933747594949 47057839188001675077674053)
              ·
                refine ⟨8823344847750314077063885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47057839188001675077674053 8823344847750314077063885)
                ·
                  refine ⟨3308754317906367778898957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8823344847750314077063885 3308754317906367778898957)
                  ·
                    refine ⟨1240782869214887917087109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308754317906367778898957 1240782869214887917087109)
                    ·
                      rfl

theorem cell22_3624624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_3624624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624624 prefixEnd_3624624 := by exact prefixLift 3624624
  have htrace : WordTrace (prefixWord ++ tailWord_3624624) baseStart_3624624 baseEnd_3624624 := by
    simpa [prefixWord, tailWord_3624624, baseEnd_3624624] using wordTrace_append hprefix tailTrace_3624624
  have hstable : (prefixWord ++ tailWord_3624624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624624).length < 2 ^ (prefixWord ++ tailWord_3624624).sum := by decide
  have hdescent : baseEnd_3624624 < baseStart_3624624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624684 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3624684 : Nat := 118140960795 + 3624684 * 2 ^ 59
def prefixEnd_3624684 : Nat := 4983230072969 + 3 ^ 40 * 3624684 * 2
def baseEnd_3624684 : Nat := 1240803408441067760586925

theorem tailTrace_3624684 : CollatzResearch.WordTrace tailWord_3624684 prefixEnd_3624684 1240803408441067760586925 := by
  unfold tailWord_3624684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66101543200198194793740553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88135390933597593058320737 66101543200198194793740553)
  ·
    refine ⟨49576157400148646095305415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66101543200198194793740553 49576157400148646095305415)
    ·
      refine ⟨74364236100222969142958123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49576157400148646095305415 74364236100222969142958123)
      ·
        refine ⟨111546354150334453714437185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74364236100222969142958123 111546354150334453714437185)
        ·
          refine ⟨83659765612750840285827889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111546354150334453714437185 83659765612750840285827889)
          ·
            refine ⟨62744824209563130214370917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83659765612750840285827889 62744824209563130214370917)
            ·
              refine ⟨11764654539293086915194547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62744824209563130214370917 11764654539293086915194547)
              ·
                refine ⟨17646981808939630372791821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11764654539293086915194547 17646981808939630372791821)
                ·
                  refine ⟨6617618178352361389796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17646981808939630372791821 6617618178352361389796933)
                  ·
                    refine ⟨1240803408441067760586925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617618178352361389796933 1240803408441067760586925)
                    ·
                      rfl

theorem cell22_3624684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3624684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624684 prefixEnd_3624684 := by exact prefixLift 3624684
  have htrace : WordTrace (prefixWord ++ tailWord_3624684) baseStart_3624684 baseEnd_3624684 := by
    simpa [prefixWord, tailWord_3624684, baseEnd_3624684] using wordTrace_append hprefix tailTrace_3624684
  have hstable : (prefixWord ++ tailWord_3624684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624684).length < 2 ^ (prefixWord ++ tailWord_3624684).sum := by decide
  have hdescent : baseEnd_3624684 < baseStart_3624684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624692 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3624692 : Nat := 118140960795 + 3624692 * 2 ^ 59
def prefixEnd_3624692 : Nat := 4983230072969 + 3 ^ 40 * 3624692 * 2
def baseEnd_3624692 : Nat := 1240806147004558406386901

theorem tailTrace_3624692 : CollatzResearch.WordTrace tailWord_3624692 prefixEnd_3624692 1240806147004558406386901 := by
  unfold tailWord_3624692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66101689092183703476886165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88135585456244937969181553 66101689092183703476886165)
  ·
    refine ⟨3098516676196111100479039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66101689092183703476886165 3098516676196111100479039)
    ·
      refine ⟨4647775014294166650718559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098516676196111100479039 4647775014294166650718559)
      ·
        refine ⟨6971662521441249976077839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647775014294166650718559 6971662521441249976077839)
        ·
          refine ⟨10457493782161874964116759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971662521441249976077839 10457493782161874964116759)
          ·
            refine ⟨15686240673242812446175139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457493782161874964116759 15686240673242812446175139)
            ·
              refine ⟨23529361009864218669262709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686240673242812446175139 23529361009864218669262709)
              ·
                refine ⟨2205877594674770500243379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23529361009864218669262709 2205877594674770500243379)
                ·
                  refine ⟨3308816392012155750365069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205877594674770500243379 3308816392012155750365069)
                  ·
                    refine ⟨1240806147004558406386901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308816392012155750365069 1240806147004558406386901)
                    ·
                      rfl

theorem cell22_3624692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3624692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624692 prefixEnd_3624692 := by exact prefixLift 3624692
  have htrace : WordTrace (prefixWord ++ tailWord_3624692) baseStart_3624692 baseEnd_3624692 := by
    simpa [prefixWord, tailWord_3624692, baseEnd_3624692] using wordTrace_append hprefix tailTrace_3624692
  have hstable : (prefixWord ++ tailWord_3624692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624692).length < 2 ^ (prefixWord ++ tailWord_3624692).sum := by decide
  have hdescent : baseEnd_3624692 < baseStart_3624692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624716 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_3624716 : Nat := 118140960795 + 3624716 * 2 ^ 59
def prefixEnd_3624716 : Nat := 4983230072969 + 3 ^ 40 * 3624716 * 2
def baseEnd_3624716 : Nat := 413604787565010114595609

theorem tailTrace_3624716 : CollatzResearch.WordTrace tailWord_3624716 prefixEnd_3624716 413604787565010114595609 := by
  unfold tailWord_3624716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102126768140229526323001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88136169024186972701764001 66102126768140229526323001)
  ·
    refine ⟨49576595076105172144742251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66102126768140229526323001 49576595076105172144742251)
    ·
      refine ⟨74364892614157758217113377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49576595076105172144742251 74364892614157758217113377)
      ·
        refine ⟨55773669460618318662835033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74364892614157758217113377 55773669460618318662835033)
        ·
          refine ⟨41830252095463738997126275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55773669460618318662835033 41830252095463738997126275)
          ·
            refine ⟨62745378143195608495689413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41830252095463738997126275 62745378143195608495689413)
            ·
              refine ⟨11764758401849176592941765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62745378143195608495689413 11764758401849176592941765)
              ·
                refine ⟨2205892200346720611176581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11764758401849176592941765 2205892200346720611176581)
                ·
                  refine ⟨413604787565010114595609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205892200346720611176581 413604787565010114595609)
                  ·
                    rfl

theorem cell22_3624716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_3624716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624716 prefixEnd_3624716 := by exact prefixLift 3624716
  have htrace : WordTrace (prefixWord ++ tailWord_3624716) baseStart_3624716 baseEnd_3624716 := by
    simpa [prefixWord, tailWord_3624716, baseEnd_3624716] using wordTrace_append hprefix tailTrace_3624716
  have hstable : (prefixWord ++ tailWord_3624716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624716).length < 2 ^ (prefixWord ++ tailWord_3624716).sum := by decide
  have hdescent : baseEnd_3624716 < baseStart_3624716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624821 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3624821 : Nat := 118140960795 + 3624821 * 2 ^ 59
def prefixEnd_3624821 : Nat := 4983230072969 + 3 ^ 40 * 3624821 * 2
def baseEnd_3624821 : Nat := 1240850306340845069911505

theorem tailTrace_3624821 : CollatzResearch.WordTrace tailWord_3624821 prefixEnd_3624821 1240850306340845069911505 := by
  unfold tailWord_3624821
  simp only [CollatzResearch.WordTrace]
  refine ⟨132208083200900061985218317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88138722133933374656812211 132208083200900061985218317)
  ·
    refine ⟨49578031200337523244456869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132208083200900061985218317 49578031200337523244456869)
    ·
      refine ⟨9295880850063285608335663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49578031200337523244456869 9295880850063285608335663)
      ·
        refine ⟨13943821275094928412503495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295880850063285608335663 13943821275094928412503495)
        ·
          refine ⟨20915731912642392618755243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13943821275094928412503495 20915731912642392618755243)
          ·
            refine ⟨31373597868963588928132865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915731912642392618755243 31373597868963588928132865)
            ·
              refine ⟨23530198401722691696099649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31373597868963588928132865 23530198401722691696099649)
              ·
                refine ⟨17647648801292018772074737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23530198401722691696099649 17647648801292018772074737)
                ·
                  refine ⟨13235736600969014079056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17647648801292018772074737 13235736600969014079056053)
                  ·
                    refine ⟨1240850306340845069911505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13235736600969014079056053 1240850306340845069911505)
                    ·
                      rfl

theorem cell22_3624821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3624821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624821 prefixEnd_3624821 := by exact prefixLift 3624821
  have htrace : WordTrace (prefixWord ++ tailWord_3624821) baseStart_3624821 baseEnd_3624821 := by
    simpa [prefixWord, tailWord_3624821, baseEnd_3624821] using wordTrace_append hprefix tailTrace_3624821
  have hstable : (prefixWord ++ tailWord_3624821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624821).length < 2 ^ (prefixWord ++ tailWord_3624821).sum := by decide
  have hdescent : baseEnd_3624821 < baseStart_3624821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624836 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3624836 : Nat := 118140960795 + 3624836 * 2 ^ 59
def prefixEnd_3624836 : Nat := 4983230072969 + 3 ^ 40 * 3624836 * 2
def baseEnd_3624836 : Nat := 1240855441147390030786459

theorem tailTrace_3624836 : CollatzResearch.WordTrace tailWord_3624836 prefixEnd_3624836 1240855441147390030786459 := by
  unfold tailWord_3624836
  simp only [CollatzResearch.WordTrace]
  refine ⟨66104315147922859773507181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88139086863897146364676241 66104315147922859773507181)
  ·
    refine ⟨24789118180471072415065193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66104315147922859773507181 24789118180471072415065193)
    ·
      refine ⟨18591838635353304311298895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24789118180471072415065193 18591838635353304311298895)
      ·
        refine ⟨27887757953029956466948343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18591838635353304311298895 27887757953029956466948343)
        ·
          refine ⟨41831636929544934700422515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27887757953029956466948343 41831636929544934700422515)
          ·
            refine ⟨62747455394317402050633773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41831636929544934700422515 62747455394317402050633773)
            ·
              refine ⟨23530295772869025768987665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62747455394317402050633773 23530295772869025768987665)
              ·
                refine ⟨17647721829651769326740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23530295772869025768987665 17647721829651769326740749)
                ·
                  refine ⟨6617895686119413497527781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17647721829651769326740749 6617895686119413497527781)
                  ·
                    refine ⟨1240855441147390030786459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617895686119413497527781 1240855441147390030786459)
                    ·
                      rfl

theorem cell22_3624836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3624836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624836 prefixEnd_3624836 := by exact prefixLift 3624836
  have htrace : WordTrace (prefixWord ++ tailWord_3624836) baseStart_3624836 baseEnd_3624836 := by
    simpa [prefixWord, tailWord_3624836, baseEnd_3624836] using wordTrace_append hprefix tailTrace_3624836
  have hstable : (prefixWord ++ tailWord_3624836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624836).length < 2 ^ (prefixWord ++ tailWord_3624836).sum := by decide
  have hdescent : baseEnd_3624836 < baseStart_3624836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624868 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3624868 : Nat := 118140960795 + 3624868 * 2 ^ 59
def prefixEnd_3624868 : Nat := 4983230072969 + 3 ^ 40 * 3624868 * 2
def baseEnd_3624868 : Nat := 413622131800450871328787

theorem tailTrace_3624868 : CollatzResearch.WordTrace tailWord_3624868 prefixEnd_3624868 413622131800450871328787 := by
  unfold tailWord_3624868
  simp only [CollatzResearch.WordTrace]
  refine ⟨66104898715864894506089629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88139864954486526008119505 66104898715864894506089629)
  ·
    refine ⟨24789337018449335439783611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66104898715864894506089629 24789337018449335439783611)
    ·
      refine ⟨37184005527674003159675417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24789337018449335439783611 37184005527674003159675417)
      ·
        refine ⟨27888004145755502369756563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37184005527674003159675417 27888004145755502369756563)
        ·
          refine ⟨41832006218633253554634845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27888004145755502369756563 41832006218633253554634845)
          ·
            refine ⟨15687002331987470082988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41832006218633253554634845 15687002331987470082988067)
            ·
              refine ⟨23530503497981205124482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15687002331987470082988067 23530503497981205124482101)
              ·
                refine ⟨2205984702935737980420197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23530503497981205124482101 2205984702935737980420197)
                ·
                  refine ⟨413622131800450871328787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205984702935737980420197 413622131800450871328787)
                  ·
                    rfl

theorem cell22_3624868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3624868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624868 prefixEnd_3624868 := by exact prefixLift 3624868
  have htrace : WordTrace (prefixWord ++ tailWord_3624868) baseStart_3624868 baseEnd_3624868 := by
    simpa [prefixWord, tailWord_3624868, baseEnd_3624868] using wordTrace_append hprefix tailTrace_3624868
  have hstable : (prefixWord ++ tailWord_3624868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624868).length < 2 ^ (prefixWord ++ tailWord_3624868).sum := by decide
  have hdescent : baseEnd_3624868 < baseStart_3624868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624879 : List Nat := [1, 1, 2, 1, 2, 2, 13]
def baseStart_3624879 : Nat := 118140960795 + 3624879 * 2 ^ 59
def prefixEnd_3624879 : Nat := 4983230072969 + 3 ^ 40 * 3624879 * 2
def baseEnd_3624879 : Nat := 45958154108376009331901

theorem tailTrace_3624879 : CollatzResearch.WordTrace tailWord_3624879 prefixEnd_3624879 45958154108376009331901 := by
  unfold tailWord_3624879
  simp only [CollatzResearch.WordTrace]
  refine ⟨132210198634689937890829691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88140132423126625260553127 132210198634689937890829691)
  ·
    refine ⟨198315297952034906836244537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132210198634689937890829691 198315297952034906836244537)
    ·
      refine ⟨148736473464026180127183403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198315297952034906836244537 148736473464026180127183403)
      ·
        refine ⟨223104710196039270190775105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148736473464026180127183403 223104710196039270190775105)
        ·
          refine ⟨167328532647029452643081329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223104710196039270190775105 167328532647029452643081329)
          ·
            refine ⟨125496399485272089482310997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167328532647029452643081329 125496399485272089482310997)
            ·
              refine ⟨45958154108376009331901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 125496399485272089482310997 45958154108376009331901)
              ·
                rfl

theorem cell22_3624879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 13].length) (baseStart_3624879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624879 prefixEnd_3624879 := by exact prefixLift 3624879
  have htrace : WordTrace (prefixWord ++ tailWord_3624879) baseStart_3624879 baseEnd_3624879 := by
    simpa [prefixWord, tailWord_3624879, baseEnd_3624879] using wordTrace_append hprefix tailTrace_3624879
  have hstable : (prefixWord ++ tailWord_3624879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624879).length < 2 ^ (prefixWord ++ tailWord_3624879).sum := by decide
  have hdescent : baseEnd_3624879 < baseStart_3624879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624930 : List Nat := [3, 3, 3, 1, 2, 2, 8]
def baseStart_3624930 : Nat := 118140960795 + 3624930 * 2 ^ 59
def prefixEnd_3624930 : Nat := 4983230072969 + 3 ^ 40 * 3624930 * 2
def baseEnd_3624930 : Nat := 45958800713644634034673

theorem tailTrace_3624930 : CollatzResearch.WordTrace tailWord_3624930 prefixEnd_3624930 45958800713644634034673 := by
  unfold tailWord_3624930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33053014689376293400234061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88141372505003449067290829 33053014689376293400234061)
  ·
    refine ⟨12394880508516110025087773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33053014689376293400234061 12394880508516110025087773)
    ·
      refine ⟨4648080190693541259407915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12394880508516110025087773 4648080190693541259407915)
      ·
        refine ⟨6972120286040311889111873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648080190693541259407915 6972120286040311889111873)
        ·
          refine ⟨5229090214530233916833905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972120286040311889111873 5229090214530233916833905)
          ·
            refine ⟨3921817660897675437625429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229090214530233916833905 3921817660897675437625429)
            ·
              refine ⟨45958800713644634034673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3921817660897675437625429 45958800713644634034673)
              ·
                rfl

theorem cell22_3624930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 8].length) (baseStart_3624930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624930 prefixEnd_3624930 := by exact prefixLift 3624930
  have htrace : WordTrace (prefixWord ++ tailWord_3624930) baseStart_3624930 baseEnd_3624930 := by
    simpa [prefixWord, tailWord_3624930, baseEnd_3624930] using wordTrace_append hprefix tailTrace_3624930
  have hstable : (prefixWord ++ tailWord_3624930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624930).length < 2 ^ (prefixWord ++ tailWord_3624930).sum := by decide
  have hdescent : baseEnd_3624930 < baseStart_3624930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624956 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3624956 : Nat := 118140960795 + 3624956 * 2 ^ 59
def prefixEnd_3624956 : Nat := 4983230072969 + 3 ^ 40 * 3624956 * 2
def baseEnd_3624956 : Nat := 1240896519599749717786091

theorem tailTrace_3624956 : CollatzResearch.WordTrace tailWord_3624956 prefixEnd_3624956 1240896519599749717786091 := by
  unfold tailWord_3624956
  simp only [CollatzResearch.WordTrace]
  refine ⟨66106503527705490020691361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88142004703607320027588481 66106503527705490020691361)
  ·
    refine ⟨49579877645779117515518521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66106503527705490020691361 49579877645779117515518521)
    ·
      refine ⟨37184908234334338136638891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49579877645779117515518521 37184908234334338136638891)
      ·
        refine ⟨55777362351501507204958337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37184908234334338136638891 55777362351501507204958337)
        ·
          refine ⟨41833021763626130403718753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55777362351501507204958337 41833021763626130403718753)
          ·
            refine ⟨31374766322719597802789065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41833021763626130403718753 31374766322719597802789065)
            ·
              refine ⟨23531074742039698352091799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31374766322719597802789065 23531074742039698352091799)
              ·
                refine ⟨35296612113059547528137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23531074742039698352091799 35296612113059547528137699)
                ·
                  refine ⟨52944918169589321292206549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35296612113059547528137699 52944918169589321292206549)
                  ·
                    refine ⟨1240896519599749717786091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52944918169589321292206549 1240896519599749717786091)
                    ·
                      rfl

theorem cell22_3624956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3624956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624956 prefixEnd_3624956 := by exact prefixLift 3624956
  have htrace : WordTrace (prefixWord ++ tailWord_3624956) baseStart_3624956 baseEnd_3624956 := by
    simpa [prefixWord, tailWord_3624956, baseEnd_3624956] using wordTrace_append hprefix tailTrace_3624956
  have hstable : (prefixWord ++ tailWord_3624956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624956).length < 2 ^ (prefixWord ++ tailWord_3624956).sum := by decide
  have hdescent : baseEnd_3624956 < baseStart_3624956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624966 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3624966 : Nat := 118140960795 + 3624966 * 2 ^ 59
def prefixEnd_3624966 : Nat := 4983230072969 + 3 ^ 40 * 3624966 * 2
def baseEnd_3624966 : Nat := 1240899942804113025036061

theorem tailTrace_3624966 : CollatzResearch.WordTrace tailWord_3624966 prefixEnd_3624966 1240899942804113025036061 := by
  unfold tailWord_3624966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131667868292960992163961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88142247856916501166164501 4131667868292960992163961)
  ·
    refine ⟨3098750901219720744122971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4131667868292960992163961 3098750901219720744122971)
    ·
      refine ⟨4648126351829581116184457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098750901219720744122971 4648126351829581116184457)
      ·
        refine ⟨3486094763872185837138343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648126351829581116184457 3486094763872185837138343)
        ·
          refine ⟨5229142145808278755707515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486094763872185837138343 5229142145808278755707515)
          ·
            refine ⟨7843713218712418133561273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229142145808278755707515 7843713218712418133561273)
            ·
              refine ⟨5882784914034313600170955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7843713218712418133561273 5882784914034313600170955)
              ·
                refine ⟨8824177371051470400256433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882784914034313600170955 8824177371051470400256433)
                ·
                  refine ⟨6618133028288602800192325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824177371051470400256433 6618133028288602800192325)
                  ·
                    refine ⟨1240899942804113025036061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618133028288602800192325 1240899942804113025036061)
                    ·
                      rfl

theorem cell22_3624966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3624966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624966 prefixEnd_3624966 := by exact prefixLift 3624966
  have htrace : WordTrace (prefixWord ++ tailWord_3624966) baseStart_3624966 baseEnd_3624966 := by
    simpa [prefixWord, tailWord_3624966, baseEnd_3624966] using wordTrace_append hprefix tailTrace_3624966
  have hstable : (prefixWord ++ tailWord_3624966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624966).length < 2 ^ (prefixWord ++ tailWord_3624966).sum := by decide
  have hdescent : baseEnd_3624966 < baseStart_3624966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624996 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3624996 : Nat := 118140960795 + 3624996 * 2 ^ 59
def prefixEnd_3624996 : Nat := 4983230072969 + 3 ^ 40 * 3624996 * 2
def baseEnd_3624996 : Nat := 1240910212417202946785969

theorem tailTrace_3624996 : CollatzResearch.WordTrace tailWord_3624996 prefixEnd_3624996 1240910212417202946785969 := by
  unfold tailWord_3624996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66107232987633033436419421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88142977316844044581892561 66107232987633033436419421)
  ·
    refine ⟨24790212370362387538657283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66107232987633033436419421 24790212370362387538657283)
    ·
      refine ⟨37185318555543581307985925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24790212370362387538657283 37185318555543581307985925)
      ·
        refine ⟨6972247229164421495247361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37185318555543581307985925 6972247229164421495247361)
        ·
          refine ⟨5229185421873316121435521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972247229164421495247361 5229185421873316121435521)
          ·
            refine ⟨3921889066404987091076641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229185421873316121435521 3921889066404987091076641)
            ·
              refine ⟨2941416799803740318307481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921889066404987091076641 2941416799803740318307481)
              ·
                refine ⟨2206062599852805238730611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941416799803740318307481 2206062599852805238730611)
                ·
                  refine ⟨3309093899779207858095917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206062599852805238730611 3309093899779207858095917)
                  ·
                    refine ⟨1240910212417202946785969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309093899779207858095917 1240910212417202946785969)
                    ·
                      rfl

theorem cell22_3624996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3624996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3624996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3624996 prefixEnd_3624996 := by exact prefixLift 3624996
  have htrace : WordTrace (prefixWord ++ tailWord_3624996) baseStart_3624996 baseEnd_3624996 := by
    simpa [prefixWord, tailWord_3624996, baseEnd_3624996] using wordTrace_append hprefix tailTrace_3624996
  have hstable : (prefixWord ++ tailWord_3624996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624996).length < 2 ^ (prefixWord ++ tailWord_3624996).sum := by decide
  have hdescent : baseEnd_3624996 < baseStart_3624996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625018 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_3625018 : Nat := 118140960795 + 3625018 * 2 ^ 59
def prefixEnd_3625018 : Nat := 4983230072969 + 3 ^ 40 * 3625018 * 2
def baseEnd_3625018 : Nat := 1240917743466802222735901

theorem tailTrace_3625018 : CollatzResearch.WordTrace tailWord_3625018 prefixEnd_3625018 1240917743466802222735901 := by
  unfold tailWord_3625018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33053817095296591157534927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88143512254124243086759805 33053817095296591157534927)
  ·
    refine ⟨49580725642944886736302391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33053817095296591157534927 49580725642944886736302391)
    ·
      refine ⟨74371088464417330104453587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49580725642944886736302391 74371088464417330104453587)
      ·
        refine ⟨111556632696625995156680381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74371088464417330104453587 111556632696625995156680381)
        ·
          refine ⟨41833737261234748183755143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111556632696625995156680381 41833737261234748183755143)
          ·
            refine ⟨62750605891852122275632715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41833737261234748183755143 62750605891852122275632715)
            ·
              refine ⟨94125908837778183413449073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62750605891852122275632715 94125908837778183413449073)
              ·
                refine ⟨70594431628333637560086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94125908837778183413449073 70594431628333637560086805)
                ·
                  refine ⟨3309113982578139260629069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70594431628333637560086805 3309113982578139260629069)
                  ·
                    refine ⟨1240917743466802222735901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309113982578139260629069 1240917743466802222735901)
                    ·
                      rfl

theorem cell22_3625018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_3625018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625018 prefixEnd_3625018 := by exact prefixLift 3625018
  have htrace : WordTrace (prefixWord ++ tailWord_3625018) baseStart_3625018 baseEnd_3625018 := by
    simpa [prefixWord, tailWord_3625018, baseEnd_3625018] using wordTrace_append hprefix tailTrace_3625018
  have hstable : (prefixWord ++ tailWord_3625018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625018).length < 2 ^ (prefixWord ++ tailWord_3625018).sum := by decide
  have hdescent : baseEnd_3625018 < baseStart_3625018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625037 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3625037 : Nat := 118140960795 + 3625037 * 2 ^ 59
def prefixEnd_3625037 : Nat := 4983230072969 + 3 ^ 40 * 3625037 * 2
def baseEnd_3625037 : Nat := 413641415851697502170281

theorem tailTrace_3625037 : CollatzResearch.WordTrace tailWord_3625037 prefixEnd_3625037 413641415851697502170281 := by
  unfold tailWord_3625037
  simp only [CollatzResearch.WordTrace]
  refine ⟨132215961368117530875081365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88143974245411687250054243 132215961368117530875081365)
  ·
    refine ⟨6197623189130509259769439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132215961368117530875081365 6197623189130509259769439)
    ·
      refine ⟨9296434783695763889654159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197623189130509259769439 9296434783695763889654159)
      ·
        refine ⟨13944652175543645834481239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296434783695763889654159 13944652175543645834481239)
        ·
          refine ⟨20916978263315468751721859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13944652175543645834481239 20916978263315468751721859)
          ·
            refine ⟨31375467394973203127582789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20916978263315468751721859 31375467394973203127582789)
            ·
              refine ⟨5882900136557475586421773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31375467394973203127582789 5882900136557475586421773)
              ·
                refine ⟨2206087551209053344908165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5882900136557475586421773 2206087551209053344908165)
                ·
                  refine ⟨413641415851697502170281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206087551209053344908165 413641415851697502170281)
                  ·
                    rfl

theorem cell22_3625037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3625037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625037 prefixEnd_3625037 := by exact prefixLift 3625037
  have htrace : WordTrace (prefixWord ++ tailWord_3625037) baseStart_3625037 baseEnd_3625037 := by
    simpa [prefixWord, tailWord_3625037, baseEnd_3625037] using wordTrace_append hprefix tailTrace_3625037
  have hstable : (prefixWord ++ tailWord_3625037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625037).length < 2 ^ (prefixWord ++ tailWord_3625037).sum := by decide
  have hdescent : baseEnd_3625037 < baseStart_3625037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625052 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3625052 : Nat := 118140960795 + 3625052 * 2 ^ 59
def prefixEnd_3625052 : Nat := 4983230072969 + 3 ^ 40 * 3625052 * 2
def baseEnd_3625052 : Nat := 1240929382361637467385797

theorem tailTrace_3625052 : CollatzResearch.WordTrace tailWord_3625052 prefixEnd_3625052 1240929382361637467385797 := by
  unfold tailWord_3625052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66108254231531594218438705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88144338975375458957918273 66108254231531594218438705)
  ·
    refine ⟨49581190673648695663829029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66108254231531594218438705 49581190673648695663829029)
    ·
      refine ⟨9296473251309130436967943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49581190673648695663829029 9296473251309130436967943)
      ·
        refine ⟨13944709876963695655451915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296473251309130436967943 13944709876963695655451915)
        ·
          refine ⟨20917064815445543483177873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13944709876963695655451915 20917064815445543483177873)
          ·
            refine ⟨15687798611584157612383405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20917064815445543483177873 15687798611584157612383405)
            ·
              refine ⟨5882924479344059104643777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15687798611584157612383405 5882924479344059104643777)
              ·
                refine ⟨4412193359508044328482833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5882924479344059104643777 4412193359508044328482833)
                ·
                  refine ⟨3309145019631033246362125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412193359508044328482833 3309145019631033246362125)
                  ·
                    refine ⟨1240929382361637467385797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309145019631033246362125 1240929382361637467385797)
                    ·
                      rfl

theorem cell22_3625052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3625052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625052 prefixEnd_3625052 := by exact prefixLift 3625052
  have htrace : WordTrace (prefixWord ++ tailWord_3625052) baseStart_3625052 baseEnd_3625052 := by
    simpa [prefixWord, tailWord_3625052, baseEnd_3625052] using wordTrace_append hprefix tailTrace_3625052
  have hstable : (prefixWord ++ tailWord_3625052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625052).length < 2 ^ (prefixWord ++ tailWord_3625052).sum := by decide
  have hdescent : baseEnd_3625052 < baseStart_3625052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625054 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3625054 : Nat := 118140960795 + 3625054 * 2 ^ 59
def prefixEnd_3625054 : Nat := 4983230072969 + 3 ^ 40 * 3625054 * 2
def baseEnd_3625054 : Nat := 413643355667503376278597

theorem tailTrace_3625054 : CollatzResearch.WordTrace tailWord_3625054 prefixEnd_3625054 413643355667503376278597 := by
  unfold tailWord_3625054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527072676131992847306277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88144387606037295185633477 16527072676131992847306277)
  ·
    refine ⟨3098826126774748658869927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16527072676131992847306277 3098826126774748658869927)
    ·
      refine ⟨4648239190162122988304891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098826126774748658869927 4648239190162122988304891)
      ·
        refine ⟨6972358785243184482457337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648239190162122988304891 6972358785243184482457337)
        ·
          refine ⟨5229269088932388361843003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972358785243184482457337 5229269088932388361843003)
          ·
            refine ⟨7843903633398582542764505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229269088932388361843003 7843903633398582542764505)
            ·
              refine ⟨5882927725048936907073379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7843903633398582542764505 5882927725048936907073379)
              ·
                refine ⟨8824391587573405360610069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882927725048936907073379 8824391587573405360610069)
                ·
                  refine ⟨413643355667503376278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8824391587573405360610069 413643355667503376278597)
                  ·
                    rfl

theorem cell22_3625054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3625054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625054 prefixEnd_3625054 := by exact prefixLift 3625054
  have htrace : WordTrace (prefixWord ++ tailWord_3625054) baseStart_3625054 baseEnd_3625054 := by
    simpa [prefixWord, tailWord_3625054, baseEnd_3625054] using wordTrace_append hprefix tailTrace_3625054
  have hstable : (prefixWord ++ tailWord_3625054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625054).length < 2 ^ (prefixWord ++ tailWord_3625054).sum := by decide
  have hdescent : baseEnd_3625054 < baseStart_3625054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625093 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3625093 : Nat := 118140960795 + 3625093 * 2 ^ 59
def prefixEnd_3625093 : Nat := 4983230072969 + 3 ^ 40 * 3625093 * 2
def baseEnd_3625093 : Nat := 413647805833175675703557

theorem tailTrace_3625093 : CollatzResearch.WordTrace tailWord_3625093 prefixEnd_3625093 413647805833175675703557 := by
  unfold tailWord_3625093
  simp only [CollatzResearch.WordTrace]
  refine ⟨132218003855914652439119933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88145335903943101626079955 132218003855914652439119933)
  ·
    refine ⟨49581751445967994664669975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132218003855914652439119933 49581751445967994664669975)
    ·
      refine ⟨74372627168951991997004963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49581751445967994664669975 74372627168951991997004963)
      ·
        refine ⟨111558940753427987995507445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74372627168951991997004963 111558940753427987995507445)
        ·
          refine ⟨10458650695633873874578823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111558940753427987995507445 10458650695633873874578823)
          ·
            refine ⟨15687976043450810811868235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458650695633873874578823 15687976043450810811868235)
            ·
              refine ⟨23531964065176216217802353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15687976043450810811868235 23531964065176216217802353)
              ·
                refine ⟨17648973048882162163351765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23531964065176216217802353 17648973048882162163351765)
                ·
                  refine ⟨413647805833175675703557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17648973048882162163351765 413647805833175675703557)
                  ·
                    rfl

theorem cell22_3625093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3625093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625093 prefixEnd_3625093 := by exact prefixLift 3625093
  have htrace : WordTrace (prefixWord ++ tailWord_3625093) baseStart_3625093 baseEnd_3625093 := by
    simpa [prefixWord, tailWord_3625093, baseEnd_3625093] using wordTrace_append hprefix tailTrace_3625093
  have hstable : (prefixWord ++ tailWord_3625093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625093).length < 2 ^ (prefixWord ++ tailWord_3625093).sum := by decide
  have hdescent : baseEnd_3625093 < baseStart_3625093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625114 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_3625114 : Nat := 118140960795 + 3625114 * 2 ^ 59
def prefixEnd_3625114 : Nat := 4983230072969 + 3 ^ 40 * 3625114 * 2
def baseEnd_3625114 : Nat := 1240950606228689972335607

theorem tailTrace_3625114 : CollatzResearch.WordTrace tailWord_3625114 prefixEnd_3625114 1240950606228689972335607 := by
  unfold tailWord_3625114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33054692447209643256408599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88145846525892382017089597 33054692447209643256408599)
  ·
    refine ⟨49582038670814464884612899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33054692447209643256408599 49582038670814464884612899)
    ·
      refine ⟨74373058006221697326919349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49582038670814464884612899 74373058006221697326919349)
      ·
        refine ⟨6972474188083284124398689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74373058006221697326919349 6972474188083284124398689)
        ·
          refine ⟨5229355641062463093299017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972474188083284124398689 5229355641062463093299017)
          ·
            refine ⟨3922016730796847319974263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229355641062463093299017 3922016730796847319974263)
            ·
              refine ⟨5883025096195270979961395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922016730796847319974263 5883025096195270979961395)
              ·
                refine ⟨8824537644292906469942093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883025096195270979961395 8824537644292906469942093)
                ·
                  refine ⟨3309201616609839926228285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8824537644292906469942093 3309201616609839926228285)
                  ·
                    refine ⟨1240950606228689972335607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309201616609839926228285 1240950606228689972335607)
                    ·
                      rfl

theorem cell22_3625114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_3625114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625114 prefixEnd_3625114 := by exact prefixLift 3625114
  have htrace : WordTrace (prefixWord ++ tailWord_3625114) baseStart_3625114 baseEnd_3625114 := by
    simpa [prefixWord, tailWord_3625114, baseEnd_3625114] using wordTrace_append hprefix tailTrace_3625114
  have hstable : (prefixWord ++ tailWord_3625114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625114).length < 2 ^ (prefixWord ++ tailWord_3625114).sum := by decide
  have hdescent : baseEnd_3625114 < baseStart_3625114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625127 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 5]
def baseStart_3625127 : Nat := 118140960795 + 3625127 * 2 ^ 59
def prefixEnd_3625127 : Nat := 4983230072969 + 3 ^ 40 * 3625127 * 2
def baseEnd_3625127 : Nat := 413651685464787423920189

theorem tailTrace_3625127 : CollatzResearch.WordTrace tailWord_3625127 prefixEnd_3625127 413651685464787423920189 := by
  unfold tailWord_3625127
  simp only [CollatzResearch.WordTrace]
  refine ⟨132219243937791476245857635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88146162625194317497238423 132219243937791476245857635)
  ·
    refine ⟨198328865906687214368786453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132219243937791476245857635 198328865906687214368786453)
    ·
      refine ⟨9296665589375963173536865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198328865906687214368786453 9296665589375963173536865)
      ·
        refine ⟨6972499192031972380152649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9296665589375963173536865 6972499192031972380152649)
        ·
          refine ⟨5229374394023979285114487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972499192031972380152649 5229374394023979285114487)
          ·
            refine ⟨7844061591035968927671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229374394023979285114487 7844061591035968927671731)
            ·
              refine ⟨11766092386553953391507597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844061591035968927671731 11766092386553953391507597)
              ·
                refine ⟨4412284644957732521815349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11766092386553953391507597 4412284644957732521815349)
                ·
                  refine ⟨413651685464787423920189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412284644957732521815349 413651685464787423920189)
                  ·
                    rfl

theorem cell22_3625127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].length) (baseStart_3625127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625127 prefixEnd_3625127 := by exact prefixLift 3625127
  have htrace : WordTrace (prefixWord ++ tailWord_3625127) baseStart_3625127 baseEnd_3625127 := by
    simpa [prefixWord, tailWord_3625127, baseEnd_3625127] using wordTrace_append hprefix tailTrace_3625127
  have hstable : (prefixWord ++ tailWord_3625127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625127).length < 2 ^ (prefixWord ++ tailWord_3625127).sum := by decide
  have hdescent : baseEnd_3625127 < baseStart_3625127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625138 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3625138 : Nat := 118140960795 + 3625138 * 2 ^ 59
def prefixEnd_3625138 : Nat := 4983230072969 + 3 ^ 40 * 3625138 * 2
def baseEnd_3625138 : Nat := 413652940639720636578511

theorem tailTrace_3625138 : CollatzResearch.WordTrace tailWord_3625138 prefixEnd_3625138 413652940639720636578511 := by
  unfold tailWord_3625138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33054911285187906281127017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88146430093834416749672045 33054911285187906281127017)
  ·
    refine ⟨24791183463890929710845263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33054911285187906281127017 24791183463890929710845263)
    ·
      refine ⟨37186775195836394566267895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791183463890929710845263 37186775195836394566267895)
      ·
        refine ⟨55780162793754591849401843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37186775195836394566267895 55780162793754591849401843)
        ·
          refine ⟨83670244190631887774102765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55780162793754591849401843 83670244190631887774102765)
          ·
            refine ⟨31376341571486957915288537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83670244190631887774102765 31376341571486957915288537)
            ·
              refine ⟨23532256178615218436466403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31376341571486957915288537 23532256178615218436466403)
              ·
                refine ⟨35298384267922827654699605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23532256178615218436466403 35298384267922827654699605)
                ·
                  refine ⟨413652940639720636578511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35298384267922827654699605 413652940639720636578511)
                  ·
                    rfl

theorem cell22_3625138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3625138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625138 prefixEnd_3625138 := by exact prefixLift 3625138
  have htrace : WordTrace (prefixWord ++ tailWord_3625138) baseStart_3625138 baseEnd_3625138 := by
    simpa [prefixWord, tailWord_3625138, baseEnd_3625138] using wordTrace_append hprefix tailTrace_3625138
  have hstable : (prefixWord ++ tailWord_3625138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625138).length < 2 ^ (prefixWord ++ tailWord_3625138).sum := by decide
  have hdescent : baseEnd_3625138 < baseStart_3625138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625202 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_3625202 : Nat := 118140960795 + 3625202 * 2 ^ 59
def prefixEnd_3625202 : Nat := 4983230072969 + 3 ^ 40 * 3625202 * 2
def baseEnd_3625202 : Nat := 1240980730427087076135337

theorem tailTrace_3625202 : CollatzResearch.WordTrace tailWord_3625202 prefixEnd_3625202 1240980730427087076135337 := by
  unfold tailWord_3625202
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055494853129941013709465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88147986275013176036558573 33055494853129941013709465)
  ·
    refine ⟨24791621139847455760282099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33055494853129941013709465 24791621139847455760282099)
    ·
      refine ⟨37187431709771183640423149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791621139847455760282099 37187431709771183640423149)
      ·
        refine ⟨13945286891164193865158681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37187431709771183640423149 13945286891164193865158681)
        ·
          refine ⟨10458965168373145398869011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13945286891164193865158681 10458965168373145398869011)
          ·
            refine ⟨15688447752559718098303517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458965168373145398869011 15688447752559718098303517)
            ·
              refine ⟨5883167907209894286863819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15688447752559718098303517 5883167907209894286863819)
              ·
                refine ⟨8824751860814841430295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883167907209894286863819 8824751860814841430295729)
                ·
                  refine ⟨6618563895611131072721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824751860814841430295729 6618563895611131072721797)
                  ·
                    refine ⟨1240980730427087076135337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618563895611131072721797 1240980730427087076135337)
                    ·
                      rfl

theorem cell22_3625202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_3625202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625202 prefixEnd_3625202 := by exact prefixLift 3625202
  have htrace : WordTrace (prefixWord ++ tailWord_3625202) baseStart_3625202 baseEnd_3625202 := by
    simpa [prefixWord, tailWord_3625202, baseEnd_3625202] using wordTrace_append hprefix tailTrace_3625202
  have hstable : (prefixWord ++ tailWord_3625202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625202).length < 2 ^ (prefixWord ++ tailWord_3625202).sum := by decide
  have hdescent : baseEnd_3625202 < baseStart_3625202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625215 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 5, 3]
def baseStart_3625215 : Nat := 118140960795 + 3625215 * 2 ^ 59
def prefixEnd_3625215 : Nat := 4983230072969 + 3 ^ 40 * 3625215 * 2
def baseEnd_3625215 : Nat := 1240985180592759375560297

theorem tailTrace_3625215 : CollatzResearch.WordTrace tailWord_3625215 prefixEnd_3625215 1240985180592759375560297 := by
  unfold tailWord_3625215
  simp only [CollatzResearch.WordTrace]
  refine ⟨132222453561472667275061099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88148302374315111516707399 132222453561472667275061099)
  ·
    refine ⟨198333680342209000912591649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132222453561472667275061099 198333680342209000912591649)
    ·
      refine ⟨148750260256656750684443737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198333680342209000912591649 148750260256656750684443737)
      ·
        refine ⟨111562695192492563013332803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148750260256656750684443737 111562695192492563013332803)
        ·
          refine ⟨167344042788738844519999205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111562695192492563013332803 167344042788738844519999205)
          ·
            refine ⟨31377008022888533347499851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167344042788738844519999205 31377008022888533347499851)
            ·
              refine ⟨47065512034332800021249777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31377008022888533347499851 47065512034332800021249777)
              ·
                refine ⟨35299134025749600015937333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47065512034332800021249777 35299134025749600015937333)
                ·
                  refine ⟨3309293814914025001494125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35299134025749600015937333 3309293814914025001494125)
                  ·
                    refine ⟨1240985180592759375560297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309293814914025001494125 1240985180592759375560297)
                    ·
                      rfl

theorem cell22_3625215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_3625215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625215 prefixEnd_3625215 := by exact prefixLift 3625215
  have htrace : WordTrace (prefixWord ++ tailWord_3625215) baseStart_3625215 baseEnd_3625215 := by
    simpa [prefixWord, tailWord_3625215, baseEnd_3625215] using wordTrace_append hprefix tailTrace_3625215
  have hstable : (prefixWord ++ tailWord_3625215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625215).length < 2 ^ (prefixWord ++ tailWord_3625215).sum := by decide
  have hdescent : baseEnd_3625215 < baseStart_3625215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625305 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3625305 : Nat := 118140960795 + 3625305 * 2 ^ 59
def prefixEnd_3625305 : Nat := 4983230072969 + 3 ^ 40 * 3625305 * 2
def baseEnd_3625305 : Nat := 1241015989432029140810021

theorem tailTrace_3625305 : CollatzResearch.WordTrace tailWord_3625305 prefixEnd_3625305 1241015989432029140810021 := by
  unfold tailWord_3625305
  simp only [CollatzResearch.WordTrace]
  refine ⟨132225736131146612645837369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88150490754097741763891579 132225736131146612645837369)
  ·
    refine ⟨99169302098359959484378027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132225736131146612645837369 99169302098359959484378027)
    ·
      refine ⟨148753953147539939226567041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99169302098359959484378027 148753953147539939226567041)
      ·
        refine ⟨111565464860654954419925281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148753953147539939226567041 111565464860654954419925281)
        ·
          refine ⟨83674098645491215814943961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111565464860654954419925281 83674098645491215814943961)
          ·
            refine ⟨62755573984118411861207971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83674098645491215814943961 62755573984118411861207971)
            ·
              refine ⟨94133360976177617791811957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62755573984118411861207971 94133360976177617791811957)
              ·
                refine ⟨8825002591516651667982371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94133360976177617791811957 8825002591516651667982371)
                ·
                  refine ⟨13237503887274977501973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825002591516651667982371 13237503887274977501973557)
                  ·
                    refine ⟨1241015989432029140810021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13237503887274977501973557 1241015989432029140810021)
                    ·
                      rfl

theorem cell22_3625305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3625305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625305 prefixEnd_3625305 := by exact prefixLift 3625305
  have htrace : WordTrace (prefixWord ++ tailWord_3625305) baseStart_3625305 baseEnd_3625305 := by
    simpa [prefixWord, tailWord_3625305, baseEnd_3625305] using wordTrace_append hprefix tailTrace_3625305
  have hstable : (prefixWord ++ tailWord_3625305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625305).length < 2 ^ (prefixWord ++ tailWord_3625305).sum := by decide
  have hdescent : baseEnd_3625305 < baseStart_3625305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625322 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3625322 : Nat := 118140960795 + 3625322 * 2 ^ 59
def prefixEnd_3625322 : Nat := 4983230072969 + 3 ^ 40 * 3625322 * 2
def baseEnd_3625322 : Nat := 1241021808879446763134969

theorem tailTrace_3625322 : CollatzResearch.WordTrace tailWord_3625322 prefixEnd_3625322 1241021808879446763134969 := by
  unfold tailWord_3625322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33056589043021256137301555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88150904114723349699470813 33056589043021256137301555)
  ·
    refine ⟨49584883564531884205952333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33056589043021256137301555 49584883564531884205952333)
    ·
      refine ⟨18594331336699456577232125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49584883564531884205952333 18594331336699456577232125)
      ·
        refine ⟨6972874251262296216462047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18594331336699456577232125 6972874251262296216462047)
        ·
          refine ⟨10459311376893444324693071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972874251262296216462047 10459311376893444324693071)
          ·
            refine ⟨15688967065340166487039607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459311376893444324693071 15688967065340166487039607)
            ·
              refine ⟨23533450598010249730559411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688967065340166487039607 23533450598010249730559411)
              ·
                refine ⟨35300175897015374595839117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533450598010249730559411 35300175897015374595839117)
                ·
                  refine ⟨13237565961380765473439669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35300175897015374595839117 13237565961380765473439669)
                  ·
                    refine ⟨1241021808879446763134969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13237565961380765473439669 1241021808879446763134969)
                    ·
                      rfl

theorem cell22_3625322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3625322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625322 prefixEnd_3625322 := by exact prefixLift 3625322
  have htrace : WordTrace (prefixWord ++ tailWord_3625322) baseStart_3625322 baseEnd_3625322 := by
    simpa [prefixWord, tailWord_3625322, baseEnd_3625322] using wordTrace_append hprefix tailTrace_3625322
  have hstable : (prefixWord ++ tailWord_3625322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625322).length < 2 ^ (prefixWord ++ tailWord_3625322).sum := by decide
  have hdescent : baseEnd_3625322 < baseStart_3625322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625339 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 2, 3]
def baseStart_3625339 : Nat := 118140960795 + 3625339 * 2 ^ 59
def prefixEnd_3625339 : Nat := 4983230072969 + 3 ^ 40 * 3625339 * 2
def baseEnd_3625339 : Nat := 1241027628326864385459917

theorem tailTrace_3625339 : CollatzResearch.WordTrace tailWord_3625339 prefixEnd_3625339 1241027628326864385459917 := by
  unfold tailWord_3625339
  simp only [CollatzResearch.WordTrace]
  refine ⟨132226976213023436452575071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88151317475348957635050047 132226976213023436452575071)
  ·
    refine ⟨198340464319535154678862607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132226976213023436452575071 198340464319535154678862607)
    ·
      refine ⟨297510696479302732018293911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198340464319535154678862607 297510696479302732018293911)
      ·
        refine ⟨446266044718954098027440867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297510696479302732018293911 446266044718954098027440867)
        ·
          refine ⟨669399067078431147041161301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446266044718954098027440867 669399067078431147041161301)
          ·
            refine ⟨7844520317325365004388609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 669399067078431147041161301 7844520317325365004388609)
            ·
              refine ⟨5883390237994023753291457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844520317325365004388609 5883390237994023753291457)
              ·
                refine ⟨4412542678495517814968593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883390237994023753291457 4412542678495517814968593)
                ·
                  refine ⟨3309407008871638361226445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412542678495517814968593 3309407008871638361226445)
                  ·
                    refine ⟨1241027628326864385459917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309407008871638361226445 1241027628326864385459917)
                    ·
                      rfl

theorem cell22_3625339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].length) (baseStart_3625339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625339 prefixEnd_3625339 := by exact prefixLift 3625339
  have htrace : WordTrace (prefixWord ++ tailWord_3625339) baseStart_3625339 baseEnd_3625339 := by
    simpa [prefixWord, tailWord_3625339, baseEnd_3625339] using wordTrace_append hprefix tailTrace_3625339
  have hstable : (prefixWord ++ tailWord_3625339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625339).length < 2 ^ (prefixWord ++ tailWord_3625339).sum := by decide
  have hdescent : baseEnd_3625339 < baseStart_3625339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625341 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3625341 : Nat := 118140960795 + 3625341 * 2 ^ 59
def prefixEnd_3625341 : Nat := 4983230072969 + 3 ^ 40 * 3625341 * 2
def baseEnd_3625341 : Nat := 413676104322579015636637

theorem tailTrace_3625341 : CollatzResearch.WordTrace tailWord_3625341 prefixEnd_3625341 413676104322579015636637 := by
  unfold tailWord_3625341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132227049159016190794147877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88151366106010793862765251 132227049159016190794147877)
  ·
    refine ⟨24792571717315535773902727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132227049159016190794147877 24792571717315535773902727)
    ·
      refine ⟨37188857575973303660854091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24792571717315535773902727 37188857575973303660854091)
      ·
        refine ⟨55783286363959955491281137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37188857575973303660854091 55783286363959955491281137)
        ·
          refine ⟨41837464772969966618460853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55783286363959955491281137 41837464772969966618460853)
          ·
            refine ⟨3922262322465934370480705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41837464772969966618460853 3922262322465934370480705)
            ·
              refine ⟨2941696741849450777860529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922262322465934370480705 2941696741849450777860529)
              ·
                refine ⟨2206272556387088083395397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941696741849450777860529 2206272556387088083395397)
                ·
                  refine ⟨413676104322579015636637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206272556387088083395397 413676104322579015636637)
                  ·
                    rfl

theorem cell22_3625341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3625341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625341 prefixEnd_3625341 := by exact prefixLift 3625341
  have htrace : WordTrace (prefixWord ++ tailWord_3625341) baseStart_3625341 baseEnd_3625341 := by
    simpa [prefixWord, tailWord_3625341, baseEnd_3625341] using wordTrace_append hprefix tailTrace_3625341
  have hstable : (prefixWord ++ tailWord_3625341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625341).length < 2 ^ (prefixWord ++ tailWord_3625341).sum := by decide
  have hdescent : baseEnd_3625341 < baseStart_3625341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625365 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3625365 : Nat := 118140960795 + 3625365 * 2 ^ 59
def prefixEnd_3625365 : Nat := 4983230072969 + 3 ^ 40 * 3625365 * 2
def baseEnd_3625365 : Nat := 1241036528658208984309837

theorem tailTrace_3625365 : CollatzResearch.WordTrace tailWord_3625365 prefixEnd_3625365 1241036528658208984309837 := by
  unfold tailWord_3625365
  simp only [CollatzResearch.WordTrace]
  refine ⟨132227924510929242893021549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88151949673952828595347699 132227924510929242893021549)
  ·
    refine ⟨49585471691598466084883081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132227924510929242893021549 49585471691598466084883081)
    ·
      refine ⟨37189103768698849563662311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49585471691598466084883081 37189103768698849563662311)
      ·
        refine ⟨55783655653048274345493467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37189103768698849563662311 55783655653048274345493467)
        ·
          refine ⟨83675483479572411518240201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55783655653048274345493467 83675483479572411518240201)
          ·
            refine ⟨62756612609679308638680151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83675483479572411518240201 62756612609679308638680151)
            ·
              refine ⟨94134918914518962958020227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62756612609679308638680151 94134918914518962958020227)
              ·
                refine ⟨141202378371778444437030341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94134918914518962958020227 141202378371778444437030341)
                ·
                  refine ⟨26475445944708458331943189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141202378371778444437030341 26475445944708458331943189)
                  ·
                    refine ⟨1241036528658208984309837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26475445944708458331943189 1241036528658208984309837)
                    ·
                      rfl

theorem cell22_3625365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3625365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625365 prefixEnd_3625365 := by exact prefixLift 3625365
  have htrace : WordTrace (prefixWord ++ tailWord_3625365) baseStart_3625365 baseEnd_3625365 := by
    simpa [prefixWord, tailWord_3625365, baseEnd_3625365] using wordTrace_append hprefix tailTrace_3625365
  have hstable : (prefixWord ++ tailWord_3625365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625365).length < 2 ^ (prefixWord ++ tailWord_3625365).sum := by decide
  have hdescent : baseEnd_3625365 < baseStart_3625365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625367 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 5, 3]
def baseStart_3625367 : Nat := 118140960795 + 3625367 * 2 ^ 59
def prefixEnd_3625367 : Nat := 4983230072969 + 3 ^ 40 * 3625367 * 2
def baseEnd_3625367 : Nat := 1241037213299081645759831

theorem tailTrace_3625367 : CollatzResearch.WordTrace tailWord_3625367 prefixEnd_3625367 1241037213299081645759831 := by
  unfold tailWord_3625367
  simp only [CollatzResearch.WordTrace]
  refine ⟨132227997456921997234594355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88151998304614664823062903 132227997456921997234594355)
  ·
    refine ⟨198341996185382995851891533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132227997456921997234594355 198341996185382995851891533)
    ·
      refine ⟨74378248569518623444459325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198341996185382995851891533 74378248569518623444459325)
      ·
        refine ⟨27891843213569483791672247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74378248569518623444459325 27891843213569483791672247)
        ·
          refine ⟨41837764820354225687508371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27891843213569483791672247 41837764820354225687508371)
          ·
            refine ⟨62756647230531338531262557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41837764820354225687508371 62756647230531338531262557)
            ·
              refine ⟨23533742711449251949223459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62756647230531338531262557 23533742711449251949223459)
              ·
                refine ⟨35300614067173877923835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533742711449251949223459 35300614067173877923835189)
                ·
                  refine ⟨3309432568797551055359549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35300614067173877923835189 3309432568797551055359549)
                  ·
                    refine ⟨1241037213299081645759831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309432568797551055359549 1241037213299081645759831)
                    ·
                      rfl

theorem cell22_3625367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_3625367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625367 prefixEnd_3625367 := by exact prefixLift 3625367
  have htrace : WordTrace (prefixWord ++ tailWord_3625367) baseStart_3625367 baseEnd_3625367 := by
    simpa [prefixWord, tailWord_3625367, baseEnd_3625367] using wordTrace_append hprefix tailTrace_3625367
  have hstable : (prefixWord ++ tailWord_3625367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625367).length < 2 ^ (prefixWord ++ tailWord_3625367).sum := by decide
  have hdescent : baseEnd_3625367 < baseStart_3625367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625386 : List Nat := [3, 1, 6, 1, 1, 1, 9]
def baseStart_3625386 : Nat := 118140960795 + 3625386 * 2 ^ 59
def prefixEnd_3625386 : Nat := 4983230072969 + 3 ^ 40 * 3625386 * 2
def baseEnd_3625386 : Nat := 45964582125458219612399

theorem tailTrace_3625386 : CollatzResearch.WordTrace tailWord_3625386 prefixEnd_3625386 45964582125458219612399 := by
  unfold tailWord_3625386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057172610963290869884003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88152460295902108986357341 33057172610963290869884003)
  ·
    refine ⟨49585758916444936304826005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057172610963290869884003 49585758916444936304826005)
    ·
      refine ⟨2324332449208356389288719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49585758916444936304826005 2324332449208356389288719)
      ·
        refine ⟨3486498673812534583933079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324332449208356389288719 3486498673812534583933079)
        ·
          refine ⟨5229748010718801875899619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486498673812534583933079 5229748010718801875899619)
          ·
            refine ⟨7844622016078202813849429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229748010718801875899619 7844622016078202813849429)
            ·
              refine ⟨45964582125458219612399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7844622016078202813849429 45964582125458219612399)
              ·
                rfl

theorem cell22_3625386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 9].length) (baseStart_3625386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625386 prefixEnd_3625386 := by exact prefixLift 3625386
  have htrace : WordTrace (prefixWord ++ tailWord_3625386) baseStart_3625386 baseEnd_3625386 := by
    simpa [prefixWord, tailWord_3625386, baseEnd_3625386] using wordTrace_append hprefix tailTrace_3625386
  have hstable : (prefixWord ++ tailWord_3625386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625386).length < 2 ^ (prefixWord ++ tailWord_3625386).sum := by decide
  have hdescent : baseEnd_3625386 < baseStart_3625386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625401 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_3625401 : Nat := 118140960795 + 3625401 * 2 ^ 59
def prefixEnd_3625401 : Nat := 4983230072969 + 3 ^ 40 * 3625401 * 2
def baseEnd_3625401 : Nat := 1241048852193916890409727

theorem tailTrace_3625401 : CollatzResearch.WordTrace tailWord_3625401 prefixEnd_3625401 1241048852193916890409727 := by
  unfold tailWord_3625401
  simp only [CollatzResearch.WordTrace]
  refine ⟨132229237538798821041332057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88152825025865880694221371 132229237538798821041332057)
  ·
    refine ⟨99171928154099115780999043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132229237538798821041332057 99171928154099115780999043)
    ·
      refine ⟨148757892231148673671498565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99171928154099115780999043 148757892231148673671498565)
      ·
        refine ⟨27892104793340376313405981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148757892231148673671498565 27892104793340376313405981)
        ·
          refine ⟨10459539297502641117527243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27892104793340376313405981 10459539297502641117527243)
          ·
            refine ⟨15689308946253961676290865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459539297502641117527243 15689308946253961676290865)
            ·
              refine ⟨11766981709690471257218149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15689308946253961676290865 11766981709690471257218149)
              ·
                refine ⟨2206309070566963360728403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11766981709690471257218149 2206309070566963360728403)
                ·
                  refine ⟨3309463605850445041092605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206309070566963360728403 3309463605850445041092605)
                  ·
                    refine ⟨1241048852193916890409727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309463605850445041092605 1241048852193916890409727)
                    ·
                      rfl

theorem cell22_3625401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_3625401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625401 prefixEnd_3625401 := by exact prefixLift 3625401
  have htrace : WordTrace (prefixWord ++ tailWord_3625401) baseStart_3625401 baseEnd_3625401 := by
    simpa [prefixWord, tailWord_3625401, baseEnd_3625401] using wordTrace_append hprefix tailTrace_3625401
  have hstable : (prefixWord ++ tailWord_3625401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625401).length < 2 ^ (prefixWord ++ tailWord_3625401).sum := by decide
  have hdescent : baseEnd_3625401 < baseStart_3625401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625504 : List Nat := [2, 1, 1, 6, 3, 9]
def baseStart_3625504 : Nat := 118140960795 + 3625504 * 2 ^ 59
def prefixEnd_3625504 : Nat := 4983230072969 + 3 ^ 40 * 3625504 * 2
def baseEnd_3625504 : Nat := 15322026064183443889931

theorem tailTrace_3625504 : CollatzResearch.WordTrace tailWord_3625504 prefixEnd_3625504 15322026064183443889931 := by
  unfold tailWord_3625504
  simp only [CollatzResearch.WordTrace]
  refine ⟨66116497128712834816165783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88155329504950446421554377 66116497128712834816165783)
  ·
    refine ⟨99174745693069252224248675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66116497128712834816165783 99174745693069252224248675)
    ·
      refine ⟨148762118539603878336373013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99174745693069252224248675 148762118539603878336373013)
      ·
        refine ⟨6973224306543931797017485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148762118539603878336373013 6973224306543931797017485)
        ·
          refine ⟨2614959114953974423881557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6973224306543931797017485 2614959114953974423881557)
          ·
            refine ⟨15322026064183443889931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2614959114953974423881557 15322026064183443889931)
            ·
              rfl

theorem cell22_3625504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 9].length) (baseStart_3625504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625504 prefixEnd_3625504 := by exact prefixLift 3625504
  have htrace : WordTrace (prefixWord ++ tailWord_3625504) baseStart_3625504 baseEnd_3625504 := by
    simpa [prefixWord, tailWord_3625504, baseEnd_3625504] using wordTrace_append hprefix tailTrace_3625504
  have hstable : (prefixWord ++ tailWord_3625504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625504).length < 2 ^ (prefixWord ++ tailWord_3625504).sum := by decide
  have hdescent : baseEnd_3625504 < baseStart_3625504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625553 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_3625553 : Nat := 118140960795 + 3625553 * 2 ^ 59
def prefixEnd_3625553 : Nat := 4983230072969 + 3 ^ 40 * 3625553 * 2
def baseEnd_3625553 : Nat := 1241100884900239160609261

theorem tailTrace_3625553 : CollatzResearch.WordTrace tailWord_3625553 prefixEnd_3625553 1241100884900239160609261 := by
  unfold tailWord_3625553
  simp only [CollatzResearch.WordTrace]
  refine ⟨132234781434248151000865313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88156520956165434000576875 132234781434248151000865313)
  ·
    refine ⟨99176086075686113250648985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132234781434248151000865313 99176086075686113250648985)
    ·
      refine ⟨74382064556764584937986739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99176086075686113250648985 74382064556764584937986739)
      ·
        refine ⟨111573096835146877406980109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74382064556764584937986739 111573096835146877406980109)
        ·
          refine ⟨41839911313180079027617541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111573096835146877406980109 41839911313180079027617541)
          ·
            refine ⟨7844983371221264817678289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41839911313180079027617541 7844983371221264817678289)
            ·
              refine ⟨5883737528415948613258717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844983371221264817678289 5883737528415948613258717)
              ·
                refine ⟨2206401573155980729972019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5883737528415948613258717 2206401573155980729972019)
                ·
                  refine ⟨3309602359733971094958029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206401573155980729972019 3309602359733971094958029)
                  ·
                    refine ⟨1241100884900239160609261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309602359733971094958029 1241100884900239160609261)
                    ·
                      rfl

theorem cell22_3625553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_3625553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625553 prefixEnd_3625553 := by exact prefixLift 3625553
  have htrace : WordTrace (prefixWord ++ tailWord_3625553) baseStart_3625553 baseEnd_3625553 := by
    simpa [prefixWord, tailWord_3625553, baseEnd_3625553] using wordTrace_append hprefix tailTrace_3625553
  have hstable : (prefixWord ++ tailWord_3625553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625553).length < 2 ^ (prefixWord ++ tailWord_3625553).sum := by decide
  have hdescent : baseEnd_3625553 < baseStart_3625553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625570 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3625570 : Nat := 118140960795 + 3625570 * 2 ^ 59
def prefixEnd_3625570 : Nat := 4983230072969 + 3 ^ 40 * 3625570 * 2
def baseEnd_3625570 : Nat := 1241106704347656782934209

theorem tailTrace_3625570 : CollatzResearch.WordTrace tailWord_3625570 prefixEnd_3625570 1241106704347656782934209 := by
  unfold tailWord_3625570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33058850368796640726058541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88156934316791041936156109 33058850368796640726058541)
  ·
    refine ⟨12397068888298740272271953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33058850368796640726058541 12397068888298740272271953)
    ·
      refine ⟨9297801666224055204203965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12397068888298740272271953 9297801666224055204203965)
      ·
        refine ⟨3486675624834020701576487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9297801666224055204203965 3486675624834020701576487)
        ·
          refine ⟨5230013437251031052364731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486675624834020701576487 5230013437251031052364731)
          ·
            refine ⟨7845020155876546578547097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230013437251031052364731 7845020155876546578547097)
            ·
              refine ⟨5883765116907409933910323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845020155876546578547097 5883765116907409933910323)
              ·
                refine ⟨8825647675361114900865485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883765116907409933910323 8825647675361114900865485)
                ·
                  refine ⟨3309617878260418087824557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8825647675361114900865485 3309617878260418087824557)
                  ·
                    refine ⟨1241106704347656782934209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309617878260418087824557 1241106704347656782934209)
                    ·
                      rfl

theorem cell22_3625570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3625570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625570 prefixEnd_3625570 := by exact prefixLift 3625570
  have htrace : WordTrace (prefixWord ++ tailWord_3625570) baseStart_3625570 baseEnd_3625570 := by
    simpa [prefixWord, tailWord_3625570, baseEnd_3625570] using wordTrace_append hprefix tailTrace_3625570
  have hstable : (prefixWord ++ tailWord_3625570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625570).length < 2 ^ (prefixWord ++ tailWord_3625570).sum := by decide
  have hdescent : baseEnd_3625570 < baseStart_3625570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625677 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3625677 : Nat := 118140960795 + 3625677 * 2 ^ 59
def prefixEnd_3625677 : Nat := 4983230072969 + 3 ^ 40 * 3625677 * 2
def baseEnd_3625677 : Nat := 1241143332634344170508881

theorem tailTrace_3625677 : CollatzResearch.WordTrace tailWord_3625677 prefixEnd_3625677 1241143332634344170508881 := by
  unfold tailWord_3625677
  simp only [CollatzResearch.WordTrace]
  refine ⟨132239304085798920178379285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88159536057199280118919523 132239304085798920178379285)
  ·
    refine ⟨6198717379021824383361529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132239304085798920178379285 6198717379021824383361529)
    ·
      refine ⟨4649038034266368287521147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6198717379021824383361529 4649038034266368287521147)
      ·
        refine ⟨6973557051399552431281721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649038034266368287521147 6973557051399552431281721)
        ·
          refine ⟨5230167788549664323461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973557051399552431281721 5230167788549664323461291)
          ·
            refine ⟨7845251682824496485191937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230167788549664323461291 7845251682824496485191937)
            ·
              refine ⟨5883938762118372363893953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845251682824496485191937 5883938762118372363893953)
              ·
                refine ⟨4412954071588779272920465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883938762118372363893953 4412954071588779272920465)
                ·
                  refine ⟨3309715553691584454690349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412954071588779272920465 3309715553691584454690349)
                  ·
                    refine ⟨1241143332634344170508881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309715553691584454690349 1241143332634344170508881)
                    ·
                      rfl

theorem cell22_3625677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3625677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625677 prefixEnd_3625677 := by exact prefixLift 3625677
  have htrace : WordTrace (prefixWord ++ tailWord_3625677) baseStart_3625677 baseEnd_3625677 := by
    simpa [prefixWord, tailWord_3625677, baseEnd_3625677] using wordTrace_append hprefix tailTrace_3625677
  have hstable : (prefixWord ++ tailWord_3625677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625677).length < 2 ^ (prefixWord ++ tailWord_3625677).sum := by decide
  have hdescent : baseEnd_3625677 < baseStart_3625677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625701 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3625701 : Nat := 118140960795 + 3625701 * 2 ^ 59
def prefixEnd_3625701 : Nat := 4983230072969 + 3 ^ 40 * 3625701 * 2
def baseEnd_3625701 : Nat := 413717182774938702636269

theorem tailTrace_3625701 : CollatzResearch.WordTrace tailWord_3625701 prefixEnd_3625701 413717182774938702636269 := by
  unfold tailWord_3625701
  simp only [CollatzResearch.WordTrace]
  refine ⟨132240179437711972277252957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88160119625141314851501971 132240179437711972277252957)
  ·
    refine ⟨49590067289141989603969859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132240179437711972277252957 49590067289141989603969859)
    ·
      refine ⟨74385100933712984405954789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49590067289141989603969859 74385100933712984405954789)
      ·
        refine ⟨13947206425071184576116523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74385100933712984405954789 13947206425071184576116523)
        ·
          refine ⟨20920809637606776864174785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13947206425071184576116523 20920809637606776864174785)
          ·
            refine ⟨15690607228205082648131089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20920809637606776864174785 15690607228205082648131089)
            ·
              refine ⟨11767955421153811986098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15690607228205082648131089 11767955421153811986098317)
              ·
                refine ⟨4412983282932679494786869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11767955421153811986098317 4412983282932679494786869)
                ·
                  refine ⟨413717182774938702636269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412983282932679494786869 413717182774938702636269)
                  ·
                    rfl

theorem cell22_3625701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3625701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625701 prefixEnd_3625701 := by exact prefixLift 3625701
  have htrace : WordTrace (prefixWord ++ tailWord_3625701) baseStart_3625701 baseEnd_3625701 := by
    simpa [prefixWord, tailWord_3625701, baseEnd_3625701] using wordTrace_append hprefix tailTrace_3625701
  have hstable : (prefixWord ++ tailWord_3625701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625701).length < 2 ^ (prefixWord ++ tailWord_3625701).sum := by decide
  have hdescent : baseEnd_3625701 < baseStart_3625701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625729 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 10]
def baseStart_3625729 : Nat := 118140960795 + 3625729 * 2 ^ 59
def prefixEnd_3625729 : Nat := 4983230072969 + 3 ^ 40 * 3625729 * 2
def baseEnd_3625729 : Nat := 413720377765677789402907

theorem tailTrace_3625729 : CollatzResearch.WordTrace tailWord_3625729 prefixEnd_3625729 413720377765677789402907 := by
  unfold tailWord_3625729
  simp only [CollatzResearch.WordTrace]
  refine ⟨132241200681610533059272241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88160800454407022039514827 132241200681610533059272241)
  ·
    refine ⟨99180900511207899794454181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132241200681610533059272241 99180900511207899794454181)
    ·
      refine ⟨18596418845851481211460159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99180900511207899794454181 18596418845851481211460159)
      ·
        refine ⟨27894628268777221817190239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18596418845851481211460159 27894628268777221817190239)
        ·
          refine ⟨41841942403165832725785359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27894628268777221817190239 41841942403165832725785359)
          ·
            refine ⟨62762913604748749088678039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41841942403165832725785359 62762913604748749088678039)
            ·
              refine ⟨94144370407123123633017059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62762913604748749088678039 94144370407123123633017059)
              ·
                refine ⟨141216555610684685449525589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94144370407123123633017059 141216555610684685449525589)
                ·
                  refine ⟨413720377765677789402907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141216555610684685449525589 413720377765677789402907)
                  ·
                    rfl

theorem cell22_3625729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_3625729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625729 prefixEnd_3625729 := by exact prefixLift 3625729
  have htrace : WordTrace (prefixWord ++ tailWord_3625729) baseStart_3625729 baseEnd_3625729 := by
    simpa [prefixWord, tailWord_3625729, baseEnd_3625729] using wordTrace_append hprefix tailTrace_3625729
  have hstable : (prefixWord ++ tailWord_3625729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625729).length < 2 ^ (prefixWord ++ tailWord_3625729).sum := by decide
  have hdescent : baseEnd_3625729 < baseStart_3625729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625791 : List Nat := [1, 1, 2, 2, 5, 3, 8]
def baseStart_3625791 : Nat := 118140960795 + 3625791 * 2 ^ 59
def prefixEnd_3625791 : Nat := 4983230072969 + 3 ^ 40 * 3625791 * 2
def baseEnd_3625791 : Nat := 45969716932003180487353

theorem tailTrace_3625791 : CollatzResearch.WordTrace tailWord_3625791 prefixEnd_3625791 45969716932003180487353 := by
  unfold tailWord_3625791
  simp only [CollatzResearch.WordTrace]
  refine ⟨132243462007385917648029227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88162308004923945098686151 132243462007385917648029227)
  ·
    refine ⟨198365193011078876472043841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132243462007385917648029227 198365193011078876472043841)
    ·
      refine ⟨148773894758309157354032881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198365193011078876472043841 148773894758309157354032881)
      ·
        refine ⟨111580421068731868015524661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148773894758309157354032881 111580421068731868015524661)
        ·
          refine ⟨10460664475193612626455437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111580421068731868015524661 10460664475193612626455437)
          ·
            refine ⟨3922749178197604734920789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10460664475193612626455437 3922749178197604734920789)
            ·
              refine ⟨45969716932003180487353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3922749178197604734920789 45969716932003180487353)
              ·
                rfl

theorem cell22_3625791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 8].length) (baseStart_3625791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3625791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3625791 prefixEnd_3625791 := by exact prefixLift 3625791
  have htrace : WordTrace (prefixWord ++ tailWord_3625791) baseStart_3625791 baseEnd_3625791 := by
    simpa [prefixWord, tailWord_3625791, baseEnd_3625791] using wordTrace_append hprefix tailTrace_3625791
  have hstable : (prefixWord ++ tailWord_3625791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625791).length < 2 ^ (prefixWord ++ tailWord_3625791).sum := by decide
  have hdescent : baseEnd_3625791 < baseStart_3625791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626033 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 6]
def baseStart_3626033 : Nat := 118140960795 + 3626033 * 2 ^ 59
def prefixEnd_3626033 : Nat := 4983230072969 + 3 ^ 40 * 3626033 * 2
def baseEnd_3626033 : Nat := 413755066236559302869263

theorem tailTrace_3626033 : CollatzResearch.WordTrace tailWord_3626033 prefixEnd_3626033 413755066236559302869263 := by
  unfold tailWord_3626033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252288472509192978338753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88168192315006128652225835 132252288472509192978338753)
  ·
    refine ⟨99189216354381894733754065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132252288472509192978338753 99189216354381894733754065)
    ·
      refine ⟨74391912265786421050315549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99189216354381894733754065 74391912265786421050315549)
      ·
        refine ⟨27896967099669907893868331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74391912265786421050315549 27896967099669907893868331)
        ·
          refine ⟨41845450649504861840802497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27896967099669907893868331 41845450649504861840802497)
          ·
            refine ⟨31384087987128646380601873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41845450649504861840802497 31384087987128646380601873)
            ·
              refine ⟨23538065990346484785451405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31384087987128646380601873 23538065990346484785451405)
              ·
                refine ⟨8826774746379931794544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23538065990346484785451405 8826774746379931794544277)
                ·
                  refine ⟨413755066236559302869263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8826774746379931794544277 413755066236559302869263)
                  ·
                    rfl

theorem cell22_3626033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_3626033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626033 prefixEnd_3626033 := by exact prefixLift 3626033
  have htrace : WordTrace (prefixWord ++ tailWord_3626033) baseStart_3626033 baseEnd_3626033 := by
    simpa [prefixWord, tailWord_3626033, baseEnd_3626033] using wordTrace_append hprefix tailTrace_3626033
  have hstable : (prefixWord ++ tailWord_3626033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626033).length < 2 ^ (prefixWord ++ tailWord_3626033).sum := by decide
  have hdescent : baseEnd_3626033 < baseStart_3626033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626140 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3626140 : Nat := 118140960795 + 3626140 * 2 ^ 59
def prefixEnd_3626140 : Nat := 4983230072969 + 3 ^ 40 * 3626140 * 2
def baseEnd_3626140 : Nat := 413767275665455098727487

theorem tailTrace_3626140 : CollatzResearch.WordTrace tailWord_3626140 prefixEnd_3626140 413767275665455098727487 := by
  unfold tailWord_3626140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66128095541560775126241937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88170794055414366834989249 66128095541560775126241937)
  ·
    refine ⟨49596071656170581344681453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66128095541560775126241937 49596071656170581344681453)
    ·
      refine ⟨18598526871063968004255545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49596071656170581344681453 18598526871063968004255545)
      ·
        refine ⟨13948895153297976003191659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18598526871063968004255545 13948895153297976003191659)
        ·
          refine ⟨20923342729946964004787489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13948895153297976003191659 20923342729946964004787489)
          ·
            refine ⟨15692507047460223003590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20923342729946964004787489 15692507047460223003590617)
            ·
              refine ⟨11769380285595167252692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15692507047460223003590617 11769380285595167252692963)
              ·
                refine ⟨17654070428392750879039445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769380285595167252692963 17654070428392750879039445)
                ·
                  refine ⟨413767275665455098727487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17654070428392750879039445 413767275665455098727487)
                  ·
                    rfl

theorem cell22_3626140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3626140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626140 prefixEnd_3626140 := by exact prefixLift 3626140
  have htrace : WordTrace (prefixWord ++ tailWord_3626140) baseStart_3626140 baseEnd_3626140 := by
    simpa [prefixWord, tailWord_3626140, baseEnd_3626140] using wordTrace_append hprefix tailTrace_3626140
  have hstable : (prefixWord ++ tailWord_3626140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626140).length < 2 ^ (prefixWord ++ tailWord_3626140).sum := by decide
  have hdescent : baseEnd_3626140 < baseStart_3626140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626292 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3626292 : Nat := 118140960795 + 3626292 * 2 ^ 59
def prefixEnd_3626292 : Nat := 4983230072969 + 3 ^ 40 * 3626292 * 2
def baseEnd_3626292 : Nat := 413784619900895855460665

theorem tailTrace_3626292 : CollatzResearch.WordTrace tailWord_3626292 prefixEnd_3626292 413784619900895855460665 := by
  unfold tailWord_3626292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66130867489285440106008565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88174489985713920141344753 66130867489285440106008565)
  ·
    refine ⟨6199768827120510009938303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66130867489285440106008565 6199768827120510009938303)
    ·
      refine ⟨9299653240680765014907455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199768827120510009938303 9299653240680765014907455)
      ·
        refine ⟨13949479861021147522361183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9299653240680765014907455 13949479861021147522361183)
        ·
          refine ⟨20924219791531721283541775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13949479861021147522361183 20924219791531721283541775)
          ·
            refine ⟨31386329687297581925312663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20924219791531721283541775 31386329687297581925312663)
            ·
              refine ⟨47079494530946372887968995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31386329687297581925312663 47079494530946372887968995)
              ·
                refine ⟨70619241796419559331953493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47079494530946372887968995 70619241796419559331953493)
                ·
                  refine ⟨413784619900895855460665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70619241796419559331953493 413784619900895855460665)
                  ·
                    rfl

theorem cell22_3626292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3626292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626292 prefixEnd_3626292 := by exact prefixLift 3626292
  have htrace : WordTrace (prefixWord ++ tailWord_3626292) baseStart_3626292 baseEnd_3626292 := by
    simpa [prefixWord, tailWord_3626292, baseEnd_3626292] using wordTrace_append hprefix tailTrace_3626292
  have hstable : (prefixWord ++ tailWord_3626292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626292).length < 2 ^ (prefixWord ++ tailWord_3626292).sum := by decide
  have hdescent : baseEnd_3626292 < baseStart_3626292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626322 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3626322 : Nat := 118140960795 + 3626322 * 2 ^ 59
def prefixEnd_3626322 : Nat := 4983230072969 + 3 ^ 40 * 3626322 * 2
def baseEnd_3626322 : Nat := 1241364129315777488131903

theorem tailTrace_3626322 : CollatzResearch.WordTrace tailWord_3626322 prefixEnd_3626322 1241364129315777488131903 := by
  unfold tailWord_3626322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33065707292115548833902305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88175219445641463557072813 33065707292115548833902305)
  ·
    refine ⟨24799280469086661625426729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33065707292115548833902305 24799280469086661625426729)
    ·
      refine ⟨18599460351814996219070047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24799280469086661625426729 18599460351814996219070047)
      ·
        refine ⟨27899190527722494328605071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18599460351814996219070047 27899190527722494328605071)
        ·
          refine ⟨41848785791583741492907607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899190527722494328605071 41848785791583741492907607)
          ·
            refine ⟨62773178687375612239361411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41848785791583741492907607 62773178687375612239361411)
            ·
              refine ⟨94159768031063418359042117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62773178687375612239361411 94159768031063418359042117)
              ·
                refine ⟨17654956505824390942320397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94159768031063418359042117 17654956505824390942320397)
                ·
                  refine ⟨6620608689684146603370149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17654956505824390942320397 6620608689684146603370149)
                  ·
                    refine ⟨1241364129315777488131903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620608689684146603370149 1241364129315777488131903)
                    ·
                      rfl

theorem cell22_3626322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3626322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626322 prefixEnd_3626322 := by exact prefixLift 3626322
  have htrace : WordTrace (prefixWord ++ tailWord_3626322) baseStart_3626322 baseEnd_3626322 := by
    simpa [prefixWord, tailWord_3626322, baseEnd_3626322] using wordTrace_append hprefix tailTrace_3626322
  have hstable : (prefixWord ++ tailWord_3626322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626322).length < 2 ^ (prefixWord ++ tailWord_3626322).sum := by decide
  have hdescent : baseEnd_3626322 < baseStart_3626322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626339 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 1, 4]
def baseStart_3626339 : Nat := 118140960795 + 3626339 * 2 ^ 59
def prefixEnd_3626339 : Nat := 4983230072969 + 3 ^ 40 * 3626339 * 2
def baseEnd_3626339 : Nat := 1241369948763195110456851

theorem tailTrace_3626339 : CollatzResearch.WordTrace tailWord_3626339 prefixEnd_3626339 1241369948763195110456851 := by
  unfold tailWord_3626339
  simp only [CollatzResearch.WordTrace]
  refine ⟨132263449209400607238978071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88175632806267071492652047 132263449209400607238978071)
  ·
    refine ⟨198395173814100910858467107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132263449209400607238978071 198395173814100910858467107)
    ·
      refine ⟨297592760721151366287700661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198395173814100910858467107 297592760721151366287700661)
      ·
        refine ⟨27899321317607940589471937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297592760721151366287700661 27899321317607940589471937)
        ·
          refine ⟨20924490988205955442103953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27899321317607940589471937 20924490988205955442103953)
          ·
            refine ⟨15693368241154466581577965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20924490988205955442103953 15693368241154466581577965)
            ·
              refine ⟨5885013090432924968091737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15693368241154466581577965 5885013090432924968091737)
              ·
                refine ⟨4413759817824693726068803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885013090432924968091737 4413759817824693726068803)
                ·
                  refine ⟨6620639726737040589103205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413759817824693726068803 6620639726737040589103205)
                  ·
                    refine ⟨1241369948763195110456851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620639726737040589103205 1241369948763195110456851)
                    ·
                      rfl

theorem cell22_3626339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_3626339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626339 prefixEnd_3626339 := by exact prefixLift 3626339
  have htrace : WordTrace (prefixWord ++ tailWord_3626339) baseStart_3626339 baseEnd_3626339 := by
    simpa [prefixWord, tailWord_3626339, baseEnd_3626339] using wordTrace_append hprefix tailTrace_3626339
  have hstable : (prefixWord ++ tailWord_3626339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626339).length < 2 ^ (prefixWord ++ tailWord_3626339).sum := by decide
  have hdescent : baseEnd_3626339 < baseStart_3626339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626352 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_3626352 : Nat := 118140960795 + 3626352 * 2 ^ 59
def prefixEnd_3626352 : Nat := 4983230072969 + 3 ^ 40 * 3626352 * 2
def baseEnd_3626352 : Nat := 1241374398928867409881811

theorem tailTrace_3626352 : CollatzResearch.WordTrace tailWord_3626352 prefixEnd_3626352 1241374398928867409881811 := by
  unfold tailWord_3626352
  simp only [CollatzResearch.WordTrace]
  refine ⟨66131961679176755229600655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88175948905569006972800873 66131961679176755229600655)
  ·
    refine ⟨99197942518765132844400983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66131961679176755229600655 99197942518765132844400983)
    ·
      refine ⟨148796913778147699266601475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99197942518765132844400983 148796913778147699266601475)
      ·
        refine ⟨223195370667221548899902213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148796913778147699266601475 223195370667221548899902213)
        ·
          refine ⟨41849132000104040418731665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223195370667221548899902213 41849132000104040418731665)
          ·
            refine ⟨31386849000078030314048749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41849132000104040418731665 31386849000078030314048749)
            ·
              refine ⟨11770068375029261367768281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31386849000078030314048749 11770068375029261367768281)
              ·
                refine ⟨8827551281271946025826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11770068375029261367768281 8827551281271946025826211)
                ·
                  refine ⟨13241326921907919038739317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827551281271946025826211 13241326921907919038739317)
                  ·
                    refine ⟨1241374398928867409881811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13241326921907919038739317 1241374398928867409881811)
                    ·
                      rfl

theorem cell22_3626352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_3626352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626352 prefixEnd_3626352 := by exact prefixLift 3626352
  have htrace : WordTrace (prefixWord ++ tailWord_3626352) baseStart_3626352 baseEnd_3626352 := by
    simpa [prefixWord, tailWord_3626352, baseEnd_3626352] using wordTrace_append hprefix tailTrace_3626352
  have hstable : (prefixWord ++ tailWord_3626352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626352).length < 2 ^ (prefixWord ++ tailWord_3626352).sum := by decide
  have hdescent : baseEnd_3626352 < baseStart_3626352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626354 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_3626354 : Nat := 118140960795 + 3626354 * 2 ^ 59
def prefixEnd_3626354 : Nat := 4983230072969 + 3 ^ 40 * 3626354 * 2
def baseEnd_3626354 : Nat := 413791694523246690443935

theorem tailTrace_3626354 : CollatzResearch.WordTrace tailWord_3626354 prefixEnd_3626354 413791694523246690443935 := by
  unfold tailWord_3626354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33065999076086566200193529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88175997536230843200516077 33065999076086566200193529)
  ·
    refine ⟨24799499307064924650145147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33065999076086566200193529 24799499307064924650145147)
    ·
      refine ⟨37199248960597386975217721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24799499307064924650145147 37199248960597386975217721)
      ·
        refine ⟨27899436720448040231413291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37199248960597386975217721 27899436720448040231413291)
        ·
          refine ⟨41849155080672060347119937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899436720448040231413291 41849155080672060347119937)
          ·
            refine ⟨31386866310504045260339953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41849155080672060347119937 31386866310504045260339953)
            ·
              refine ⟨23540149732878033945254965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31386866310504045260339953 23540149732878033945254965)
              ·
                refine ⟨2206889037457315682367653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23540149732878033945254965 2206889037457315682367653)
                ·
                  refine ⟨413791694523246690443935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206889037457315682367653 413791694523246690443935)
                  ·
                    rfl

theorem cell22_3626354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_3626354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626354 prefixEnd_3626354 := by exact prefixLift 3626354
  have htrace : WordTrace (prefixWord ++ tailWord_3626354) baseStart_3626354 baseEnd_3626354 := by
    simpa [prefixWord, tailWord_3626354, baseEnd_3626354] using wordTrace_append hprefix tailTrace_3626354
  have hstable : (prefixWord ++ tailWord_3626354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626354).length < 2 ^ (prefixWord ++ tailWord_3626354).sum := by decide
  have hdescent : baseEnd_3626354 < baseStart_3626354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626371 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 4]
def baseStart_3626371 : Nat := 118140960795 + 3626371 * 2 ^ 59
def prefixEnd_3626371 : Nat := 4983230072969 + 3 ^ 40 * 3626371 * 2
def baseEnd_3626371 : Nat := 413793634339052564552251

theorem tailTrace_3626371 : CollatzResearch.WordTrace tailWord_3626371 prefixEnd_3626371 413793634339052564552251 := by
  unfold tailWord_3626371
  simp only [CollatzResearch.WordTrace]
  refine ⟨132264616345284676704142967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88176410896856451136095311 132264616345284676704142967)
  ·
    refine ⟨198396924517927015056214451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132264616345284676704142967 198396924517927015056214451)
    ·
      refine ⟨297595386776890522584321677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198396924517927015056214451 297595386776890522584321677)
      ·
        refine ⟨111598270041333945969120629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297595386776890522584321677 111598270041333945969120629)
        ·
          refine ⟨10462337816375057434605059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111598270041333945969120629 10462337816375057434605059)
          ·
            refine ⟨15693506724562586151907589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462337816375057434605059 15693506724562586151907589)
            ·
              refine ⟨2942532510855484903482673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15693506724562586151907589 2942532510855484903482673)
              ·
                refine ⟨2206899383141613677612005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942532510855484903482673 2206899383141613677612005)
                ·
                  refine ⟨413793634339052564552251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206899383141613677612005 413793634339052564552251)
                  ·
                    rfl

theorem cell22_3626371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 4].length) (baseStart_3626371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626371 prefixEnd_3626371 := by exact prefixLift 3626371
  have htrace : WordTrace (prefixWord ++ tailWord_3626371) baseStart_3626371 baseEnd_3626371 := by
    simpa [prefixWord, tailWord_3626371, baseEnd_3626371] using wordTrace_append hprefix tailTrace_3626371
  have hstable : (prefixWord ++ tailWord_3626371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626371).length < 2 ^ (prefixWord ++ tailWord_3626371).sum := by decide
  have hdescent : baseEnd_3626371 < baseStart_3626371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626399 : List Nat := [1, 1, 2, 5, 1, 3, 3, 6]
def baseStart_3626399 : Nat := 118140960795 + 3626399 * 2 ^ 59
def prefixEnd_3626399 : Nat := 4983230072969 + 3 ^ 40 * 3626399 * 2
def baseEnd_3626399 : Nat := 137932276443263883772963

theorem tailTrace_3626399 : CollatzResearch.WordTrace tailWord_3626399 prefixEnd_3626399 137932276443263883772963 := by
  unfold tailWord_3626399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132265637589183237486162251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88177091726122158324108167 132265637589183237486162251)
  ·
    refine ⟨198398456383774856229243377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132265637589183237486162251 198398456383774856229243377)
    ·
      refine ⟨148798842287831142171932533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198398456383774856229243377 148798842287831142171932533)
      ·
        refine ⟨13949891464484169578618675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148798842287831142171932533 13949891464484169578618675)
        ·
          refine ⟨20924837196726254367928013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13949891464484169578618675 20924837196726254367928013)
          ·
            refine ⟨7846813948772345387973005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20924837196726254367928013 7846813948772345387973005)
            ·
              refine ⟨2942555230789629520489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7846813948772345387973005 2942555230789629520489877)
              ·
                refine ⟨137932276443263883772963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2942555230789629520489877 137932276443263883772963)
                ·
                  rfl

theorem cell22_3626399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 6].length) (baseStart_3626399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626399 prefixEnd_3626399 := by exact prefixLift 3626399
  have htrace : WordTrace (prefixWord ++ tailWord_3626399) baseStart_3626399 baseEnd_3626399 := by
    simpa [prefixWord, tailWord_3626399, baseEnd_3626399] using wordTrace_append hprefix tailTrace_3626399
  have hstable : (prefixWord ++ tailWord_3626399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626399).length < 2 ^ (prefixWord ++ tailWord_3626399).sum := by decide
  have hdescent : baseEnd_3626399 < baseStart_3626399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626487 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3626487 : Nat := 118140960795 + 3626487 * 2 ^ 59
def prefixEnd_3626487 : Nat := 4983230072969 + 3 ^ 40 * 3626487 * 2
def baseEnd_3626487 : Nat := 1241420612187772057756397

theorem tailTrace_3626487 : CollatzResearch.WordTrace tailWord_3626487 prefixEnd_3626487 1241420612187772057756397 := by
  unfold tailWord_3626487
  simp only [CollatzResearch.WordTrace]
  refine ⟨132268847212864428515365715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88179231475242952343577143 132268847212864428515365715)
  ·
    refine ⟨198403270819296642773048573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132268847212864428515365715 198403270819296642773048573)
    ·
      refine ⟨74401226557236241039893215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198403270819296642773048573 74401226557236241039893215)
      ·
        refine ⟨111601839835854361559839823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74401226557236241039893215 111601839835854361559839823)
        ·
          refine ⟨167402759753781542339759735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111601839835854361559839823 167402759753781542339759735)
          ·
            refine ⟨251104139630672313509639603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167402759753781542339759735 251104139630672313509639603)
            ·
              refine ⟨376656209446008470264459405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251104139630672313509639603 376656209446008470264459405)
              ·
                refine ⟨141246078542253176349172277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376656209446008470264459405 141246078542253176349172277)
                ·
                  refine ⟨13241819863336235282734901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141246078542253176349172277 13241819863336235282734901)
                  ·
                    refine ⟨1241420612187772057756397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13241819863336235282734901 1241420612187772057756397)
                    ·
                      rfl

theorem cell22_3626487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3626487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626487 prefixEnd_3626487 := by exact prefixLift 3626487
  have htrace : WordTrace (prefixWord ++ tailWord_3626487) baseStart_3626487 baseEnd_3626487 := by
    simpa [prefixWord, tailWord_3626487, baseEnd_3626487] using wordTrace_append hprefix tailTrace_3626487
  have hstable : (prefixWord ++ tailWord_3626487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626487).length < 2 ^ (prefixWord ++ tailWord_3626487).sum := by decide
  have hdescent : baseEnd_3626487 < baseStart_3626487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626508 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_3626508 : Nat := 118140960795 + 3626508 * 2 ^ 59
def prefixEnd_3626508 : Nat := 4983230072969 + 3 ^ 40 * 3626508 * 2
def baseEnd_3626508 : Nat := 1241427800916935002981333

theorem tailTrace_3626508 : CollatzResearch.WordTrace tailWord_3626508 prefixEnd_3626508 1241427800916935002981333 := by
  unfold tailWord_3626508
  simp only [CollatzResearch.WordTrace]
  refine ⟨66134806572894174550940089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88179742097192232734586785 66134806572894174550940089)
  ·
    refine ⟨49601104929670630913205067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66134806572894174550940089 49601104929670630913205067)
    ·
      refine ⟨74401657394505946369807601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49601104929670630913205067 74401657394505946369807601)
      ·
        refine ⟨55801243045879459777355701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74401657394505946369807601 55801243045879459777355701)
        ·
          refine ⟨5231366535551199354127097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55801243045879459777355701 5231366535551199354127097)
          ·
            refine ⟨3923524901663399515595323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231366535551199354127097 3923524901663399515595323)
            ·
              refine ⟨5885287352495099273392985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923524901663399515595323 5885287352495099273392985)
              ·
                refine ⟨4413965514371324455044739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885287352495099273392985 4413965514371324455044739)
                ·
                  refine ⟨6620948271556986682567109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413965514371324455044739 6620948271556986682567109)
                  ·
                    refine ⟨1241427800916935002981333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620948271556986682567109 1241427800916935002981333)
                    ·
                      rfl

theorem cell22_3626508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_3626508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626508 prefixEnd_3626508 := by exact prefixLift 3626508
  have htrace : WordTrace (prefixWord ++ tailWord_3626508) baseStart_3626508 baseEnd_3626508 := by
    simpa [prefixWord, tailWord_3626508, baseEnd_3626508] using wordTrace_append hprefix tailTrace_3626508
  have hstable : (prefixWord ++ tailWord_3626508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626508).length < 2 ^ (prefixWord ++ tailWord_3626508).sum := by decide
  have hdescent : baseEnd_3626508 < baseStart_3626508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626538 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3626538 : Nat := 118140960795 + 3626538 * 2 ^ 59
def prefixEnd_3626538 : Nat := 4983230072969 + 3 ^ 40 * 3626538 * 2
def baseEnd_3626538 : Nat := 1241438070530024924731241

theorem tailTrace_3626538 : CollatzResearch.WordTrace tailWord_3626538 prefixEnd_3626538 1241438070530024924731241 := by
  unfold tailWord_3626538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067676833919916056368067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88180471557119776150314845 33067676833919916056368067)
  ·
    refine ⟨49601515250879874084552101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33067676833919916056368067 49601515250879874084552101)
    ·
      refine ⟨9300284109539976390853519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49601515250879874084552101 9300284109539976390853519)
      ·
        refine ⟨13950426164309964586280279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300284109539976390853519 13950426164309964586280279)
        ·
          refine ⟨20925639246464946879420419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950426164309964586280279 20925639246464946879420419)
          ·
            refine ⟨31388458869697420319130629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20925639246464946879420419 31388458869697420319130629)
            ·
              refine ⟨5885336038068266309836993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31388458869697420319130629 5885336038068266309836993)
              ·
                refine ⟨4414002028551199732377745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885336038068266309836993 4414002028551199732377745)
                ·
                  refine ⟨3310501521413399799283309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414002028551199732377745 3310501521413399799283309)
                  ·
                    refine ⟨1241438070530024924731241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310501521413399799283309 1241438070530024924731241)
                    ·
                      rfl

theorem cell22_3626538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3626538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626538 prefixEnd_3626538 := by exact prefixLift 3626538
  have htrace : WordTrace (prefixWord ++ tailWord_3626538) baseStart_3626538 baseEnd_3626538 := by
    simpa [prefixWord, tailWord_3626538, baseEnd_3626538] using wordTrace_append hprefix tailTrace_3626538
  have hstable : (prefixWord ++ tailWord_3626538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626538).length < 2 ^ (prefixWord ++ tailWord_3626538).sum := by decide
  have hdescent : baseEnd_3626538 < baseStart_3626538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626583 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 1, 3]
def baseStart_3626583 : Nat := 118140960795 + 3626583 * 2 ^ 59
def prefixEnd_3626583 : Nat := 4983230072969 + 3 ^ 40 * 3626583 * 2
def baseEnd_3626583 : Nat := 1241453474949659807356103

theorem tailTrace_3626583 : CollatzResearch.WordTrace tailWord_3626583 prefixEnd_3626583 1241453474949659807356103 := by
  unfold tailWord_3626583
  simp only [CollatzResearch.WordTrace]
  refine ⟨132272348620516636910860403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88181565747011091273906935 132272348620516636910860403)
  ·
    refine ⟨198408522930774955366290605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132272348620516636910860403 198408522930774955366290605)
    ·
      refine ⟨74403196099040608262358977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198408522930774955366290605 74403196099040608262358977)
      ·
        refine ⟨55802397074280456196769233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74403196099040608262358977 55802397074280456196769233)
        ·
          refine ⟨41851797805710342147576925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55802397074280456196769233 41851797805710342147576925)
          ·
            refine ⟨15694424177141378305341347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41851797805710342147576925 15694424177141378305341347)
            ·
              refine ⟨23541636265712067458012021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15694424177141378305341347 23541636265712067458012021)
              ·
                refine ⟨2207028399910506324188627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23541636265712067458012021 2207028399910506324188627)
                ·
                  refine ⟨3310542599865759486282941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207028399910506324188627 3310542599865759486282941)
                  ·
                    refine ⟨1241453474949659807356103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310542599865759486282941 1241453474949659807356103)
                    ·
                      rfl

theorem cell22_3626583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_3626583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626583 prefixEnd_3626583 := by exact prefixLift 3626583
  have htrace : WordTrace (prefixWord ++ tailWord_3626583) baseStart_3626583 baseEnd_3626583 := by
    simpa [prefixWord, tailWord_3626583, baseEnd_3626583] using wordTrace_append hprefix tailTrace_3626583
  have hstable : (prefixWord ++ tailWord_3626583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626583).length < 2 ^ (prefixWord ++ tailWord_3626583).sum := by decide
  have hdescent : baseEnd_3626583 < baseStart_3626583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626589 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3626589 : Nat := 118140960795 + 3626589 * 2 ^ 59
def prefixEnd_3626589 : Nat := 4983230072969 + 3 ^ 40 * 3626589 * 2
def baseEnd_3626589 : Nat := 1241455528872277791706085

theorem tailTrace_3626589 : CollatzResearch.WordTrace tailWord_3626589 prefixEnd_3626589 1241455528872277791706085 := by
  unfold tailWord_3626589
  simp only [CollatzResearch.WordTrace]
  refine ⟨132272567458494899935578821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88181711638996599957052547 132272567458494899935578821)
  ·
    refine ⟨24801106398467793737921029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132272567458494899935578821 24801106398467793737921029)
    ·
      refine ⟨4650207449712711325860193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24801106398467793737921029 4650207449712711325860193)
      ·
        refine ⟨3487655587284533494395145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650207449712711325860193 3487655587284533494395145)
        ·
          refine ⟨2615741690463400120796359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3487655587284533494395145 2615741690463400120796359)
          ·
            refine ⟨3923612535695100181194539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615741690463400120796359 3923612535695100181194539)
            ·
              refine ⟨5885418803542650271791809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923612535695100181194539 5885418803542650271791809)
              ·
                refine ⟨4414064102656987703843857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885418803542650271791809 4414064102656987703843857)
                ·
                  refine ⟨3310548076992740777882893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414064102656987703843857 3310548076992740777882893)
                  ·
                    refine ⟨1241455528872277791706085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310548076992740777882893 1241455528872277791706085)
                    ·
                      rfl

theorem cell22_3626589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3626589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626589 prefixEnd_3626589 := by exact prefixLift 3626589
  have htrace : WordTrace (prefixWord ++ tailWord_3626589) baseStart_3626589 baseEnd_3626589 := by
    simpa [prefixWord, tailWord_3626589, baseEnd_3626589] using wordTrace_append hprefix tailTrace_3626589
  have hstable : (prefixWord ++ tailWord_3626589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626589).length < 2 ^ (prefixWord ++ tailWord_3626589).sum := by decide
  have hdescent : baseEnd_3626589 < baseStart_3626589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626596 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3626596 : Nat := 118140960795 + 3626596 * 2 ^ 59
def prefixEnd_3626596 : Nat := 4983230072969 + 3 ^ 40 * 3626596 * 2
def baseEnd_3626596 : Nat := 413819308371777368927021

theorem tailTrace_3626596 : CollatzResearch.WordTrace tailWord_3626596 prefixEnd_3626596 413819308371777368927021 := by
  unfold tailWord_3626596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66136411384734770065541821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88181881846313026754055761 66136411384734770065541821)
  ·
    refine ⟨24801154269275538774578183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66136411384734770065541821 24801154269275538774578183)
    ·
      refine ⟨37201731403913308161867275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24801154269275538774578183 37201731403913308161867275)
      ·
        refine ⟨55802597105869962242800913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37201731403913308161867275 55802597105869962242800913)
        ·
          refine ⟨41851947829402471682100685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55802597105869962242800913 41851947829402471682100685)
          ·
            refine ⟨15694480436025926880787757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41851947829402471682100685 15694480436025926880787757)
            ·
              refine ⟨5885430163509722580295409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15694480436025926880787757 5885430163509722580295409)
              ·
                refine ⟨4414072622632291935221557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885430163509722580295409 4414072622632291935221557)
                ·
                  refine ⟨413819308371777368927021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414072622632291935221557 413819308371777368927021)
                  ·
                    rfl

theorem cell22_3626596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3626596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626596 prefixEnd_3626596 := by exact prefixLift 3626596
  have htrace : WordTrace (prefixWord ++ tailWord_3626596) baseStart_3626596 baseEnd_3626596 := by
    simpa [prefixWord, tailWord_3626596, baseEnd_3626596] using wordTrace_append hprefix tailTrace_3626596
  have hstable : (prefixWord ++ tailWord_3626596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626596).length < 2 ^ (prefixWord ++ tailWord_3626596).sum := by decide
  have hdescent : baseEnd_3626596 < baseStart_3626596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626600 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3626600 : Nat := 118140960795 + 3626600 * 2 ^ 59
def prefixEnd_3626600 : Nat := 4983230072969 + 3 ^ 40 * 3626600 * 2
def baseEnd_3626600 : Nat := 1241459294397077429681051

theorem tailTrace_3626600 : CollatzResearch.WordTrace tailWord_3626600 prefixEnd_3626600 1241459294397077429681051 := by
  unfold tailWord_3626600
  simp only [CollatzResearch.WordTrace]
  refine ⟨66136484330727524407114627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88181979107636699209486169 66136484330727524407114627)
  ·
    refine ⟨99204726496091286610671941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66136484330727524407114627 99204726496091286610671941)
    ·
      refine ⟨18600886218017116239500989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99204726496091286610671941 18600886218017116239500989)
      ·
        refine ⟨6975332331756418589812871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18600886218017116239500989 6975332331756418589812871)
        ·
          refine ⟨10462998497634627884719307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6975332331756418589812871 10462998497634627884719307)
          ·
            refine ⟨15694497746451941827078961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462998497634627884719307 15694497746451941827078961)
            ·
              refine ⟨11770873309838956370309221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15694497746451941827078961 11770873309838956370309221)
              ·
                refine ⟨2207038745594804319432979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11770873309838956370309221 2207038745594804319432979)
                ·
                  refine ⟨3310558118392206479149469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207038745594804319432979 3310558118392206479149469)
                  ·
                    refine ⟨1241459294397077429681051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310558118392206479149469 1241459294397077429681051)
                    ·
                      rfl

theorem cell22_3626600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3626600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626600 prefixEnd_3626600 := by exact prefixLift 3626600
  have htrace : WordTrace (prefixWord ++ tailWord_3626600) baseStart_3626600 baseEnd_3626600 := by
    simpa [prefixWord, tailWord_3626600, baseEnd_3626600] using wordTrace_append hprefix tailTrace_3626600
  have hstable : (prefixWord ++ tailWord_3626600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626600).length < 2 ^ (prefixWord ++ tailWord_3626600).sum := by decide
  have hdescent : baseEnd_3626600 < baseStart_3626600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3626609 : Nat := 118140960795 + 3626609 * 2 ^ 59
def prefixEnd_3626609 : Nat := 4983230072969 + 3 ^ 40 * 3626609 * 2
def baseEnd_3626609 : Nat := 1241462375281004406206023

theorem tailTrace_3626609 : CollatzResearch.WordTrace tailWord_3626609 prefixEnd_3626609 1241462375281004406206023 := by
  unfold tailWord_3626609
  simp only [CollatzResearch.WordTrace]
  refine ⟨132273296918422443351306881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88182197945614962234204587 132273296918422443351306881)
  ·
    refine ⟨99204972688816832513480161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132273296918422443351306881 99204972688816832513480161)
    ·
      refine ⟨74403729516612624385110121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99204972688816832513480161 74403729516612624385110121)
      ·
        refine ⟨55802797137459468288832591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74403729516612624385110121 55802797137459468288832591)
        ·
          refine ⟨83704195706189202433248887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55802797137459468288832591 83704195706189202433248887)
          ·
            refine ⟨125556293559283803649873331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83704195706189202433248887 125556293559283803649873331)
            ·
              refine ⟨188334440338925705474809997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125556293559283803649873331 188334440338925705474809997)
              ·
                refine ⟨70625415127097139553053749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188334440338925705474809997 70625415127097139553053749)
                ·
                  refine ⟨6621132668165356833098789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70625415127097139553053749 6621132668165356833098789)
                  ·
                    refine ⟨1241462375281004406206023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621132668165356833098789 1241462375281004406206023)
                    ·
                      rfl

theorem cell22_3626609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3626609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626609 prefixEnd_3626609 := by exact prefixLift 3626609
  have htrace : WordTrace (prefixWord ++ tailWord_3626609) baseStart_3626609 baseEnd_3626609 := by
    simpa [prefixWord, tailWord_3626609, baseEnd_3626609] using wordTrace_append hprefix tailTrace_3626609
  have hstable : (prefixWord ++ tailWord_3626609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626609).length < 2 ^ (prefixWord ++ tailWord_3626609).sum := by decide
  have hdescent : baseEnd_3626609 < baseStart_3626609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626624 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_3626624 : Nat := 118140960795 + 3626624 * 2 ^ 59
def prefixEnd_3626624 : Nat := 4983230072969 + 3 ^ 40 * 3626624 * 2
def baseEnd_3626624 : Nat := 413822503362516455693659

theorem tailTrace_3626624 : CollatzResearch.WordTrace tailWord_3626624 prefixEnd_3626624 413822503362516455693659 := by
  unfold tailWord_3626624
  simp only [CollatzResearch.WordTrace]
  refine ⟨66136922006684050456551463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88182562675578733942068617 66136922006684050456551463)
  ·
    refine ⟨99205383010026075684827195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66136922006684050456551463 99205383010026075684827195)
    ·
      refine ⟨148808074515039113527240793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99205383010026075684827195 148808074515039113527240793)
      ·
        refine ⟨111606055886279335145430595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148808074515039113527240793 111606055886279335145430595)
        ·
          refine ⟨167409083829419002718145893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111606055886279335145430595 167409083829419002718145893)
          ·
            refine ⟨31389203218016063009652355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167409083829419002718145893 31389203218016063009652355)
            ·
              refine ⟨47083804827024094514478533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31389203218016063009652355 47083804827024094514478533)
              ·
                refine ⟨8828213405067017721464725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47083804827024094514478533 8828213405067017721464725)
                ·
                  refine ⟨413822503362516455693659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8828213405067017721464725 413822503362516455693659)
                  ·
                    rfl

theorem cell22_3626624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_3626624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626624 prefixEnd_3626624 := by exact prefixLift 3626624
  have htrace : WordTrace (prefixWord ++ tailWord_3626624) baseStart_3626624 baseEnd_3626624 := by
    simpa [prefixWord, tailWord_3626624, baseEnd_3626624] using wordTrace_append hprefix tailTrace_3626624
  have hstable : (prefixWord ++ tailWord_3626624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626624).length < 2 ^ (prefixWord ++ tailWord_3626624).sum := by decide
  have hdescent : baseEnd_3626624 < baseStart_3626624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 4]
def baseStart_3626641 : Nat := 118140960795 + 3626641 * 2 ^ 59
def prefixEnd_3626641 : Nat := 4983230072969 + 3 ^ 40 * 3626641 * 2
def baseEnd_3626641 : Nat := 413824443178322329801975

theorem tailTrace_3626641 : CollatzResearch.WordTrace tailWord_3626641 prefixEnd_3626641 413824443178322329801975 := by
  unfold tailWord_3626641
  simp only [CollatzResearch.WordTrace]
  refine ⟨132274464054306512816471777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88182976036204341877647851 132274464054306512816471777)
  ·
    refine ⟨99205848040729884612353833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132274464054306512816471777 99205848040729884612353833)
    ·
      refine ⟨74404386030547413459265375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99205848040729884612353833 74404386030547413459265375)
      ·
        refine ⟨111606579045821120188898063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74404386030547413459265375 111606579045821120188898063)
        ·
          refine ⟨167409868568731680283347095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111606579045821120188898063 167409868568731680283347095)
          ·
            refine ⟨251114802853097520425020643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167409868568731680283347095 251114802853097520425020643)
            ·
              refine ⟨376672204279646280637530965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251114802853097520425020643 376672204279646280637530965)
              ·
                refine ⟨2207063696951052425610533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 376672204279646280637530965 2207063696951052425610533)
                ·
                  refine ⟨413824443178322329801975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207063696951052425610533 413824443178322329801975)
                  ·
                    rfl

theorem cell22_3626641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_3626641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626641 prefixEnd_3626641 := by exact prefixLift 3626641
  have htrace : WordTrace (prefixWord ++ tailWord_3626641) baseStart_3626641 baseEnd_3626641 := by
    simpa [prefixWord, tailWord_3626641, baseEnd_3626641] using wordTrace_append hprefix tailTrace_3626641
  have hstable : (prefixWord ++ tailWord_3626641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626641).length < 2 ^ (prefixWord ++ tailWord_3626641).sum := by decide
  have hdescent : baseEnd_3626641 < baseStart_3626641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626664 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_3626664 : Nat := 118140960795 + 3626664 * 2 ^ 59
def prefixEnd_3626664 : Nat := 4983230072969 + 3 ^ 40 * 3626664 * 2
def baseEnd_3626664 : Nat := 413827067635000865360285

theorem tailTrace_3626664 : CollatzResearch.WordTrace tailWord_3626664 prefixEnd_3626664 413827067635000865360285 := by
  unfold tailWord_3626664
  simp only [CollatzResearch.WordTrace]
  refine ⟨66137651466611593872279523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88183535288815458496372697 66137651466611593872279523)
  ·
    refine ⟨99206477199917390808419285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66137651466611593872279523 99206477199917390808419285)
    ·
      refine ⟨2325151809373063847072327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 99206477199917390808419285 2325151809373063847072327)
      ·
        refine ⟨3487727714059595770608491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325151809373063847072327 3487727714059595770608491)
        ·
          refine ⟨5231591571089393655912737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487727714059595770608491 5231591571089393655912737)
          ·
            refine ⟨3923693678317045241934553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231591571089393655912737 3923693678317045241934553)
            ·
              refine ⟨2942770258737783931450915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923693678317045241934553 2942770258737783931450915)
              ·
                refine ⟨4414155388106675897176373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942770258737783931450915 4414155388106675897176373)
                ·
                  refine ⟨413827067635000865360285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414155388106675897176373 413827067635000865360285)
                  ·
                    rfl

theorem cell22_3626664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_3626664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626664 prefixEnd_3626664 := by exact prefixLift 3626664
  have htrace : WordTrace (prefixWord ++ tailWord_3626664) baseStart_3626664 baseEnd_3626664 := by
    simpa [prefixWord, tailWord_3626664, baseEnd_3626664] using wordTrace_append hprefix tailTrace_3626664
  have hstable : (prefixWord ++ tailWord_3626664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626664).length < 2 ^ (prefixWord ++ tailWord_3626664).sum := by decide
  have hdescent : baseEnd_3626664 < baseStart_3626664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626677 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3626677 : Nat := 118140960795 + 3626677 * 2 ^ 59
def prefixEnd_3626677 : Nat := 4983230072969 + 3 ^ 40 * 3626677 * 2
def baseEnd_3626677 : Nat := 1241485653070674895505815

theorem tailTrace_3626677 : CollatzResearch.WordTrace tailWord_3626677 prefixEnd_3626677 1241485653070674895505815 := by
  unfold tailWord_3626677
  simp only [CollatzResearch.WordTrace]
  refine ⟨132275777082176090964782285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88183851388117393976521523 132275777082176090964782285)
  ·
    refine ⟨49603416405816034111793357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132275777082176090964782285 49603416405816034111793357)
    ·
      refine ⟨18601281152181012791922509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49603416405816034111793357 18601281152181012791922509)
      ·
        refine ⟨6975480432067879796970941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18601281152181012791922509 6975480432067879796970941)
        ·
          refine ⟨2615805162025454923864103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6975480432067879796970941 2615805162025454923864103)
          ·
            refine ⟨3923707743038182385796155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615805162025454923864103 3923707743038182385796155)
            ·
              refine ⟨5885561614557273578694233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923707743038182385796155 5885561614557273578694233)
              ·
                refine ⟨4414171210917955184020675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885561614557273578694233 4414171210917955184020675)
                ·
                  refine ⟨6621256816376932776031013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414171210917955184020675 6621256816376932776031013)
                  ·
                    refine ⟨1241485653070674895505815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621256816376932776031013 1241485653070674895505815)
                    ·
                      rfl

theorem cell22_3626677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3626677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626677 prefixEnd_3626677 := by exact prefixLift 3626677
  have htrace : WordTrace (prefixWord ++ tailWord_3626677) baseStart_3626677 baseEnd_3626677 := by
    simpa [prefixWord, tailWord_3626677, baseEnd_3626677] using wordTrace_append hprefix tailTrace_3626677
  have hstable : (prefixWord ++ tailWord_3626677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626677).length < 2 ^ (prefixWord ++ tailWord_3626677).sum := by decide
  have hdescent : baseEnd_3626677 < baseStart_3626677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626686 : List Nat := [4, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3626686 : Nat := 118140960795 + 3626686 * 2 ^ 59
def prefixEnd_3626686 : Nat := 4983230072969 + 3 ^ 40 * 3626686 * 2
def baseEnd_3626686 : Nat := 137943192661622430225643

theorem tailTrace_3626686 : CollatzResearch.WordTrace tailWord_3626686 prefixEnd_3626686 137943192661622430225643 := by
  unfold tailWord_3626686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534513167392935687732489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88184070226095657001239941 16534513167392935687732489)
  ·
    refine ⟨12400884875544701765799367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16534513167392935687732489 12400884875544701765799367)
    ·
      refine ⟨18601327313317052648699051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12400884875544701765799367 18601327313317052648699051)
      ·
        refine ⟨27901990969975578973048577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18601327313317052648699051 27901990969975578973048577)
        ·
          refine ⟨20926493227481684229786433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27901990969975578973048577 20926493227481684229786433)
          ·
            refine ⟨15694869920611263172339825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20926493227481684229786433 15694869920611263172339825)
            ·
              refine ⟨11771152440458447379254869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15694869920611263172339825 11771152440458447379254869)
              ·
                refine ⟨137943192661622430225643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11771152440458447379254869 137943192661622430225643)
                ·
                  rfl

theorem cell22_3626686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3626686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626686 prefixEnd_3626686 := by exact prefixLift 3626686
  have htrace : WordTrace (prefixWord ++ tailWord_3626686) baseStart_3626686 baseEnd_3626686 := by
    simpa [prefixWord, tailWord_3626686, baseEnd_3626686] using wordTrace_append hprefix tailTrace_3626686
  have hstable : (prefixWord ++ tailWord_3626686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626686).length < 2 ^ (prefixWord ++ tailWord_3626686).sum := by decide
  have hdescent : baseEnd_3626686 < baseStart_3626686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626694 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3626694 : Nat := 118140960795 + 3626694 * 2 ^ 59
def prefixEnd_3626694 : Nat := 4983230072969 + 3 ^ 40 * 3626694 * 2
def baseEnd_3626694 : Nat := 1241491472518092517830763

theorem tailTrace_3626694 : CollatzResearch.WordTrace tailWord_3626694 prefixEnd_3626694 1241491472518092517830763 := by
  unfold tailWord_3626694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133637410097328214629723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88184264748743001912100757 4133637410097328214629723)
  ·
    refine ⟨6200456115145992321944585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133637410097328214629723 6200456115145992321944585)
    ·
      refine ⟨4650342086359494241458439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6200456115145992321944585 4650342086359494241458439)
      ·
        refine ⟨6975513129539241362187659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650342086359494241458439 6975513129539241362187659)
        ·
          refine ⟨10463269694308862043281489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6975513129539241362187659 10463269694308862043281489)
          ·
            refine ⟨7847452270731646532461117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10463269694308862043281489 7847452270731646532461117)
            ·
              refine ⟨2942794601524367449672919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7847452270731646532461117 2942794601524367449672919)
              ·
                refine ⟨4414191902286551174509379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942794601524367449672919 4414191902286551174509379)
                ·
                  refine ⟨6621287853429826761764069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414191902286551174509379 6621287853429826761764069)
                  ·
                    refine ⟨1241491472518092517830763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621287853429826761764069 1241491472518092517830763)
                    ·
                      rfl

theorem cell22_3626694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3626694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626694 prefixEnd_3626694 := by exact prefixLift 3626694
  have htrace : WordTrace (prefixWord ++ tailWord_3626694) baseStart_3626694 baseEnd_3626694 := by
    simpa [prefixWord, tailWord_3626694, baseEnd_3626694] using wordTrace_append hprefix tailTrace_3626694
  have hstable : (prefixWord ++ tailWord_3626694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626694).length < 2 ^ (prefixWord ++ tailWord_3626694).sum := by decide
  have hdescent : baseEnd_3626694 < baseStart_3626694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626699 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_3626699 : Nat := 118140960795 + 3626699 * 2 ^ 59
def prefixEnd_3626699 : Nat := 4983230072969 + 3 ^ 40 * 3626699 * 2
def baseEnd_3626699 : Nat := 1241493184120274171455747

theorem tailTrace_3626699 : CollatzResearch.WordTrace tailWord_3626699 prefixEnd_3626699 1241493184120274171455747 := by
  unfold tailWord_3626699
  simp only [CollatzResearch.WordTrace]
  refine ⟨132276579488096388722083151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88184386325397592481388767 132276579488096388722083151)
  ·
    refine ⟨198414869232144583083124727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132276579488096388722083151 198414869232144583083124727)
    ·
      refine ⟨297622303848216874624687091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198414869232144583083124727 297622303848216874624687091)
      ·
        refine ⟨446433455772325311937030637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297622303848216874624687091 446433455772325311937030637)
        ·
          refine ⟨167412545914621991976386489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446433455772325311937030637 167412545914621991976386489)
          ·
            refine ⟨125559409435966493982289867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167412545914621991976386489 125559409435966493982289867)
            ·
              refine ⟨188339114153949740973434801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125559409435966493982289867 188339114153949740973434801)
              ·
                refine ⟨141254335615462305730076101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188339114153949740973434801 141254335615462305730076101)
                ·
                  refine ⟨26485187927899182324389269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141254335615462305730076101 26485187927899182324389269)
                  ·
                    refine ⟨1241493184120274171455747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26485187927899182324389269 1241493184120274171455747)
                    ·
                      rfl

theorem cell22_3626699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_3626699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626699 prefixEnd_3626699 := by exact prefixLift 3626699
  have htrace : WordTrace (prefixWord ++ tailWord_3626699) baseStart_3626699 baseEnd_3626699 := by
    simpa [prefixWord, tailWord_3626699, baseEnd_3626699] using wordTrace_append hprefix tailTrace_3626699
  have hstable : (prefixWord ++ tailWord_3626699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626699).length < 2 ^ (prefixWord ++ tailWord_3626699).sum := by decide
  have hdescent : baseEnd_3626699 < baseStart_3626699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626731 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 5]
def baseStart_3626731 : Nat := 118140960795 + 3626731 * 2 ^ 59
def prefixEnd_3626731 : Nat := 4983230072969 + 3 ^ 40 * 3626731 * 2
def baseEnd_3626731 : Nat := 413834712791412251551883

theorem tailTrace_3626731 : CollatzResearch.WordTrace tailWord_3626731 prefixEnd_3626731 413834712791412251551883 := by
  unfold tailWord_3626731
  simp only [CollatzResearch.WordTrace]
  refine ⟨132277746623980458187248047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88185164415986972124832031 132277746623980458187248047)
  ·
    refine ⟨198416619935970687280872071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132277746623980458187248047 198416619935970687280872071)
    ·
      refine ⟨297624929903956030921308107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198416619935970687280872071 297624929903956030921308107)
      ·
        refine ⟨446437394855934046381962161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297624929903956030921308107 446437394855934046381962161)
        ·
          refine ⟨334828046141950534786471621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446437394855934046381962161 334828046141950534786471621)
          ·
            refine ⟨62780258651615725272463429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334828046141950534786471621 62780258651615725272463429)
            ·
              refine ⟨11771298497177948488586893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62780258651615725272463429 11771298497177948488586893)
              ·
                refine ⟨4414236936441730683220085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771298497177948488586893 4414236936441730683220085)
                ·
                  refine ⟨413834712791412251551883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414236936441730683220085 413834712791412251551883)
                  ·
                    rfl

theorem cell22_3626731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].length) (baseStart_3626731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626731 prefixEnd_3626731 := by exact prefixLift 3626731
  have htrace : WordTrace (prefixWord ++ tailWord_3626731) baseStart_3626731 baseEnd_3626731 := by
    simpa [prefixWord, tailWord_3626731, baseEnd_3626731] using wordTrace_append hprefix tailTrace_3626731
  have hstable : (prefixWord ++ tailWord_3626731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626731).length < 2 ^ (prefixWord ++ tailWord_3626731).sum := by decide
  have hdescent : baseEnd_3626731 < baseStart_3626731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626776 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_3626776 : Nat := 118140960795 + 3626776 * 2 ^ 59
def prefixEnd_3626776 : Nat := 4983230072969 + 3 ^ 40 * 3626776 * 2
def baseEnd_3626776 : Nat := 413839847597957212426837

theorem tailTrace_3626776 : CollatzResearch.WordTrace tailWord_3626776 prefixEnd_3626776 413839847597957212426837 := by
  unfold tailWord_3626776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139693954408715436318091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88186258605878287248424121 66139693954408715436318091)
  ·
    refine ⟨99209540931613073154477137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66139693954408715436318091 99209540931613073154477137)
    ·
      refine ⟨74407155698709804865857853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99209540931613073154477137 74407155698709804865857853)
      ·
        refine ⟨27902683387016176824696695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74407155698709804865857853 27902683387016176824696695)
        ·
          refine ⟨41854025080524265237045043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902683387016176824696695 41854025080524265237045043)
          ·
            refine ⟨62781037620786397855567565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41854025080524265237045043 62781037620786397855567565)
            ·
              refine ⟨23542889107794899195837837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62781037620786397855567565 23542889107794899195837837)
              ·
                refine ⟨8828583415423087198439189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23542889107794899195837837 8828583415423087198439189)
                ·
                  refine ⟨413839847597957212426837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8828583415423087198439189 413839847597957212426837)
                  ·
                    rfl

theorem cell22_3626776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_3626776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626776 prefixEnd_3626776 := by exact prefixLift 3626776
  have htrace : WordTrace (prefixWord ++ tailWord_3626776) baseStart_3626776 baseEnd_3626776 := by
    simpa [prefixWord, tailWord_3626776, baseEnd_3626776] using wordTrace_append hprefix tailTrace_3626776
  have hstable : (prefixWord ++ tailWord_3626776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626776).length < 2 ^ (prefixWord ++ tailWord_3626776).sum := by decide
  have hdescent : baseEnd_3626776 < baseStart_3626776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626808 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_3626808 : Nat := 118140960795 + 3626808 * 2 ^ 59
def prefixEnd_3626808 : Nat := 4983230072969 + 3 ^ 40 * 3626808 * 2
def baseEnd_3626808 : Nat := 1241530497047834220480413

theorem tailTrace_3626808 : CollatzResearch.WordTrace tailWord_3626808 prefixEnd_3626808 1241530497047834220480413 := by
  unfold tailWord_3626808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66140277522350750168900539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88187036696467666891867385 66140277522350750168900539)
  ·
    refine ⟨99210416283526125253350809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66140277522350750168900539 99210416283526125253350809)
    ·
      refine ⟨74407812212644593940013107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99210416283526125253350809 74407812212644593940013107)
      ·
        refine ⟨111611718318966890910019661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74407812212644593940013107 111611718318966890910019661)
        ·
          refine ⟨41854394369612584091257373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111611718318966890910019661 41854394369612584091257373)
          ·
            refine ⟨15695397888604719034221515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41854394369612584091257373 15695397888604719034221515)
            ·
              refine ⟨23543096832907078551332273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695397888604719034221515 23543096832907078551332273)
              ·
                refine ⟨17657322624680308913499205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23543096832907078551332273 17657322624680308913499205)
                ·
                  refine ⟨3310747992127557921281101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17657322624680308913499205 3310747992127557921281101)
                  ·
                    refine ⟨1241530497047834220480413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310747992127557921281101 1241530497047834220480413)
                    ·
                      rfl

theorem cell22_3626808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_3626808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626808 prefixEnd_3626808 := by exact prefixLift 3626808
  have htrace : WordTrace (prefixWord ++ tailWord_3626808) baseStart_3626808 baseEnd_3626808 := by
    simpa [prefixWord, tailWord_3626808, baseEnd_3626808] using wordTrace_append hprefix tailTrace_3626808
  have hstable : (prefixWord ++ tailWord_3626808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626808).length < 2 ^ (prefixWord ++ tailWord_3626808).sum := by decide
  have hdescent : baseEnd_3626808 < baseStart_3626808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626810 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_3626810 : Nat := 118140960795 + 3626810 * 2 ^ 59
def prefixEnd_3626810 : Nat := 4983230072969 + 3 ^ 40 * 3626810 * 2
def baseEnd_3626810 : Nat := 413843727229568960643469

theorem tailTrace_3626810 : CollatzResearch.WordTrace tailWord_3626810 prefixEnd_3626810 413843727229568960643469 := by
  unfold tailWord_3626810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070156997673563669843471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88187085327129503119582589 33070156997673563669843471)
  ·
    refine ⟨49605235496510345504765207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33070156997673563669843471 49605235496510345504765207)
    ·
      refine ⟨74407853244765518257147811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49605235496510345504765207 74407853244765518257147811)
      ·
        refine ⟨111611779867148277385721717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74407853244765518257147811 111611779867148277385721717)
        ·
          refine ⟨10463604362545151004911411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111611779867148277385721717 10463604362545151004911411)
          ·
            refine ⟨15695406543817726507367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10463604362545151004911411 15695406543817726507367117)
            ·
              refine ⟨5885777453931647440262669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15695406543817726507367117 5885777453931647440262669)
              ·
                refine ⟨2207166545224367790098501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5885777453931647440262669 2207166545224367790098501)
                ·
                  refine ⟨413843727229568960643469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207166545224367790098501 413843727229568960643469)
                  ·
                    rfl

theorem cell22_3626810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_3626810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626810 prefixEnd_3626810 := by exact prefixLift 3626810
  have htrace : WordTrace (prefixWord ++ tailWord_3626810) baseStart_3626810 baseEnd_3626810 := by
    simpa [prefixWord, tailWord_3626810, baseEnd_3626810] using wordTrace_append hprefix tailTrace_3626810
  have hstable : (prefixWord ++ tailWord_3626810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626810).length < 2 ^ (prefixWord ++ tailWord_3626810).sum := by decide
  have hdescent : baseEnd_3626810 < baseStart_3626810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626853 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_3626853 : Nat := 118140960795 + 3626853 * 2 ^ 59
def prefixEnd_3626853 : Nat := 4983230072969 + 3 ^ 40 * 3626853 * 2
def baseEnd_3626853 : Nat := 1241545901467469103105275

theorem tailTrace_3626853 : CollatzResearch.WordTrace tailWord_3626853 prefixEnd_3626853 1241545901467469103105275 := by
  unfold tailWord_3626853
  simp only [CollatzResearch.WordTrace]
  refine ⟨132282196329538473023189213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88188130886358982015459475 132282196329538473023189213)
  ·
    refine ⟨49605823623576927383695955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132282196329538473023189213 49605823623576927383695955)
    ·
      refine ⟨74408735435365391075543933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49605823623576927383695955 74408735435365391075543933)
      ·
        refine ⟨27903275788262021653328975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74408735435365391075543933 27903275788262021653328975)
        ·
          refine ⟨41854913682393032479993463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27903275788262021653328975 41854913682393032479993463)
          ·
            refine ⟨62782370523589548719990195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41854913682393032479993463 62782370523589548719990195)
            ·
              refine ⟨94173555785384323079985293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62782370523589548719990195 94173555785384323079985293)
              ·
                refine ⟨35315083419519121154994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94173555785384323079985293 35315083419519121154994485)
                ·
                  refine ⟨3310789070579917608280733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35315083419519121154994485 3310789070579917608280733)
                  ·
                    refine ⟨1241545901467469103105275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310789070579917608280733 1241545901467469103105275)
                    ·
                      rfl

theorem cell22_3626853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_3626853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626853 prefixEnd_3626853 := by exact prefixLift 3626853
  have htrace : WordTrace (prefixWord ++ tailWord_3626853) baseStart_3626853 baseEnd_3626853 := by
    simpa [prefixWord, tailWord_3626853, baseEnd_3626853] using wordTrace_append hprefix tailTrace_3626853
  have hstable : (prefixWord ++ tailWord_3626853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626853).length < 2 ^ (prefixWord ++ tailWord_3626853).sum := by decide
  have hdescent : baseEnd_3626853 < baseStart_3626853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626883 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 5]
def baseStart_3626883 : Nat := 118140960795 + 3626883 * 2 ^ 59
def prefixEnd_3626883 : Nat := 4983230072969 + 3 ^ 40 * 3626883 * 2
def baseEnd_3626883 : Nat := 413852057026853008285061

theorem tailTrace_3626883 : CollatzResearch.WordTrace tailWord_3626883 prefixEnd_3626883 413852057026853008285061 := by
  unfold tailWord_3626883
  simp only [CollatzResearch.WordTrace]
  refine ⟨132283290519429788146781303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88188860346286525431187535 132283290519429788146781303)
  ·
    refine ⟨198424935779144682220171955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132283290519429788146781303 198424935779144682220171955)
    ·
      refine ⟨297637403668717023330257933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198424935779144682220171955 297637403668717023330257933)
      ·
        refine ⟨111614026375768883748846725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297637403668717023330257933 111614026375768883748846725)
        ·
          refine ⟨20927629945456665702908761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111614026375768883748846725 20927629945456665702908761)
          ·
            refine ⟨15695722459092499277181571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20927629945456665702908761 15695722459092499277181571)
            ·
              refine ⟨23543583688638748915772357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695722459092499277181571 23543583688638748915772357)
              ·
                refine ⟨4414421941619765421707317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23543583688638748915772357 4414421941619765421707317)
                ·
                  refine ⟨413852057026853008285061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414421941619765421707317 413852057026853008285061)
                  ·
                    rfl

theorem cell22_3626883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].length) (baseStart_3626883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626883 prefixEnd_3626883 := by exact prefixLift 3626883
  have htrace : WordTrace (prefixWord ++ tailWord_3626883) baseStart_3626883 baseEnd_3626883 := by
    simpa [prefixWord, tailWord_3626883, baseEnd_3626883] using wordTrace_append hprefix tailTrace_3626883
  have hstable : (prefixWord ++ tailWord_3626883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626883).length < 2 ^ (prefixWord ++ tailWord_3626883).sum := by decide
  have hdescent : baseEnd_3626883 < baseStart_3626883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626896 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_3626896 : Nat := 118140960795 + 3626896 * 2 ^ 59
def prefixEnd_3626896 : Nat := 4983230072969 + 3 ^ 40 * 3626896 * 2
def baseEnd_3626896 : Nat := 1241560621246231324280143

theorem tailTrace_3626896 : CollatzResearch.WordTrace tailWord_3626896 prefixEnd_3626896 1241560621246231324280143 := by
  unfold tailWord_3626896
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141882334191345683502271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88189176445588460911336361 66141882334191345683502271)
  ·
    refine ⟨99212823501287018525253407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66141882334191345683502271 99212823501287018525253407)
    ·
      refine ⟨148819235251930527787880111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99212823501287018525253407 148819235251930527787880111)
      ·
        refine ⟨223228852877895791681820167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148819235251930527787880111 223228852877895791681820167)
        ·
          refine ⟨334843279316843687522730251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223228852877895791681820167 334843279316843687522730251)
          ·
            refine ⟨502264918975265531284095377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334843279316843687522730251 502264918975265531284095377)
            ·
              refine ⟨376698689231449148463071533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502264918975265531284095377 376698689231449148463071533)
              ·
                refine ⟨141262008461793430673651825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376698689231449148463071533 141262008461793430673651825)
                ·
                  refine ⟨105946506346345073005238869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141262008461793430673651825 105946506346345073005238869)
                  ·
                    refine ⟨1241560621246231324280143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105946506346345073005238869 1241560621246231324280143)
                    ·
                      rfl

theorem cell22_3626896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_3626896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626896 prefixEnd_3626896 := by exact prefixLift 3626896
  have htrace : WordTrace (prefixWord ++ tailWord_3626896) baseStart_3626896 baseEnd_3626896 := by
    simpa [prefixWord, tailWord_3626896, baseEnd_3626896] using wordTrace_append hprefix tailTrace_3626896
  have hstable : (prefixWord ++ tailWord_3626896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626896).length < 2 ^ (prefixWord ++ tailWord_3626896).sum := by decide
  have hdescent : baseEnd_3626896 < baseStart_3626896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626900 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3626900 : Nat := 118140960795 + 3626900 * 2 ^ 59
def prefixEnd_3626900 : Nat := 4983230072969 + 3 ^ 40 * 3626900 * 2
def baseEnd_3626900 : Nat := 413853996842658882393377

theorem tailTrace_3626900 : CollatzResearch.WordTrace tailWord_3626900 prefixEnd_3626900 413853996842658882393377 := by
  unfold tailWord_3626900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141955280184100025075077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88189273706912133366766769 66141955280184100025075077)
  ·
    refine ⟨12401616615034518754701577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66141955280184100025075077 12401616615034518754701577)
    ·
      refine ⟨9301212461275889066026183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401616615034518754701577 9301212461275889066026183)
      ·
        refine ⟨13951818691913833599039275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301212461275889066026183 13951818691913833599039275)
        ·
          refine ⟨20927728037870750398558913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13951818691913833599039275 20927728037870750398558913)
          ·
            refine ⟨15695796028403062798919185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20927728037870750398558913 15695796028403062798919185)
            ·
              refine ⟨11771847021302297099189389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15695796028403062798919185 11771847021302297099189389)
              ·
                refine ⟨4414442632988361412196021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771847021302297099189389 4414442632988361412196021)
                ·
                  refine ⟨413853996842658882393377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414442632988361412196021 413853996842658882393377)
                  ·
                    rfl

theorem cell22_3626900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3626900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626900 prefixEnd_3626900 := by exact prefixLift 3626900
  have htrace : WordTrace (prefixWord ++ tailWord_3626900) baseStart_3626900 baseEnd_3626900 := by
    simpa [prefixWord, tailWord_3626900, baseEnd_3626900] using wordTrace_append hprefix tailTrace_3626900
  have hstable : (prefixWord ++ tailWord_3626900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626900).length < 2 ^ (prefixWord ++ tailWord_3626900).sum := by decide
  have hdescent : baseEnd_3626900 < baseStart_3626900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626958 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3626958 : Nat := 118140960795 + 3626958 * 2 ^ 59
def prefixEnd_3626958 : Nat := 4983230072969 + 3 ^ 40 * 3626958 * 2
def baseEnd_3626958 : Nat := 1241581845113283829229953

theorem tailTrace_3626958 : CollatzResearch.WordTrace tailWord_3626958 prefixEnd_3626958 1241581845113283829229953 := by
  unfold tailWord_3626958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535753249269759494470191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88190683996105383970507685 16535753249269759494470191)
  ·
    refine ⟨24803629873904639241705287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535753249269759494470191 24803629873904639241705287)
    ·
      refine ⟨37205444810856958862557931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24803629873904639241705287 37205444810856958862557931)
      ·
        refine ⟨55808167216285438293836897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37205444810856958862557931 55808167216285438293836897)
        ·
          refine ⟨41856125412214078720377673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55808167216285438293836897 41856125412214078720377673)
          ·
            refine ⟨31392094059160559040283255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41856125412214078720377673 31392094059160559040283255)
            ·
              refine ⟨47088141088740838560424883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31392094059160559040283255 47088141088740838560424883)
              ·
                refine ⟨70632211633111257840637325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47088141088740838560424883 70632211633111257840637325)
                ·
                  refine ⟨26487079362416721690238997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70632211633111257840637325 26487079362416721690238997)
                  ·
                    refine ⟨1241581845113283829229953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26487079362416721690238997 1241581845113283829229953)
                    ·
                      rfl

theorem cell22_3626958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3626958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626958 prefixEnd_3626958 := by exact prefixLift 3626958
  have htrace : WordTrace (prefixWord ++ tailWord_3626958) baseStart_3626958 baseEnd_3626958 := by
    simpa [prefixWord, tailWord_3626958, baseEnd_3626958] using wordTrace_append hprefix tailTrace_3626958
  have hstable : (prefixWord ++ tailWord_3626958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626958).length < 2 ^ (prefixWord ++ tailWord_3626958).sum := by decide
  have hdescent : baseEnd_3626958 < baseStart_3626958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626960 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_3626960 : Nat := 118140960795 + 3626960 * 2 ^ 59
def prefixEnd_3626960 : Nat := 4983230072969 + 3 ^ 40 * 3626960 * 2
def baseEnd_3626960 : Nat := 1241582529754156490679947

theorem tailTrace_3626960 : CollatzResearch.WordTrace tailWord_3626960 prefixEnd_3626960 1241582529754156490679947 := by
  unfold tailWord_3626960
  simp only [CollatzResearch.WordTrace]
  refine ⟨66143049470075415148667167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88190732626767220198222889 66143049470075415148667167)
  ·
    refine ⟨99214574205113122723000751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66143049470075415148667167 99214574205113122723000751)
    ·
      refine ⟨148821861307669684084501127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99214574205113122723000751 148821861307669684084501127)
      ·
        refine ⟨223232791961504526126751691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148821861307669684084501127 223232791961504526126751691)
        ·
          refine ⟨334849187942256789190127537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223232791961504526126751691 334849187942256789190127537)
          ·
            refine ⟨251136890956692591892595653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334849187942256789190127537 251136890956692591892595653)
            ·
              refine ⟨47088167054379860979861685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251136890956692591892595653 47088167054379860979861685)
              ·
                refine ⟨4414515661348111966862033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47088167054379860979861685 4414515661348111966862033)
                ·
                  refine ⟨3310886746011083975146525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414515661348111966862033 3310886746011083975146525)
                  ·
                    refine ⟨1241582529754156490679947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310886746011083975146525 1241582529754156490679947)
                    ·
                      rfl

theorem cell22_3626960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_3626960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626960 prefixEnd_3626960 := by exact prefixLift 3626960
  have htrace : WordTrace (prefixWord ++ tailWord_3626960) baseStart_3626960 baseEnd_3626960 := by
    simpa [prefixWord, tailWord_3626960, baseEnd_3626960] using wordTrace_append hprefix tailTrace_3626960
  have hstable : (prefixWord ++ tailWord_3626960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626960).length < 2 ^ (prefixWord ++ tailWord_3626960).sum := by decide
  have hdescent : baseEnd_3626960 < baseStart_3626960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626990 : List Nat := [4, 1, 2, 1, 3, 3, 8]
def baseStart_3626990 : Nat := 118140960795 + 3626990 * 2 ^ 59
def prefixEnd_3626990 : Nat := 4983230072969 + 3 ^ 40 * 3626990 * 2
def baseEnd_3626990 : Nat := 45984918495083200460365

theorem tailTrace_3626990 : CollatzResearch.WordTrace tailWord_3626990 prefixEnd_3626990 45984918495083200460365 := by
  unfold tailWord_3626990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535899141255268177615803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88191462086694763613950949 16535899141255268177615803)
  ·
    refine ⟨24803848711882902266423705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535899141255268177615803 24803848711882902266423705)
    ·
      refine ⟨18602886533912176699817779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24803848711882902266423705 18602886533912176699817779)
      ·
        refine ⟨27904329800868265049726669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18602886533912176699817779 27904329800868265049726669)
        ·
          refine ⟨10464123675325599393647501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27904329800868265049726669 10464123675325599393647501)
          ·
            refine ⟨3924046378247099772617813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10464123675325599393647501 3924046378247099772617813)
            ·
              refine ⟨45984918495083200460365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3924046378247099772617813 45984918495083200460365)
              ·
                rfl

theorem cell22_3626990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 8].length) (baseStart_3626990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3626990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3626990 prefixEnd_3626990 := by exact prefixLift 3626990
  have htrace : WordTrace (prefixWord ++ tailWord_3626990) baseStart_3626990 baseEnd_3626990 := by
    simpa [prefixWord, tailWord_3626990, baseEnd_3626990] using wordTrace_append hprefix tailTrace_3626990
  have hstable : (prefixWord ++ tailWord_3626990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626990).length < 2 ^ (prefixWord ++ tailWord_3626990).sum := by decide
  have hdescent : baseEnd_3626990 < baseStart_3626990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627033 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3627033 : Nat := 118140960795 + 3627033 * 2 ^ 59
def prefixEnd_3627033 : Nat := 4983230072969 + 3 ^ 40 * 3627033 * 2
def baseEnd_3627033 : Nat := 1241607519146008633604723

theorem tailTrace_3627033 : CollatzResearch.WordTrace tailWord_3627033 prefixEnd_3627033 1241607519146008633604723 := by
  unfold tailWord_3627033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132288761468886363764741753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88192507645924242509827835 132288761468886363764741753)
  ·
    refine ⟨99216571101664772823556315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132288761468886363764741753 99216571101664772823556315)
    ·
      refine ⟨148824856652497159235334473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99216571101664772823556315 148824856652497159235334473)
      ·
        refine ⟨111618642489372869426500855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148824856652497159235334473 111618642489372869426500855)
        ·
          refine ⟨167427963734059304139751283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111618642489372869426500855 167427963734059304139751283)
          ·
            refine ⟨251141945601088956209626925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167427963734059304139751283 251141945601088956209626925)
            ·
              refine ⟨94178229600408358578610097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251141945601088956209626925 94178229600408358578610097)
              ·
                refine ⟨70633672200306268933957573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94178229600408358578610097 70633672200306268933957573)
                ·
                  refine ⟨13243813537557425425117045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70633672200306268933957573 13243813537557425425117045)
                  ·
                    refine ⟨1241607519146008633604723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13243813537557425425117045 1241607519146008633604723)
                    ·
                      rfl

theorem cell22_3627033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3627033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627033 prefixEnd_3627033 := by exact prefixLift 3627033
  have htrace : WordTrace (prefixWord ++ tailWord_3627033) baseStart_3627033 baseEnd_3627033 := by
    simpa [prefixWord, tailWord_3627033, baseEnd_3627033] using wordTrace_append hprefix tailTrace_3627033
  have hstable : (prefixWord ++ tailWord_3627033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627033).length < 2 ^ (prefixWord ++ tailWord_3627033).sum := by decide
  have hdescent : baseEnd_3627033 < baseStart_3627033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627056 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_3627056 : Nat := 118140960795 + 3627056 * 2 ^ 59
def prefixEnd_3627056 : Nat := 4983230072969 + 3 ^ 40 * 3627056 * 2
def baseEnd_3627056 : Nat := 1241615392516044240279653

theorem tailTrace_3627056 : CollatzResearch.WordTrace tailWord_3627056 prefixEnd_3627056 1241615392516044240279653 := by
  unfold tailWord_3627056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144800173901519346414511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88193066898535359128552681 66144800173901519346414511)
  ·
    refine ⟨99217200260852279019621767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66144800173901519346414511 99217200260852279019621767)
    ·
      refine ⟨148825800391278418529432651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99217200260852279019621767 148825800391278418529432651)
      ·
        refine ⟨223238700586917627794148977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148825800391278418529432651 223238700586917627794148977)
        ·
          refine ⟨167429025440188220845611733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223238700586917627794148977 167429025440188220845611733)
          ·
            refine ⟨3924117783754411426069025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167429025440188220845611733 3924117783754411426069025)
            ·
              refine ⟨2943088337815808569551769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924117783754411426069025 2943088337815808569551769)
              ·
                refine ⟨2207316253361856427163827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943088337815808569551769 2207316253361856427163827)
                ·
                  refine ⟨3310974380042784640745741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207316253361856427163827 3310974380042784640745741)
                  ·
                    refine ⟨1241615392516044240279653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3310974380042784640745741 1241615392516044240279653)
                    ·
                      rfl

theorem cell22_3627056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_3627056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627056 prefixEnd_3627056 := by exact prefixLift 3627056
  have htrace : WordTrace (prefixWord ++ tailWord_3627056) baseStart_3627056 baseEnd_3627056 := by
    simpa [prefixWord, tailWord_3627056, baseEnd_3627056] using wordTrace_append hprefix tailTrace_3627056
  have hstable : (prefixWord ++ tailWord_3627056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627056).length < 2 ^ (prefixWord ++ tailWord_3627056).sum := by decide
  have hdescent : baseEnd_3627056 < baseStart_3627056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627095 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3627095 : Nat := 118140960795 + 3627095 * 2 ^ 59
def prefixEnd_3627095 : Nat := 4983230072969 + 3 ^ 40 * 3627095 * 2
def baseEnd_3627095 : Nat := 1241628743013061138554533

theorem tailTrace_3627095 : CollatzResearch.WordTrace tailWord_3627095 prefixEnd_3627095 1241628743013061138554533 := by
  unfold tailWord_3627095
  simp only [CollatzResearch.WordTrace]
  refine ⟨132291022794661748353498739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88194015196441165568999159 132291022794661748353498739)
  ·
    refine ⟨198436534191992622530248109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132291022794661748353498739 198436534191992622530248109)
    ·
      refine ⟨74413700321997233448843041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198436534191992622530248109 74413700321997233448843041)
      ·
        refine ⟨55810275241497925086632281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74413700321997233448843041 55810275241497925086632281)
        ·
          refine ⟨41857706431123443814974211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55810275241497925086632281 41857706431123443814974211)
          ·
            refine ⟨62786559646685165722461317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41857706431123443814974211 62786559646685165722461317)
            ·
              refine ⟨11772479933753468572961497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62786559646685165722461317 11772479933753468572961497)
              ·
                refine ⟨8829359950315101429721123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11772479933753468572961497 8829359950315101429721123)
                ·
                  refine ⟨13244039925472652144581685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829359950315101429721123 13244039925472652144581685)
                  ·
                    refine ⟨1241628743013061138554533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13244039925472652144581685 1241628743013061138554533)
                    ·
                      rfl

theorem cell22_3627095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3627095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627095 prefixEnd_3627095 := by exact prefixLift 3627095
  have htrace : WordTrace (prefixWord ++ tailWord_3627095) baseStart_3627095 baseEnd_3627095 := by
    simpa [prefixWord, tailWord_3627095, baseEnd_3627095] using wordTrace_append hprefix tailTrace_3627095
  have hstable : (prefixWord ++ tailWord_3627095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627095).length < 2 ^ (prefixWord ++ tailWord_3627095).sum := by decide
  have hdescent : baseEnd_3627095 < baseStart_3627095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627097 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 4]
def baseStart_3627097 : Nat := 118140960795 + 3627097 * 2 ^ 59
def prefixEnd_3627097 : Nat := 4983230072969 + 3 ^ 40 * 3627097 * 2
def baseEnd_3627097 : Nat := 413876475884644600001509

theorem tailTrace_3627097 : CollatzResearch.WordTrace tailWord_3627097 prefixEnd_3627097 413876475884644600001509 := by
  unfold tailWord_3627097
  simp only [CollatzResearch.WordTrace]
  refine ⟨132291095740654502695071545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88194063827103001796714363 132291095740654502695071545)
  ·
    refine ⟨99218321805490877021303659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132291095740654502695071545 99218321805490877021303659)
    ·
      refine ⟨148827482708236315531955489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99218321805490877021303659 148827482708236315531955489)
      ·
        refine ⟨111620612031177236648966617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148827482708236315531955489 111620612031177236648966617)
        ·
          refine ⟨83715459023382927486724963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111620612031177236648966617 83715459023382927486724963)
          ·
            refine ⟨125573188535074391230087445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83715459023382927486724963 125573188535074391230087445)
            ·
              refine ⟨5886243212581612088910349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125573188535074391230087445 5886243212581612088910349)
              ·
                refine ⟨2207341204718104533341381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5886243212581612088910349 2207341204718104533341381)
                ·
                  refine ⟨413876475884644600001509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207341204718104533341381 413876475884644600001509)
                  ·
                    rfl

theorem cell22_3627097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_3627097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627097 prefixEnd_3627097 := by exact prefixLift 3627097
  have htrace : WordTrace (prefixWord ++ tailWord_3627097) baseStart_3627097 baseEnd_3627097 := by
    simpa [prefixWord, tailWord_3627097, baseEnd_3627097] using wordTrace_append hprefix tailTrace_3627097
  have hstable : (prefixWord ++ tailWord_3627097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627097).length < 2 ^ (prefixWord ++ tailWord_3627097).sum := by decide
  have hdescent : baseEnd_3627097 < baseStart_3627097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627140 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3627140 : Nat := 118140960795 + 3627140 * 2 ^ 59
def prefixEnd_3627140 : Nat := 4983230072969 + 3 ^ 40 * 3627140 * 2
def baseEnd_3627140 : Nat := 1241644147432696021179395

theorem tailTrace_3627140 : CollatzResearch.WordTrace tailWord_3627140 prefixEnd_3627140 1241644147432696021179395 := by
  unfold tailWord_3627140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66146332039749360519443437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88195109386332480692591249 66146332039749360519443437)
  ·
    refine ⟨24804874514906010194791289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66146332039749360519443437 24804874514906010194791289)
    ·
      refine ⟨18603655886179507646093467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24804874514906010194791289 18603655886179507646093467)
      ·
        refine ⟨27905483829269261469140201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603655886179507646093467 27905483829269261469140201)
        ·
          refine ⟨20929112871951946101855151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27905483829269261469140201 20929112871951946101855151)
          ·
            refine ⟨31393669307927919152782727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20929112871951946101855151 31393669307927919152782727)
            ·
              refine ⟨47090503961891878729174091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31393669307927919152782727 47090503961891878729174091)
              ·
                refine ⟨70635755942837818093761137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47090503961891878729174091 70635755942837818093761137)
                ·
                  refine ⟨52976816957128363570320853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70635755942837818093761137 52976816957128363570320853)
                  ·
                    refine ⟨1241644147432696021179395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52976816957128363570320853 1241644147432696021179395)
                    ·
                      rfl

theorem cell22_3627140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3627140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627140 prefixEnd_3627140 := by exact prefixLift 3627140
  have htrace : WordTrace (prefixWord ++ tailWord_3627140) baseStart_3627140 baseEnd_3627140 := by
    simpa [prefixWord, tailWord_3627140, baseEnd_3627140] using wordTrace_append hprefix tailTrace_3627140
  have hstable : (prefixWord ++ tailWord_3627140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627140).length < 2 ^ (prefixWord ++ tailWord_3627140).sum := by decide
  have hdescent : baseEnd_3627140 < baseStart_3627140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627217 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_3627217 : Nat := 118140960795 + 3627217 * 2 ^ 59
def prefixEnd_3627217 : Nat := 4983230072969 + 3 ^ 40 * 3627217 * 2
def baseEnd_3627217 : Nat := 1241670506106293487004159

theorem tailTrace_3627217 : CollatzResearch.WordTrace tailWord_3627217 prefixEnd_3627217 1241670506106293487004159 := by
  unfold tailWord_3627217
  simp only [CollatzResearch.WordTrace]
  refine ⟨132295472500219763189439905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88196981666813175459626603 132295472500219763189439905)
  ·
    refine ⟨99221604375164822392079929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132295472500219763189439905 99221604375164822392079929)
    ·
      refine ⟨74416203281373616794059947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99221604375164822392079929 74416203281373616794059947)
      ·
        refine ⟨111624304922060425191089921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74416203281373616794059947 111624304922060425191089921)
        ·
          refine ⟨83718228691545318893317441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111624304922060425191089921 83718228691545318893317441)
          ·
            refine ⟨62788671518658989169988081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83718228691545318893317441 62788671518658989169988081)
            ·
              refine ⟨47091503638994241877491061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62788671518658989169988081 47091503638994241877491061)
              ·
                refine ⟨4414828466155710176014787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47091503638994241877491061 4414828466155710176014787)
                ·
                  refine ⟨6622242699233565264022181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414828466155710176014787 6622242699233565264022181)
                  ·
                    refine ⟨1241670506106293487004159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622242699233565264022181 1241670506106293487004159)
                    ·
                      rfl

theorem cell22_3627217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_3627217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627217 prefixEnd_3627217 := by exact prefixLift 3627217
  have htrace : WordTrace (prefixWord ++ tailWord_3627217) baseStart_3627217 baseEnd_3627217 := by
    simpa [prefixWord, tailWord_3627217, baseEnd_3627217] using wordTrace_append hprefix tailTrace_3627217
  have hstable : (prefixWord ++ tailWord_3627217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627217).length < 2 ^ (prefixWord ++ tailWord_3627217).sum := by decide
  have hdescent : baseEnd_3627217 < baseStart_3627217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627247 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3627247 : Nat := 118140960795 + 3627247 * 2 ^ 59
def prefixEnd_3627247 : Nat := 4983230072969 + 3 ^ 40 * 3627247 * 2
def baseEnd_3627247 : Nat := 1241680775719383408754067

theorem tailTrace_3627247 : CollatzResearch.WordTrace tailWord_3627247 prefixEnd_3627247 1241680775719383408754067 := by
  unfold tailWord_3627247
  simp only [CollatzResearch.WordTrace]
  refine ⟨132296566690111078313031995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88197711126740718875354663 132296566690111078313031995)
  ·
    refine ⟨198444850035166617469547993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132296566690111078313031995 198444850035166617469547993)
    ·
      refine ⟨148833637526374963102160995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198444850035166617469547993 148833637526374963102160995)
      ·
        refine ⟨223250456289562444653241493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148833637526374963102160995 223250456289562444653241493)
        ·
          refine ⟨10464865138573239593120695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223250456289562444653241493 10464865138573239593120695)
          ·
            refine ⟨15697297707859859389681043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464865138573239593120695 15697297707859859389681043)
            ·
              refine ⟨23545946561789789084521565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697297707859859389681043 23545946561789789084521565)
              ·
                refine ⟨8829729960671170906695587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23545946561789789084521565 8829729960671170906695587)
                ·
                  refine ⟨13244594941006756360043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829729960671170906695587 13244594941006756360043381)
                  ·
                    refine ⟨1241680775719383408754067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13244594941006756360043381 1241680775719383408754067)
                    ·
                      rfl

theorem cell22_3627247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3627247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627247 prefixEnd_3627247 := by exact prefixLift 3627247
  have htrace : WordTrace (prefixWord ++ tailWord_3627247) baseStart_3627247 baseEnd_3627247 := by
    simpa [prefixWord, tailWord_3627247, baseEnd_3627247] using wordTrace_append hprefix tailTrace_3627247
  have hstable : (prefixWord ++ tailWord_3627247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627247).length < 2 ^ (prefixWord ++ tailWord_3627247).sum := by decide
  have hdescent : baseEnd_3627247 < baseStart_3627247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627266 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3627266 : Nat := 118140960795 + 3627266 * 2 ^ 59
def prefixEnd_3627266 : Nat := 4983230072969 + 3 ^ 40 * 3627266 * 2
def baseEnd_3627266 : Nat := 413895759935891230843003

theorem tailTrace_3627266 : CollatzResearch.WordTrace tailWord_3627266 prefixEnd_3627266 413895759935891230843003 := by
  unfold tailWord_3627266
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074314919260561139493413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88198173118028163038649101 33074314919260561139493413)
  ·
    refine ⟨6201434047361355213655015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33074314919260561139493413 6201434047361355213655015)
    ·
      refine ⟨9302151071042032820482523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201434047361355213655015 9302151071042032820482523)
      ·
        refine ⟨13953226606563049230723785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302151071042032820482523 13953226606563049230723785)
        ·
          refine ⟨10464919954922286923042839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13953226606563049230723785 10464919954922286923042839)
          ·
            refine ⟨15697379932383430384564259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464919954922286923042839 15697379932383430384564259)
            ·
              refine ⟨23546069898575145576846389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697379932383430384564259 23546069898575145576846389)
              ·
                refine ⟨2207444052991419897829349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23546069898575145576846389 2207444052991419897829349)
                ·
                  refine ⟨413895759935891230843003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207444052991419897829349 413895759935891230843003)
                  ·
                    rfl

theorem cell22_3627266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3627266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627266 prefixEnd_3627266 := by exact prefixLift 3627266
  have htrace : WordTrace (prefixWord ++ tailWord_3627266) baseStart_3627266 baseEnd_3627266 := by
    simpa [prefixWord, tailWord_3627266, baseEnd_3627266] using wordTrace_append hprefix tailTrace_3627266
  have hstable : (prefixWord ++ tailWord_3627266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627266).length < 2 ^ (prefixWord ++ tailWord_3627266).sum := by decide
  have hdescent : baseEnd_3627266 < baseStart_3627266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627268 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3627268 : Nat := 118140960795 + 3627268 * 2 ^ 59
def prefixEnd_3627268 : Nat := 4983230072969 + 3 ^ 40 * 3627268 * 2
def baseEnd_3627268 : Nat := 1241687964448546353979003

theorem tailTrace_3627268 : CollatzResearch.WordTrace tailWord_3627268 prefixEnd_3627268 1241687964448546353979003 := by
  unfold tailWord_3627268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148666311517499449773229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88198221748689999266364305 66148666311517499449773229)
  ·
    refine ⟨24805749866819062293664961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66148666311517499449773229 24805749866819062293664961)
    ·
      refine ⟨18604312400114296720248721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24805749866819062293664961 18604312400114296720248721)
      ·
        refine ⟨13953234300085722540186541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18604312400114296720248721 13953234300085722540186541)
        ·
          refine ⟨5232462862532145952569953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13953234300085722540186541 5232462862532145952569953)
          ·
            refine ⟨3924347146899109464427465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232462862532145952569953 3924347146899109464427465)
            ·
              refine ⟨2943260360174332098320599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924347146899109464427465 2943260360174332098320599)
              ·
                refine ⟨4414890540261498147480899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943260360174332098320599 4414890540261498147480899)
                ·
                  refine ⟨6622335810392247221221349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414890540261498147480899 6622335810392247221221349)
                  ·
                    refine ⟨1241687964448546353979003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622335810392247221221349 1241687964448546353979003)
                    ·
                      rfl

theorem cell22_3627268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3627268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627268 prefixEnd_3627268 := by exact prefixLift 3627268
  have htrace : WordTrace (prefixWord ++ tailWord_3627268) baseStart_3627268 baseEnd_3627268 := by
    simpa [prefixWord, tailWord_3627268, baseEnd_3627268] using wordTrace_append hprefix tailTrace_3627268
  have hstable : (prefixWord ++ tailWord_3627268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627268).length < 2 ^ (prefixWord ++ tailWord_3627268).sum := by decide
  have hdescent : baseEnd_3627268 < baseStart_3627268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627281 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_3627281 : Nat := 118140960795 + 3627281 * 2 ^ 59
def prefixEnd_3627281 : Nat := 4983230072969 + 3 ^ 40 * 3627281 * 2
def baseEnd_3627281 : Nat := 1241692414614218653403963

theorem tailTrace_3627281 : CollatzResearch.WordTrace tailWord_3627281 prefixEnd_3627281 1241692414614218653403963 := by
  unfold tailWord_3627281
  simp only [CollatzResearch.WordTrace]
  refine ⟨132297806771987902119769697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88198537847991934746513131 132297806771987902119769697)
  ·
    refine ⟨99223355078990926589827273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132297806771987902119769697 99223355078990926589827273)
    ·
      refine ⟨74417516309243194942370455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99223355078990926589827273 74417516309243194942370455)
      ·
        refine ⟨111626274463864792413555683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74417516309243194942370455 111626274463864792413555683)
        ·
          refine ⟨167439411695797188620333525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111626274463864792413555683 167439411695797188620333525)
          ·
            refine ⟨3924361211620246608289067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167439411695797188620333525 3924361211620246608289067)
            ·
              refine ⟨5886541817430369912433601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924361211620246608289067 5886541817430369912433601)
              ·
                refine ⟨4414906363072777434325201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886541817430369912433601 4414906363072777434325201)
                ·
                  refine ⟨3311179772304583075743901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414906363072777434325201 3311179772304583075743901)
                  ·
                    refine ⟨1241692414614218653403963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311179772304583075743901 1241692414614218653403963)
                    ·
                      rfl

theorem cell22_3627281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_3627281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627281 prefixEnd_3627281 := by exact prefixLift 3627281
  have htrace : WordTrace (prefixWord ++ tailWord_3627281) baseStart_3627281 baseEnd_3627281 := by
    simpa [prefixWord, tailWord_3627281, baseEnd_3627281] using wordTrace_append hprefix tailTrace_3627281
  have hstable : (prefixWord ++ tailWord_3627281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627281).length < 2 ^ (prefixWord ++ tailWord_3627281).sum := by decide
  have hdescent : baseEnd_3627281 < baseStart_3627281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627298 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3627298 : Nat := 118140960795 + 3627298 * 2 ^ 59
def prefixEnd_3627298 : Nat := 4983230072969 + 3 ^ 40 * 3627298 * 2
def baseEnd_3627298 : Nat := 1241698234061636275728911

theorem tailTrace_3627298 : CollatzResearch.WordTrace tailWord_3627298 prefixEnd_3627298 1241698234061636275728911 := by
  unfold tailWord_3627298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074606703231578505784637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88198951208617542682092365 33074606703231578505784637)
  ·
    refine ⟨12402977513711841939669239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33074606703231578505784637 12402977513711841939669239)
    ·
      refine ⟨18604466270567762909503859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12402977513711841939669239 18604466270567762909503859)
      ·
        refine ⟨27906699405851644364255789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604466270567762909503859 27906699405851644364255789)
        ·
          refine ⟨10465012277194366636595921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27906699405851644364255789 10465012277194366636595921)
          ·
            refine ⟨7848759207895774977446941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465012277194366636595921 7848759207895774977446941)
            ·
              refine ⟨2943284702960915616542603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7848759207895774977446941 2943284702960915616542603)
              ·
                refine ⟨4414927054441373424813905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943284702960915616542603 4414927054441373424813905)
                ·
                  refine ⟨3311195290831030068610429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414927054441373424813905 3311195290831030068610429)
                  ·
                    refine ⟨1241698234061636275728911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311195290831030068610429 1241698234061636275728911)
                    ·
                      rfl

theorem cell22_3627298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3627298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627298 prefixEnd_3627298 := by exact prefixLift 3627298
  have htrace : WordTrace (prefixWord ++ tailWord_3627298) baseStart_3627298 baseEnd_3627298 := by
    simpa [prefixWord, tailWord_3627298, baseEnd_3627298] using wordTrace_append hprefix tailTrace_3627298
  have hstable : (prefixWord ++ tailWord_3627298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627298).length < 2 ^ (prefixWord ++ tailWord_3627298).sum := by decide
  have hdescent : baseEnd_3627298 < baseStart_3627298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627322 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3627322 : Nat := 118140960795 + 3627322 * 2 ^ 59
def prefixEnd_3627322 : Nat := 4983230072969 + 3 ^ 40 * 3627322 * 2
def baseEnd_3627322 : Nat := 413902149917369404376279

theorem tailTrace_3627322 : CollatzResearch.WordTrace tailWord_3627322 prefixEnd_3627322 413902149917369404376279 := by
  unfold tailWord_3627322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074825541209841530503055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88199534776559577414674813 33074825541209841530503055)
  ·
    refine ⟨49612238311814762295754583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33074825541209841530503055 49612238311814762295754583)
    ·
      refine ⟨74418357467722143443631875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49612238311814762295754583 74418357467722143443631875)
      ·
        refine ⟨111627536201583215165447813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74418357467722143443631875 111627536201583215165447813)
        ·
          refine ⟨20930163037796852843521465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111627536201583215165447813 20930163037796852843521465)
          ·
            refine ⟨15697622278347639632641099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930163037796852843521465 15697622278347639632641099)
            ·
              refine ⟨23546433417521459448961649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697622278347639632641099 23546433417521459448961649)
              ·
                refine ⟨17659825063141094586721237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23546433417521459448961649 17659825063141094586721237)
                ·
                  refine ⟨413902149917369404376279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17659825063141094586721237 413902149917369404376279)
                  ·
                    rfl

theorem cell22_3627322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3627322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627322 prefixEnd_3627322 := by exact prefixLift 3627322
  have htrace : WordTrace (prefixWord ++ tailWord_3627322) baseStart_3627322 baseEnd_3627322 := by
    simpa [prefixWord, tailWord_3627322, baseEnd_3627322] using wordTrace_append hprefix tailTrace_3627322
  have hstable : (prefixWord ++ tailWord_3627322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627322).length < 2 ^ (prefixWord ++ tailWord_3627322).sum := by decide
  have hdescent : baseEnd_3627322 < baseStart_3627322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627394 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3627394 : Nat := 118140960795 + 3627394 * 2 ^ 59
def prefixEnd_3627394 : Nat := 4983230072969 + 3 ^ 40 * 3627394 * 2
def baseEnd_3627394 : Nat := 1241731096823524025328617

theorem tailTrace_3627394 : CollatzResearch.WordTrace tailWord_3627394 prefixEnd_3627394 1241731096823524025328617 := by
  unfold tailWord_3627394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33075482055144630604658309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88201285480385681612422157 33075482055144630604658309)
  ·
    refine ⟨6201652885339618238373433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33075482055144630604658309 6201652885339618238373433)
    ·
      refine ⟨4651239664004713678780075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201652885339618238373433 4651239664004713678780075)
      ·
        refine ⟨6976859496007070518170113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651239664004713678780075 6976859496007070518170113)
        ·
          refine ⟨5232644622005302888627585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6976859496007070518170113 5232644622005302888627585)
          ·
            refine ⟨3924483466503977166470689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232644622005302888627585 3924483466503977166470689)
            ·
              refine ⟨2943362599877982874853017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924483466503977166470689 2943362599877982874853017)
              ·
                refine ⟨2207521949908487156139763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943362599877982874853017 2207521949908487156139763)
                ·
                  refine ⟨3311282924862730734209645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207521949908487156139763 3311282924862730734209645)
                  ·
                    refine ⟨1241731096823524025328617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311282924862730734209645 1241731096823524025328617)
                    ·
                      rfl

theorem cell22_3627394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3627394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627394 prefixEnd_3627394 := by exact prefixLift 3627394
  have htrace : WordTrace (prefixWord ++ tailWord_3627394) baseStart_3627394 baseEnd_3627394 := by
    simpa [prefixWord, tailWord_3627394, baseEnd_3627394] using wordTrace_append hprefix tailTrace_3627394
  have hstable : (prefixWord ++ tailWord_3627394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627394).length < 2 ^ (prefixWord ++ tailWord_3627394).sum := by decide
  have hdescent : baseEnd_3627394 < baseStart_3627394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627397 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3627397 : Nat := 118140960795 + 3627397 * 2 ^ 59
def prefixEnd_3627397 : Nat := 4983230072969 + 3 ^ 40 * 3627397 * 2
def baseEnd_3627397 : Nat := 1241732123784833017503607

theorem tailTrace_3627397 : CollatzResearch.WordTrace tailWord_3627397 prefixEnd_3627397 1241732123784833017503607 := by
  unfold tailWord_3627397
  simp only [CollatzResearch.WordTrace]
  refine ⟨132302037639567653930992445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88201358426378435953994963 132302037639567653930992445)
  ·
    refine ⟨49613264114837870224122167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132302037639567653930992445 49613264114837870224122167)
    ·
      refine ⟨74419896172256805336183251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49613264114837870224122167 74419896172256805336183251)
      ·
        refine ⟨111629844258385208004274877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74419896172256805336183251 111629844258385208004274877)
        ·
          refine ⟨41861191596894453001603079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111629844258385208004274877 41861191596894453001603079)
          ·
            refine ⟨62791787395341679502404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41861191596894453001603079 62791787395341679502404619)
            ·
              refine ⟨94187681093012519253606929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62791787395341679502404619 94187681093012519253606929)
              ·
                refine ⟨70640760819759389440205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94187681093012519253606929 70640760819759389440205197)
                ·
                  refine ⟨26490285307409771040076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70640760819759389440205197 26490285307409771040076949)
                  ·
                    refine ⟨1241732123784833017503607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26490285307409771040076949 1241732123784833017503607)
                    ·
                      rfl

theorem cell22_3627397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3627397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627397 prefixEnd_3627397 := by exact prefixLift 3627397
  have htrace : WordTrace (prefixWord ++ tailWord_3627397) baseStart_3627397 baseEnd_3627397 := by
    simpa [prefixWord, tailWord_3627397, baseEnd_3627397] using wordTrace_append hprefix tailTrace_3627397
  have hstable : (prefixWord ++ tailWord_3627397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627397).length < 2 ^ (prefixWord ++ tailWord_3627397).sum := by decide
  have hdescent : baseEnd_3627397 < baseStart_3627397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627401 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 4]
def baseStart_3627401 : Nat := 118140960795 + 3627401 * 2 ^ 59
def prefixEnd_3627401 : Nat := 4983230072969 + 3 ^ 40 * 3627401 * 2
def baseEnd_3627401 : Nat := 413911164355526113467865

theorem tailTrace_3627401 : CollatzResearch.WordTrace tailWord_3627401 prefixEnd_3627401 413911164355526113467865 := by
  unfold tailWord_3627401
  simp only [CollatzResearch.WordTrace]
  refine ⟨132302183531553162614138057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88201455687702108409425371 132302183531553162614138057)
  ·
    refine ⟨99226637648664871960603543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132302183531553162614138057 99226637648664871960603543)
    ·
      refine ⟨148839956472997307940905315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99226637648664871960603543 148839956472997307940905315)
      ·
        refine ⟨223259934709495961911357973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148839956472997307940905315 223259934709495961911357973)
        ·
          refine ⟨10465309439507623214594905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223259934709495961911357973 10465309439507623214594905)
          ·
            refine ⟨7848982079630717410946179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465309439507623214594905 7848982079630717410946179)
            ·
              refine ⟨11773473119446076116419269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848982079630717410946179 11773473119446076116419269)
              ·
                refine ⟨2207526209896139271828613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11773473119446076116419269 2207526209896139271828613)
                ·
                  refine ⟨413911164355526113467865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207526209896139271828613 413911164355526113467865)
                  ·
                    rfl

theorem cell22_3627401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_3627401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627401 prefixEnd_3627401 := by exact prefixLift 3627401
  have htrace : WordTrace (prefixWord ++ tailWord_3627401) baseStart_3627401 baseEnd_3627401 := by
    simpa [prefixWord, tailWord_3627401, baseEnd_3627401] using wordTrace_append hprefix tailTrace_3627401
  have hstable : (prefixWord ++ tailWord_3627401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627401).length < 2 ^ (prefixWord ++ tailWord_3627401).sum := by decide
  have hdescent : baseEnd_3627401 < baseStart_3627401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627416 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_3627416 : Nat := 118140960795 + 3627416 * 2 ^ 59
def prefixEnd_3627416 : Nat := 4983230072969 + 3 ^ 40 * 3627416 * 2
def baseEnd_3627416 : Nat := 1241738627873123301278549

theorem tailTrace_3627416 : CollatzResearch.WordTrace tailWord_3627416 prefixEnd_3627416 1241738627873123301278549 := by
  unfold tailWord_3627416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66151365313249410087967051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88201820417665880117289401 66151365313249410087967051)
  ·
    refine ⟨99227047969874115131950577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66151365313249410087967051 99227047969874115131950577)
    ·
      refine ⟨74420285977405586348962933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99227047969874115131950577 74420285977405586348962933)
      ·
        refine ⟨6976901810381773720215275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74420285977405586348962933 6976901810381773720215275)
        ·
          refine ⟨10465352715572660580322913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976901810381773720215275 10465352715572660580322913)
          ·
            refine ⟨7849014536679495435242185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465352715572660580322913 7849014536679495435242185)
            ·
              refine ⟨5886760902509621576431639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7849014536679495435242185 5886760902509621576431639)
              ·
                refine ⟨8830141353764432364647459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886760902509621576431639 8830141353764432364647459)
                ·
                  refine ⟨13245212030646648546971189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830141353764432364647459 13245212030646648546971189)
                  ·
                    refine ⟨1241738627873123301278549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13245212030646648546971189 1241738627873123301278549)
                    ·
                      rfl

theorem cell22_3627416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_3627416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627416 prefixEnd_3627416 := by exact prefixLift 3627416
  have htrace : WordTrace (prefixWord ++ tailWord_3627416) baseStart_3627416 baseEnd_3627416 := by
    simpa [prefixWord, tailWord_3627416, baseEnd_3627416] using wordTrace_append hprefix tailTrace_3627416
  have hstable : (prefixWord ++ tailWord_3627416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627416).length < 2 ^ (prefixWord ++ tailWord_3627416).sum := by decide
  have hdescent : baseEnd_3627416 < baseStart_3627416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627429 : List Nat := [1, 3, 1, 2, 1, 1, 7, 6]
def baseStart_3627429 : Nat := 118140960795 + 3627429 * 2 ^ 59
def prefixEnd_3627429 : Nat := 4983230072969 + 3 ^ 40 * 3627429 * 2
def baseEnd_3627429 : Nat := 137971453115421733411501

theorem tailTrace_3627429 : CollatzResearch.WordTrace tailWord_3627429 prefixEnd_3627429 137971453115421733411501 := by
  unfold tailWord_3627429
  simp only [CollatzResearch.WordTrace]
  refine ⟨132303204775451723396157341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88202136516967815597438227 132303204775451723396157341)
  ·
    refine ⟨49613701790794396273559003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132303204775451723396157341 49613701790794396273559003)
    ·
      refine ⟨74420552686191594410338505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49613701790794396273559003 74420552686191594410338505)
      ·
        refine ⟨55815414514643695807753879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74420552686191594410338505 55815414514643695807753879)
        ·
          refine ⟨83723121771965543711630819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55815414514643695807753879 83723121771965543711630819)
          ·
            refine ⟨125584682657948315567446229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83723121771965543711630819 125584682657948315567446229)
            ·
              refine ⟨2943390999795663646112021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125584682657948315567446229 2943390999795663646112021)
              ·
                refine ⟨137971453115421733411501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2943390999795663646112021 137971453115421733411501)
                ·
                  rfl

theorem cell22_3627429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 6].length) (baseStart_3627429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627429 prefixEnd_3627429 := by exact prefixLift 3627429
  have htrace : WordTrace (prefixWord ++ tailWord_3627429) baseStart_3627429 baseEnd_3627429 := by
    simpa [prefixWord, tailWord_3627429, baseEnd_3627429] using wordTrace_append hprefix tailTrace_3627429
  have hstable : (prefixWord ++ tailWord_3627429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627429).length < 2 ^ (prefixWord ++ tailWord_3627429).sum := by decide
  have hdescent : baseEnd_3627429 < baseStart_3627429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627431 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3627431 : Nat := 118140960795 + 3627431 * 2 ^ 59
def prefixEnd_3627431 : Nat := 4983230072969 + 3 ^ 40 * 3627431 * 2
def baseEnd_3627431 : Nat := 1241743762679668262153503

theorem tailTrace_3627431 : CollatzResearch.WordTrace tailWord_3627431 prefixEnd_3627431 1241743762679668262153503 := by
  unfold tailWord_3627431
  simp only [CollatzResearch.WordTrace]
  refine ⟨132303277721444477737730147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88202185147629651825153431 132303277721444477737730147)
  ·
    refine ⟨198454916582166716606595221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132303277721444477737730147 198454916582166716606595221)
    ·
      refine ⟨9302574214789064840934151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198454916582166716606595221 9302574214789064840934151)
      ·
        refine ⟨13953861322183597261401227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302574214789064840934151 13953861322183597261401227)
        ·
          refine ⟨20930791983275395892101841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953861322183597261401227 20930791983275395892101841)
          ·
            refine ⟨15698093987456546919076381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930791983275395892101841 15698093987456546919076381)
            ·
              refine ⟨5886785245296205094653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15698093987456546919076381 5886785245296205094653643)
              ·
                refine ⟨8830177867944307641980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886785245296205094653643 8830177867944307641980465)
                ·
                  refine ⟨6622633400958230731485349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830177867944307641980465 6622633400958230731485349)
                  ·
                    refine ⟨1241743762679668262153503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622633400958230731485349 1241743762679668262153503)
                    ·
                      rfl

theorem cell22_3627431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3627431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627431 prefixEnd_3627431 := by exact prefixLift 3627431
  have htrace : WordTrace (prefixWord ++ tailWord_3627431) baseStart_3627431 baseEnd_3627431 := by
    simpa [prefixWord, tailWord_3627431, baseEnd_3627431] using wordTrace_append hprefix tailTrace_3627431
  have hstable : (prefixWord ++ tailWord_3627431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627431).length < 2 ^ (prefixWord ++ tailWord_3627431).sum := by decide
  have hdescent : baseEnd_3627431 < baseStart_3627431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627437 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3627437 : Nat := 118140960795 + 3627437 * 2 ^ 59
def prefixEnd_3627437 : Nat := 4983230072969 + 3 ^ 40 * 3627437 * 2
def baseEnd_3627437 : Nat := 1241745816602286246503485

theorem tailTrace_3627437 : CollatzResearch.WordTrace tailWord_3627437 prefixEnd_3627437 1241745816602286246503485 := by
  unfold tailWord_3627437
  simp only [CollatzResearch.WordTrace]
  refine ⟨132303496559422740762448565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88202331039615160508299043 132303496559422740762448565)
  ·
    refine ⟨12403452802445881946479553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132303496559422740762448565 12403452802445881946479553)
    ·
      refine ⟨9302589601834411459859665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12403452802445881946479553 9302589601834411459859665)
      ·
        refine ⟨6976942201375808594894749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9302589601834411459859665 6976942201375808594894749)
        ·
          refine ⟨2616353325515928223085531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6976942201375808594894749 2616353325515928223085531)
          ·
            refine ⟨3924529988273892334628297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616353325515928223085531 3924529988273892334628297)
            ·
              refine ⟨2943397491205419250971223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924529988273892334628297 2943397491205419250971223)
              ·
                refine ⟨4415096236808128876456835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943397491205419250971223 4415096236808128876456835)
                ·
                  refine ⟨6622644355212193314685253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415096236808128876456835 6622644355212193314685253)
                  ·
                    refine ⟨1241745816602286246503485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622644355212193314685253 1241745816602286246503485)
                    ·
                      rfl

theorem cell22_3627437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3627437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627437 prefixEnd_3627437 := by exact prefixLift 3627437
  have htrace : WordTrace (prefixWord ++ tailWord_3627437) baseStart_3627437 baseEnd_3627437 := by
    simpa [prefixWord, tailWord_3627437, baseEnd_3627437] using wordTrace_append hprefix tailTrace_3627437
  have hstable : (prefixWord ++ tailWord_3627437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627437).length < 2 ^ (prefixWord ++ tailWord_3627437).sum := by decide
  have hdescent : baseEnd_3627437 < baseStart_3627437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627478 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3627478 : Nat := 118140960795 + 3627478 * 2 ^ 59
def prefixEnd_3627478 : Nat := 4983230072969 + 3 ^ 40 * 3627478 * 2
def baseEnd_3627478 : Nat := 1241759851740175806228359

theorem tailTrace_3627478 : CollatzResearch.WordTrace tailWord_3627478 prefixEnd_3627478 1241759851740175806228359 := by
  unfold tailWord_3627478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269061997017137797793193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88203327968182803176460725 8269061997017137797793193)
  ·
    refine ⟨6201796497762853348344895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8269061997017137797793193 6201796497762853348344895)
    ·
      refine ⟨9302694746644280022517343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201796497762853348344895 9302694746644280022517343)
      ·
        refine ⟨13954042119966420033776015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302694746644280022517343 13954042119966420033776015)
        ·
          refine ⟨20931063179949630050664023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954042119966420033776015 20931063179949630050664023)
          ·
            refine ⟨31396594769924445075996035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20931063179949630050664023 31396594769924445075996035)
            ·
              refine ⟨47094892154886667613994053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31396594769924445075996035 47094892154886667613994053)
              ·
                refine ⟨8830292279041250177623885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47094892154886667613994053 8830292279041250177623885)
                ·
                  refine ⟨3311359604640468816608957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830292279041250177623885 3311359604640468816608957)
                  ·
                    refine ⟨1241759851740175806228359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311359604640468816608957 1241759851740175806228359)
                    ·
                      rfl

theorem cell22_3627478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3627478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627478 prefixEnd_3627478 := by exact prefixLift 3627478
  have htrace : WordTrace (prefixWord ++ tailWord_3627478) baseStart_3627478 baseEnd_3627478 := by
    simpa [prefixWord, tailWord_3627478, baseEnd_3627478] using wordTrace_append hprefix tailTrace_3627478
  have hstable : (prefixWord ++ tailWord_3627478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627478).length < 2 ^ (prefixWord ++ tailWord_3627478).sum := by decide
  have hdescent : baseEnd_3627478 < baseStart_3627478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627581 : List Nat := [1, 4, 1, 3, 2, 1, 3, 7]
def baseStart_3627581 : Nat := 118140960795 + 3627581 * 2 ^ 59
def prefixEnd_3627581 : Nat := 4983230072969 + 3 ^ 40 * 3627581 * 2
def baseEnd_3627581 : Nat := 137977234527235318989227

theorem tailTrace_3627581 : CollatzResearch.WordTrace tailWord_3627581 prefixEnd_3627581 137977234527235318989227 := by
  unfold tailWord_3627581
  simp only [CollatzResearch.WordTrace]
  refine ⟨132308748670901053355690597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88205832447267368903793731 132308748670901053355690597)
  ·
    refine ⟨24807890375793947504191987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132308748670901053355690597 24807890375793947504191987)
    ·
      refine ⟨37211835563690921256287981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24807890375793947504191987 37211835563690921256287981)
      ·
        refine ⟨13954438336384095471107993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37211835563690921256287981 13954438336384095471107993)
        ·
          refine ⟨10465828752288071603330995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13954438336384095471107993 10465828752288071603330995)
          ·
            refine ⟨15698743128432107404996493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465828752288071603330995 15698743128432107404996493)
            ·
              refine ⟨5887028673162040276873685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15698743128432107404996493 5887028673162040276873685)
              ·
                refine ⟨137977234527235318989227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5887028673162040276873685 137977234527235318989227)
                ·
                  rfl

theorem cell22_3627581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 7].length) (baseStart_3627581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627581 prefixEnd_3627581 := by exact prefixLift 3627581
  have htrace : WordTrace (prefixWord ++ tailWord_3627581) baseStart_3627581 baseEnd_3627581 := by
    simpa [prefixWord, tailWord_3627581, baseEnd_3627581] using wordTrace_append hprefix tailTrace_3627581
  have hstable : (prefixWord ++ tailWord_3627581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627581).length < 2 ^ (prefixWord ++ tailWord_3627581).sum := by decide
  have hdescent : baseEnd_3627581 < baseStart_3627581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627626 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_3627626 : Nat := 118140960795 + 3627626 * 2 ^ 59
def prefixEnd_3627626 : Nat := 4983230072969 + 3 ^ 40 * 3627626 * 2
def baseEnd_3627626 : Nat := 413936838388250917842635

theorem tailTrace_3627626 : CollatzResearch.WordTrace tailWord_3627626 prefixEnd_3627626 413936838388250917842635 := by
  unfold tailWord_3627626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077597488934506510269683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88206926637158684027385821 33077597488934506510269683)
  ·
    refine ⟨49616396233401759765404525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077597488934506510269683 49616396233401759765404525)
    ·
      refine ⟨18606148587525659912026697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49616396233401759765404525 18606148587525659912026697)
      ·
        refine ⟨13954611440644244934020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606148587525659912026697 13954611440644244934020023)
        ·
          refine ⟨20931917160966367401030035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954611440644244934020023 20931917160966367401030035)
          ·
            refine ⟨31397875741449551101545053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20931917160966367401030035 31397875741449551101545053)
            ·
              refine ⟨11774203403043581663079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31397875741449551101545053 11774203403043581663079395)
              ·
                refine ⟨17661305104565372494619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774203403043581663079395 17661305104565372494619093)
                ·
                  refine ⟨413936838388250917842635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17661305104565372494619093 413936838388250917842635)
                  ·
                    rfl

theorem cell22_3627626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_3627626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627626 prefixEnd_3627626 := by exact prefixLift 3627626
  have htrace : WordTrace (prefixWord ++ tailWord_3627626) baseStart_3627626 baseEnd_3627626 := by
    simpa [prefixWord, tailWord_3627626, baseEnd_3627626] using wordTrace_append hprefix tailTrace_3627626
  have hstable : (prefixWord ++ tailWord_3627626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627626).length < 2 ^ (prefixWord ++ tailWord_3627626).sum := by decide
  have hdescent : baseEnd_3627626 < baseStart_3627626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627630 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3627630 : Nat := 118140960795 + 3627630 * 2 ^ 59
def prefixEnd_3627630 : Nat := 4983230072969 + 3 ^ 40 * 3627630 * 2
def baseEnd_3627630 : Nat := 1241811884446498076427893

theorem tailTrace_3627630 : CollatzResearch.WordTrace tailWord_3627630 prefixEnd_3627630 1241811884446498076427893 := by
  unfold tailWord_3627630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16538816980965441840528043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88207023898482356482816229 16538816980965441840528043)
  ·
    refine ⟨24808225471448162760792065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16538816980965441840528043 24808225471448162760792065)
    ·
      refine ⟨18606169103586122070594049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24808225471448162760792065 18606169103586122070594049)
      ·
        refine ⟨13954626827689591552945537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606169103586122070594049 13954626827689591552945537)
        ·
          refine ⟨10465970120767193664709153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13954626827689591552945537 10465970120767193664709153)
          ·
            refine ⟨7849477590575395248531865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465970120767193664709153 7849477590575395248531865)
            ·
              refine ⟨5887108192931546436398899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7849477590575395248531865 5887108192931546436398899)
              ·
                refine ⟨8830662289397319654598349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887108192931546436398899 8830662289397319654598349)
                ·
                  refine ⟨3311498358523994870474381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830662289397319654598349 3311498358523994870474381)
                  ·
                    refine ⟨1241811884446498076427893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311498358523994870474381 1241811884446498076427893)
                    ·
                      rfl

theorem cell22_3627630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3627630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627630 prefixEnd_3627630 := by exact prefixLift 3627630
  have htrace : WordTrace (prefixWord ++ tailWord_3627630) baseStart_3627630 baseEnd_3627630 := by
    simpa [prefixWord, tailWord_3627630, baseEnd_3627630] using wordTrace_append hprefix tailTrace_3627630
  have hstable : (prefixWord ++ tailWord_3627630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627630).length < 2 ^ (prefixWord ++ tailWord_3627630).sum := by decide
  have hdescent : baseEnd_3627630 < baseStart_3627630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627641 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_3627641 : Nat := 118140960795 + 3627641 * 2 ^ 59
def prefixEnd_3627641 : Nat := 4983230072969 + 3 ^ 40 * 3627641 * 2
def baseEnd_3627641 : Nat := 1241815649971297714402859

theorem tailTrace_3627641 : CollatzResearch.WordTrace tailWord_3627641 prefixEnd_3627641 1241815649971297714402859 := by
  unfold tailWord_3627641
  simp only [CollatzResearch.WordTrace]
  refine ⟨132310937050683683602874777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88207291367122455735249851 132310937050683683602874777)
  ·
    refine ⟨99233202788012762702156083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132310937050683683602874777 99233202788012762702156083)
    ·
      refine ⟨148849804182019144053234125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99233202788012762702156083 148849804182019144053234125)
      ·
        refine ⟨55818676568257179019962797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148849804182019144053234125 55818676568257179019962797)
        ·
          refine ⟨20932003713096442132486049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55818676568257179019962797 20932003713096442132486049)
          ·
            refine ⟨15699002784822331599364537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20932003713096442132486049 15699002784822331599364537)
            ·
              refine ⟨11774252088616748699523403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15699002784822331599364537 11774252088616748699523403)
              ·
                refine ⟨17661378132925123049285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774252088616748699523403 17661378132925123049285105)
                ·
                  refine ⟨13246033599693842286963829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17661378132925123049285105 13246033599693842286963829)
                  ·
                    refine ⟨1241815649971297714402859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13246033599693842286963829 1241815649971297714402859)
                    ·
                      rfl

theorem cell22_3627641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_3627641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627641 prefixEnd_3627641 := by exact prefixLift 3627641
  have htrace : WordTrace (prefixWord ++ tailWord_3627641) baseStart_3627641 baseEnd_3627641 := by
    simpa [prefixWord, tailWord_3627641, baseEnd_3627641] using wordTrace_append hprefix tailTrace_3627641
  have hstable : (prefixWord ++ tailWord_3627641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627641).length < 2 ^ (prefixWord ++ tailWord_3627641).sum := by decide
  have hdescent : baseEnd_3627641 < baseStart_3627641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627733 : List Nat := [1, 3, 2, 5, 1, 10]
def baseStart_3627733 : Nat := 118140960795 + 3627733 * 2 ^ 59
def prefixEnd_3627733 : Nat := 4983230072969 + 3 ^ 40 * 3627733 * 2
def baseEnd_3627733 : Nat := 15331446215449878285217

theorem tailTrace_3627733 : CollatzResearch.WordTrace tailWord_3627733 prefixEnd_3627733 15331446215449878285217 := by
  unfold tailWord_3627733
  simp only [CollatzResearch.WordTrace]
  refine ⟨132314292566350383315223853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88209528377566922210149235 132314292566350383315223853)
  ·
    refine ⟨49617859712381393743208945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132314292566350383315223853 49617859712381393743208945)
    ·
      refine ⟨37213394784286045307406709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49617859712381393743208945 37213394784286045307406709)
      ·
        refine ⟨3488755761026816747569379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37213394784286045307406709 3488755761026816747569379)
        ·
          refine ⟨5233133641540225121354069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488755761026816747569379 5233133641540225121354069)
          ·
            refine ⟨15331446215449878285217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5233133641540225121354069 15331446215449878285217)
            ·
              rfl

theorem cell22_3627733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 10].length) (baseStart_3627733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627733 prefixEnd_3627733 := by exact prefixLift 3627733
  have htrace : WordTrace (prefixWord ++ tailWord_3627733) baseStart_3627733 baseEnd_3627733 := by
    simpa [prefixWord, tailWord_3627733, baseEnd_3627733] using wordTrace_append hprefix tailTrace_3627733
  have hstable : (prefixWord ++ tailWord_3627733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627733).length < 2 ^ (prefixWord ++ tailWord_3627733).sum := by decide
  have hdescent : baseEnd_3627733 < baseStart_3627733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627776 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_3627776 : Nat := 118140960795 + 3627776 * 2 ^ 59
def prefixEnd_3627776 : Nat := 4983230072969 + 3 ^ 40 * 3627776 * 2
def baseEnd_3627776 : Nat := 1241861863230202362277445

theorem tailTrace_3627776 : CollatzResearch.WordTrace tailWord_3627776 prefixEnd_3627776 1241861863230202362277445 := by
  unfold tailWord_3627776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66157930452597300829519591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88210573936796401106026121 66157930452597300829519591)
  ·
    refine ⟨99236895678895951244279387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66157930452597300829519591 99236895678895951244279387)
    ·
      refine ⟨148855343518343926866419081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99236895678895951244279387 148855343518343926866419081)
      ·
        refine ⟨111641507638757945149814311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148855343518343926866419081 111641507638757945149814311)
        ·
          refine ⟨167462261458136917724721467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111641507638757945149814311 167462261458136917724721467)
          ·
            refine ⟨251193392187205376587082201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167462261458136917724721467 251193392187205376587082201)
            ·
              refine ⟨188395044140404032440311651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251193392187205376587082201 188395044140404032440311651)
              ·
                refine ⟨282592566210606048660467477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188395044140404032440311651 282592566210606048660467477)
                ·
                  refine ⟨13246526541122158530959413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282592566210606048660467477 13246526541122158530959413)
                  ·
                    refine ⟨1241861863230202362277445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13246526541122158530959413 1241861863230202362277445)
                    ·
                      rfl

theorem cell22_3627776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_3627776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627776 prefixEnd_3627776 := by exact prefixLift 3627776
  have htrace : WordTrace (prefixWord ++ tailWord_3627776) baseStart_3627776 baseEnd_3627776 := by
    simpa [prefixWord, tailWord_3627776, baseEnd_3627776] using wordTrace_append hprefix tailTrace_3627776
  have hstable : (prefixWord ++ tailWord_3627776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627776).length < 2 ^ (prefixWord ++ tailWord_3627776).sum := by decide
  have hdescent : baseEnd_3627776 < baseStart_3627776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627812 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_3627812 : Nat := 118140960795 + 3627812 * 2 ^ 59
def prefixEnd_3627812 : Nat := 4983230072969 + 3 ^ 40 * 3627812 * 2
def baseEnd_3627812 : Nat := 413958062255303422792445

theorem tailTrace_3627812 : CollatzResearch.WordTrace tailWord_3627812 prefixEnd_3627812 413958062255303422792445 := by
  unfold tailWord_3627812
  simp only [CollatzResearch.WordTrace]
  refine ⟨66158586966532089903674845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88211449288709453204899793 66158586966532089903674845)
  ·
    refine ⟨24809470112449533713878067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66158586966532089903674845 24809470112449533713878067)
    ·
      refine ⟨37214205168674300570817101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24809470112449533713878067 37214205168674300570817101)
      ·
        refine ⟨13955326938252862714056413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37214205168674300570817101 13955326938252862714056413)
        ·
          refine ⟨5233247601844823517771155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13955326938252862714056413 5233247601844823517771155)
          ·
            refine ⟨7849871402767235276656733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233247601844823517771155 7849871402767235276656733)
            ·
              refine ⟨2943701776037713228746275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7849871402767235276656733 2943701776037713228746275)
              ·
                refine ⟨4415552664056569843119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943701776037713228746275 4415552664056569843119413)
                ·
                  refine ⟨413958062255303422792445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4415552664056569843119413 413958062255303422792445)
                  ·
                    rfl

theorem cell22_3627812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_3627812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627812 prefixEnd_3627812 := by exact prefixLift 3627812
  have htrace : WordTrace (prefixWord ++ tailWord_3627812) baseStart_3627812 baseEnd_3627812 := by
    simpa [prefixWord, tailWord_3627812, baseEnd_3627812] using wordTrace_append hprefix tailTrace_3627812
  have hstable : (prefixWord ++ tailWord_3627812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627812).length < 2 ^ (prefixWord ++ tailWord_3627812).sum := by decide
  have hdescent : baseEnd_3627812 < baseStart_3627812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627825 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3627825 : Nat := 118140960795 + 3627825 * 2 ^ 59
def prefixEnd_3627825 : Nat := 4983230072969 + 3 ^ 40 * 3627825 * 2
def baseEnd_3627825 : Nat := 1241878636931582567802295

theorem tailTrace_3627825 : CollatzResearch.WordTrace tailWord_3627825 prefixEnd_3627825 1241878636931582567802295 := by
  unfold tailWord_3627825
  simp only [CollatzResearch.WordTrace]
  refine ⟨132317648082017083027572929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88211765388011388685048619 132317648082017083027572929)
  ·
    refine ⟨99238236061512812270679697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132317648082017083027572929 99238236061512812270679697)
    ·
      refine ⟨74428677046134609203009773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99238236061512812270679697 74428677046134609203009773)
      ·
        refine ⟨27910753892300478451128665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74428677046134609203009773 27910753892300478451128665)
        ·
          refine ⟨20933065419225358838346499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27910753892300478451128665 20933065419225358838346499)
          ·
            refine ⟨31399598128838038257519749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20933065419225358838346499 31399598128838038257519749)
            ·
              refine ⟨5887424649157132173284953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31399598128838038257519749 5887424649157132173284953)
              ·
                refine ⟨4415568486867849129963715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887424649157132173284953 4415568486867849129963715)
                ·
                  refine ⟨6623352730301773694945573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415568486867849129963715 6623352730301773694945573)
                  ·
                    refine ⟨1241878636931582567802295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6623352730301773694945573 1241878636931582567802295)
                    ·
                      rfl

theorem cell22_3627825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3627825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627825 prefixEnd_3627825 := by exact prefixLift 3627825
  have htrace : WordTrace (prefixWord ++ tailWord_3627825) baseStart_3627825 baseEnd_3627825 := by
    simpa [prefixWord, tailWord_3627825, baseEnd_3627825] using wordTrace_append hprefix tailTrace_3627825
  have hstable : (prefixWord ++ tailWord_3627825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627825).length < 2 ^ (prefixWord ++ tailWord_3627825).sum := by decide
  have hdescent : baseEnd_3627825 < baseStart_3627825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627857 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 6]
def baseStart_3627857 : Nat := 118140960795 + 3627857 * 2 ^ 59
def prefixEnd_3627857 : Nat := 4983230072969 + 3 ^ 40 * 3627857 * 2
def baseEnd_3627857 : Nat := 413963197061848383667399

theorem tailTrace_3627857 : CollatzResearch.WordTrace tailWord_3627857 prefixEnd_3627857 413963197061848383667399 := by
  unfold tailWord_3627857
  simp only [CollatzResearch.WordTrace]
  refine ⟨132318815217901152492737825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88212543478600768328491883 132318815217901152492737825)
  ·
    refine ⟨99239111413425864369553369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132318815217901152492737825 99239111413425864369553369)
    ·
      refine ⟨74429333560069398277165027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99239111413425864369553369 74429333560069398277165027)
      ·
        refine ⟨111644000340104097415747541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74429333560069398277165027 111644000340104097415747541)
        ·
          refine ⟨2616656257971189783181583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 111644000340104097415747541 2616656257971189783181583)
          ·
            refine ⟨3924984386956784674772375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616656257971189783181583 3924984386956784674772375)
            ·
              refine ⟨5887476580435177012158563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924984386956784674772375 5887476580435177012158563)
              ·
                refine ⟨8831214870652765518237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887476580435177012158563 8831214870652765518237845)
                ·
                  refine ⟨413963197061848383667399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8831214870652765518237845 413963197061848383667399)
                  ·
                    rfl

theorem cell22_3627857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_3627857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627857 prefixEnd_3627857 := by exact prefixLift 3627857
  have htrace : WordTrace (prefixWord ++ tailWord_3627857) baseStart_3627857 baseEnd_3627857 := by
    simpa [prefixWord, tailWord_3627857, baseEnd_3627857] using wordTrace_append hprefix tailTrace_3627857
  have hstable : (prefixWord ++ tailWord_3627857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627857).length < 2 ^ (prefixWord ++ tailWord_3627857).sum := by decide
  have hdescent : baseEnd_3627857 < baseStart_3627857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627902 : List Nat := [4, 2, 3, 1, 3, 9]
def baseStart_3627902 : Nat := 118140960795 + 3627902 * 2 ^ 59
def prefixEnd_3627902 : Nat := 4983230072969 + 3 ^ 40 * 3627902 * 2
def baseEnd_3627902 : Nat := 15332160439570123871939

theorem tailTrace_3627902 : CollatzResearch.WordTrace tailWord_3627902 prefixEnd_3627902 15332160439570123871939 := by
  unfold tailWord_3627902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540057062842265647265745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88213637668492083452083973 16540057062842265647265745)
  ·
    refine ⟨12405042797131699235449309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16540057062842265647265745 12405042797131699235449309)
    ·
      refine ⟨4651891048924387213293491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12405042797131699235449309 4651891048924387213293491)
      ·
        refine ⟨6977836573386580819940237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651891048924387213293491 6977836573386580819940237)
        ·
          refine ⟨2616688715019967807477589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6977836573386580819940237 2616688715019967807477589)
          ·
            refine ⟨15332160439570123871939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2616688715019967807477589 15332160439570123871939)
            ·
              rfl

theorem cell22_3627902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 9].length) (baseStart_3627902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3627902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3627902 prefixEnd_3627902 := by exact prefixLift 3627902
  have htrace : WordTrace (prefixWord ++ tailWord_3627902) baseStart_3627902 baseEnd_3627902 := by
    simpa [prefixWord, tailWord_3627902, baseEnd_3627902] using wordTrace_append hprefix tailTrace_3627902
  have hstable : (prefixWord ++ tailWord_3627902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627902).length < 2 ^ (prefixWord ++ tailWord_3627902).sum := by decide
  have hdescent : baseEnd_3627902 < baseStart_3627902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628007 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3628007 : Nat := 118140960795 + 3628007 * 2 ^ 59
def prefixEnd_3628007 : Nat := 4983230072969 + 3 ^ 40 * 3628007 * 2
def baseEnd_3628007 : Nat := 1241940939250994759751737

theorem tailTrace_3628007 : CollatzResearch.WordTrace tailWord_3628007 prefixEnd_3628007 1241940939250994759751737 := by
  unfold tailWord_3628007
  simp only [CollatzResearch.WordTrace]
  refine ⟨132324286167357728110698275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88216190778238485407132183 132324286167357728110698275)
  ·
    refine ⟨198486429251036592166047413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132324286167357728110698275 198486429251036592166047413)
    ·
      refine ⟨18608102742284680515566945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198486429251036592166047413 18608102742284680515566945)
      ·
        refine ⟨13956077056713510386675209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18608102742284680515566945 13956077056713510386675209)
        ·
          refine ⟨10467057792535132790006407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13956077056713510386675209 10467057792535132790006407)
          ·
            refine ⟨15700586688802699185009611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467057792535132790006407 15700586688802699185009611)
            ·
              refine ⟨23550880033204048777514417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700586688802699185009611 23550880033204048777514417)
              ·
                refine ⟨17663160024903036583135813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23550880033204048777514417 17663160024903036583135813)
                ·
                  refine ⟨3311842504669319359337965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17663160024903036583135813 3311842504669319359337965)
                  ·
                    refine ⟨1241940939250994759751737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311842504669319359337965 1241940939250994759751737)
                    ·
                      rfl

theorem cell22_3628007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3628007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628007 prefixEnd_3628007 := by exact prefixLift 3628007
  have htrace : WordTrace (prefixWord ++ tailWord_3628007) baseStart_3628007 baseEnd_3628007 := by
    simpa [prefixWord, tailWord_3628007, baseEnd_3628007] using wordTrace_append hprefix tailTrace_3628007
  have hstable : (prefixWord ++ tailWord_3628007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628007).length < 2 ^ (prefixWord ++ tailWord_3628007).sum := by decide
  have hdescent : baseEnd_3628007 < baseStart_3628007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628022 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3628022 : Nat := 118140960795 + 3628022 * 2 ^ 59
def prefixEnd_3628022 : Nat := 4983230072969 + 3 ^ 40 * 3628022 * 2
def baseEnd_3628022 : Nat := 1241946074057539720626691

theorem tailTrace_3628022 : CollatzResearch.WordTrace tailWord_3628022 prefixEnd_3628022 1241946074057539720626691 := by
  unfold tailWord_3628022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270302078893961604530895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88216555508202257114996213 8270302078893961604530895)
  ·
    refine ⟨12405453118340942406796343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8270302078893961604530895 12405453118340942406796343)
    ·
      refine ⟨18608179677511413610194515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405453118340942406796343 18608179677511413610194515)
      ·
        refine ⟨27912269516267120415291773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18608179677511413610194515 27912269516267120415291773)
        ·
          refine ⟨10467101068600170155734415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27912269516267120415291773 10467101068600170155734415)
          ·
            refine ⟨15700651602900255233601623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467101068600170155734415 15700651602900255233601623)
            ·
              refine ⟨23550977404350382850402435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700651602900255233601623 23550977404350382850402435)
              ·
                refine ⟨35326466106525574275603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23550977404350382850402435 35326466106525574275603653)
                ·
                  refine ⟨6623712394973545176675685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35326466106525574275603653 6623712394973545176675685)
                  ·
                    refine ⟨1241946074057539720626691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6623712394973545176675685 1241946074057539720626691)
                    ·
                      rfl

theorem cell22_3628022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3628022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628022 prefixEnd_3628022 := by exact prefixLift 3628022
  have htrace : WordTrace (prefixWord ++ tailWord_3628022) baseStart_3628022 baseEnd_3628022 := by
    simpa [prefixWord, tailWord_3628022, baseEnd_3628022] using wordTrace_append hprefix tailTrace_3628022
  have hstable : (prefixWord ++ tailWord_3628022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628022).length < 2 ^ (prefixWord ++ tailWord_3628022).sum := by decide
  have hdescent : baseEnd_3628022 < baseStart_3628022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628069 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_3628069 : Nat := 118140960795 + 3628069 * 2 ^ 59
def prefixEnd_3628069 : Nat := 4983230072969 + 3 ^ 40 * 3628069 * 2
def baseEnd_3628069 : Nat := 1241962163118047264701547

theorem tailTrace_3628069 : CollatzResearch.WordTrace tailWord_3628069 prefixEnd_3628069 1241962163118047264701547 := by
  unfold tailWord_3628069
  simp only [CollatzResearch.WordTrace]
  refine ⟨132326547493133112699455261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88217698328755408466303507 132326547493133112699455261)
  ·
    refine ⟨49622455309924917262295723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132326547493133112699455261 49622455309924917262295723)
    ·
      refine ⟨74433682964887375893443585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49622455309924917262295723 74433682964887375893443585)
      ·
        refine ⟨55825262223665531920082689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74433682964887375893443585 55825262223665531920082689)
        ·
          refine ⟨41868946667749148940062017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55825262223665531920082689 41868946667749148940062017)
          ·
            refine ⟨31401710000811861705046513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41868946667749148940062017 31401710000811861705046513)
            ·
              refine ⟨23551282500608896278784885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31401710000811861705046513 23551282500608896278784885)
              ·
                refine ⟨2207932734432084026136083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23551282500608896278784885 2207932734432084026136083)
                ·
                  refine ⟨3311899101648126039204125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207932734432084026136083 3311899101648126039204125)
                  ·
                    refine ⟨1241962163118047264701547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311899101648126039204125 1241962163118047264701547)
                    ·
                      rfl

theorem cell22_3628069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_3628069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628069 prefixEnd_3628069 := by exact prefixLift 3628069
  have htrace : WordTrace (prefixWord ++ tailWord_3628069) baseStart_3628069 baseEnd_3628069 := by
    simpa [prefixWord, tailWord_3628069, baseEnd_3628069] using wordTrace_append hprefix tailTrace_3628069
  have hstable : (prefixWord ++ tailWord_3628069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628069).length < 2 ^ (prefixWord ++ tailWord_3628069).sum := by decide
  have hdescent : baseEnd_3628069 < baseStart_3628069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628080 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_3628080 : Nat := 118140960795 + 3628080 * 2 ^ 59
def prefixEnd_3628080 : Nat := 4983230072969 + 3 ^ 40 * 3628080 * 2
def baseEnd_3628080 : Nat := 1241965928642846902676513

theorem tailTrace_3628080 : CollatzResearch.WordTrace tailWord_3628080 prefixEnd_3628080 1241965928642846902676513 := by
  unfold tailWord_3628080
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163474348046630789052847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88217965797395507718737129 66163474348046630789052847)
  ·
    refine ⟨99245211522069946183579271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66163474348046630789052847 99245211522069946183579271)
    ·
      refine ⟨148867817283104919275368907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99245211522069946183579271 148867817283104919275368907)
      ·
        refine ⟨223301725924657378913053361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148867817283104919275368907 223301725924657378913053361)
        ·
          refine ⟨167476294443493034184790021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223301725924657378913053361 167476294443493034184790021)
          ·
            refine ⟨31401805208154943909648129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167476294443493034184790021 31401805208154943909648129)
            ·
              refine ⟨23551353906116207932236097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31401805208154943909648129 23551353906116207932236097)
              ·
                refine ⟨17663515429587155949177073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23551353906116207932236097 17663515429587155949177073)
                ·
                  refine ⟨13247636572190366961882805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17663515429587155949177073 13247636572190366961882805)
                  ·
                    refine ⟨1241965928642846902676513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13247636572190366961882805 1241965928642846902676513)
                    ·
                      rfl

theorem cell22_3628080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_3628080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628080 prefixEnd_3628080 := by exact prefixLift 3628080
  have htrace : WordTrace (prefixWord ++ tailWord_3628080) baseStart_3628080 baseEnd_3628080 := by
    simpa [prefixWord, tailWord_3628080, baseEnd_3628080] using wordTrace_append hprefix tailTrace_3628080
  have hstable : (prefixWord ++ tailWord_3628080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628080).length < 2 ^ (prefixWord ++ tailWord_3628080).sum := by decide
  have hdescent : baseEnd_3628080 < baseStart_3628080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628082 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_3628082 : Nat := 118140960795 + 3628082 * 2 ^ 59
def prefixEnd_3628082 : Nat := 4983230072969 + 3 ^ 40 * 3628082 * 2
def baseEnd_3628082 : Nat := 413988871094573188042169

theorem tailTrace_3628082 : CollatzResearch.WordTrace tailWord_3628082 prefixEnd_3628082 413988871094573188042169 := by
  unfold tailWord_3628082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33081755410521503979919625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88218014428057343946452333 33081755410521503979919625)
  ·
    refine ⟨24811316557891127984939719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33081755410521503979919625 24811316557891127984939719)
    ·
      refine ⟨37216974836836691977409579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24811316557891127984939719 37216974836836691977409579)
      ·
        refine ⟨55825462255255037966114369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37216974836836691977409579 55825462255255037966114369)
        ·
          refine ⟨41869096691441278474585777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55825462255255037966114369 41869096691441278474585777)
          ·
            refine ⟨31401822518580958855939333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41869096691441278474585777 31401822518580958855939333)
            ·
              refine ⟨5887841722233929785488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31401822518580958855939333 5887841722233929785488625)
              ·
                refine ⟨4415881291675447339116469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887841722233929785488625 4415881291675447339116469)
                ·
                  refine ⟨413988871094573188042169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4415881291675447339116469 413988871094573188042169)
                  ·
                    rfl

theorem cell22_3628082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_3628082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628082 prefixEnd_3628082 := by exact prefixLift 3628082
  have htrace : WordTrace (prefixWord ++ tailWord_3628082) baseStart_3628082 baseEnd_3628082 := by
    simpa [prefixWord, tailWord_3628082, baseEnd_3628082] using wordTrace_append hprefix tailTrace_3628082
  have hstable : (prefixWord ++ tailWord_3628082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628082).length < 2 ^ (prefixWord ++ tailWord_3628082).sum := by decide
  have hdescent : baseEnd_3628082 < baseStart_3628082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628129 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3628129 : Nat := 118140960795 + 3628129 * 2 ^ 59
def prefixEnd_3628129 : Nat := 4983230072969 + 3 ^ 40 * 3628129 * 2
def baseEnd_3628129 : Nat := 1241982702344227108201363

theorem tailTrace_3628129 : CollatzResearch.WordTrace tailWord_3628129 prefixEnd_3628129 1241982702344227108201363 := by
  unfold tailWord_3628129
  simp only [CollatzResearch.WordTrace]
  refine ⟨132328735872915742946639441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88219157248610495297759627 132328735872915742946639441)
  ·
    refine ⟨99246551904686807209979581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132328735872915742946639441 99246551904686807209979581)
    ·
      refine ⟨37217456964257552703742343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99246551904686807209979581 37217456964257552703742343)
      ·
        refine ⟨55826185446386329055613515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37217456964257552703742343 55826185446386329055613515)
        ·
          refine ⟨83739278169579493583420273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55826185446386329055613515 83739278169579493583420273)
          ·
            refine ⟨62804458627184620187565205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83739278169579493583420273 62804458627184620187565205)
            ·
              refine ⟨2943958998149279071292119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62804458627184620187565205 2943958998149279071292119)
              ·
                refine ⟨4415938497223918606938179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943958998149279071292119 4415938497223918606938179)
                ·
                  refine ⟨6623907745835877910407269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415938497223918606938179 6623907745835877910407269)
                  ·
                    refine ⟨1241982702344227108201363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6623907745835877910407269 1241982702344227108201363)
                    ·
                      rfl

theorem cell22_3628129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3628129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628129 prefixEnd_3628129 := by exact prefixLift 3628129
  have htrace : WordTrace (prefixWord ++ tailWord_3628129) baseStart_3628129 baseEnd_3628129 := by
    simpa [prefixWord, tailWord_3628129, baseEnd_3628129] using wordTrace_append hprefix tailTrace_3628129
  have hstable : (prefixWord ++ tailWord_3628129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628129).length < 2 ^ (prefixWord ++ tailWord_3628129).sum := by decide
  have hdescent : baseEnd_3628129 < baseStart_3628129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628185 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3628185 : Nat := 118140960795 + 3628185 * 2 ^ 59
def prefixEnd_3628185 : Nat := 4983230072969 + 3 ^ 40 * 3628185 * 2
def baseEnd_3628185 : Nat := 1242001872288661628801191

theorem tailTrace_3628185 : CollatzResearch.WordTrace tailWord_3628185 prefixEnd_3628185 1242001872288661628801191 := by
  unfold tailWord_3628185
  simp only [CollatzResearch.WordTrace]
  refine ⟨132330778360712864510678009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88220518907141909673785339 132330778360712864510678009)
  ·
    refine ⟨99248083770534648383008507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132330778360712864510678009 99248083770534648383008507)
    ·
      refine ⟨148872125655801972574512761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99248083770534648383008507 148872125655801972574512761)
      ·
        refine ⟨111654094241851479430884571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148872125655801972574512761 111654094241851479430884571)
        ·
          refine ⟨167481141362777219146326857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111654094241851479430884571 167481141362777219146326857)
          ·
            refine ⟨125610856022082914359745143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167481141362777219146326857 125610856022082914359745143)
            ·
              refine ⟨188416284033124371539617715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125610856022082914359745143 188416284033124371539617715)
              ·
                refine ⟨282624426049686557309426573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188416284033124371539617715 282624426049686557309426573)
                ·
                  refine ⟨105984159768632458991034965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282624426049686557309426573 105984159768632458991034965)
                  ·
                    refine ⟨1242001872288661628801191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105984159768632458991034965 1242001872288661628801191)
                    ·
                      rfl

theorem cell22_3628185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3628185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628185 prefixEnd_3628185 := by exact prefixLift 3628185
  have htrace : WordTrace (prefixWord ++ tailWord_3628185) baseStart_3628185 baseEnd_3628185 := by
    simpa [prefixWord, tailWord_3628185, baseEnd_3628185] using wordTrace_append hprefix tailTrace_3628185
  have hstable : (prefixWord ++ tailWord_3628185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628185).length < 2 ^ (prefixWord ++ tailWord_3628185).sum := by decide
  have hdescent : baseEnd_3628185 < baseStart_3628185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628341 : List Nat := [1, 3, 3, 1, 2, 4, 2, 6]
def baseStart_3628341 : Nat := 118140960795 + 3628341 * 2 ^ 59
def prefixEnd_3628341 : Nat := 4983230072969 + 3 ^ 40 * 3628341 * 2
def baseEnd_3628341 : Nat := 138006141586303246877857

theorem tailTrace_3628341 : CollatzResearch.WordTrace tailWord_3628341 prefixEnd_3628341 138006141586303246877857 := by
  unfold tailWord_3628341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132336468148147703153356877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88224312098765135435571251 132336468148147703153356877)
  ·
    refine ⟨49626175555555388682508829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132336468148147703153356877 49626175555555388682508829)
    ·
      refine ⟨18609815833333270755940811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49626175555555388682508829 18609815833333270755940811)
      ·
        refine ⟨27914723749999906133911217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18609815833333270755940811 27914723749999906133911217)
        ·
          refine ⟨20936042812499929600433413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27914723749999906133911217 20936042812499929600433413)
          ·
            refine ⟨3925508027343736800081265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20936042812499929600433413 3925508027343736800081265)
            ·
              refine ⟨2944131020507802600060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925508027343736800081265 2944131020507802600060949)
              ·
                refine ⟨138006141586303246877857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944131020507802600060949 138006141586303246877857)
                ·
                  rfl

theorem cell22_3628341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 6].length) (baseStart_3628341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628341 prefixEnd_3628341 := by exact prefixLift 3628341
  have htrace : WordTrace (prefixWord ++ tailWord_3628341) baseStart_3628341 baseEnd_3628341 := by
    simpa [prefixWord, tailWord_3628341, baseEnd_3628341] using wordTrace_append hprefix tailTrace_3628341
  have hstable : (prefixWord ++ tailWord_3628341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628341).length < 2 ^ (prefixWord ++ tailWord_3628341).sum := by decide
  have hdescent : baseEnd_3628341 < baseStart_3628341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628352 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_3628352 : Nat := 118140960795 + 3628352 * 2 ^ 59
def prefixEnd_3628352 : Nat := 4983230072969 + 3 ^ 40 * 3628352 * 2
def baseEnd_3628352 : Nat := 414019679933842953291893

theorem tailTrace_3628352 : CollatzResearch.WordTrace tailWord_3628352 prefixEnd_3628352 414019679933842953291893 := by
  unfold tailWord_3628352
  simp only [CollatzResearch.WordTrace]
  refine ⟨66168434675553926016003655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88224579567405234688004873 66168434675553926016003655)
  ·
    refine ⟨99252652013330889024005483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66168434675553926016003655 99252652013330889024005483)
    ·
      refine ⟨148878978019996333536008225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99252652013330889024005483 148878978019996333536008225)
      ·
        refine ⟨111659233514997250152006169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148878978019996333536008225 111659233514997250152006169)
        ·
          refine ⟨83744425136247937614004627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111659233514997250152006169 83744425136247937614004627)
          ·
            refine ⟨125616637704371906421006941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83744425136247937614004627 125616637704371906421006941)
            ·
              refine ⟨47106239139139464907877603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125616637704371906421006941 47106239139139464907877603)
              ·
                refine ⟨70659358708709197361816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47106239139139464907877603 70659358708709197361816405)
                ·
                  refine ⟨414019679933842953291893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70659358708709197361816405 414019679933842953291893)
                  ·
                    rfl

theorem cell22_3628352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_3628352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628352 prefixEnd_3628352 := by exact prefixLift 3628352
  have htrace : WordTrace (prefixWord ++ tailWord_3628352) baseStart_3628352 baseEnd_3628352 := by
    simpa [prefixWord, tailWord_3628352, baseEnd_3628352] using wordTrace_append hprefix tailTrace_3628352
  have hstable : (prefixWord ++ tailWord_3628352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628352).length < 2 ^ (prefixWord ++ tailWord_3628352).sum := by decide
  have hdescent : baseEnd_3628352 < baseStart_3628352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628369 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 5]
def baseStart_3628369 : Nat := 118140960795 + 3628369 * 2 ^ 59
def prefixEnd_3628369 : Nat := 4983230072969 + 3 ^ 40 * 3628369 * 2
def baseEnd_3628369 : Nat := 414021619749648827400209

theorem tailTrace_3628369 : CollatzResearch.WordTrace tailWord_3628369 prefixEnd_3628369 414021619749648827400209 := by
  unfold tailWord_3628369
  simp only [CollatzResearch.WordTrace]
  refine ⟨132337489392046263935376161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88224992928030842623584107 132337489392046263935376161)
  ·
    refine ⟨99253117044034697951532121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132337489392046263935376161 99253117044034697951532121)
    ·
      refine ⟨74439837783026023463649091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99253117044034697951532121 74439837783026023463649091)
      ·
        refine ⟨111659756674539035195473637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74439837783026023463649091 111659756674539035195473637)
        ·
          refine ⟨20936204376476069099151307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111659756674539035195473637 20936204376476069099151307)
          ·
            refine ⟨31404306564714103648726961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20936204376476069099151307 31404306564714103648726961)
            ·
              refine ⟨23553229923535577736545221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31404306564714103648726961 23553229923535577736545221)
              ·
                refine ⟨4416230610662920825602229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23553229923535577736545221 4416230610662920825602229)
                ·
                  refine ⟨414021619749648827400209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4416230610662920825602229 414021619749648827400209)
                  ·
                    rfl

theorem cell22_3628369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_3628369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628369 prefixEnd_3628369 := by exact prefixLift 3628369
  have htrace : WordTrace (prefixWord ++ tailWord_3628369) baseStart_3628369 baseEnd_3628369 := by
    simpa [prefixWord, tailWord_3628369, baseEnd_3628369] using wordTrace_append hprefix tailTrace_3628369
  have hstable : (prefixWord ++ tailWord_3628369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628369).length < 2 ^ (prefixWord ++ tailWord_3628369).sum := by decide
  have hdescent : baseEnd_3628369 < baseStart_3628369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628373 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3628373 : Nat := 118140960795 + 3628373 * 2 ^ 59
def prefixEnd_3628373 : Nat := 4983230072969 + 3 ^ 40 * 3628373 * 2
def baseEnd_3628373 : Nat := 1242066228530691805100615

theorem tailTrace_3628373 : CollatzResearch.WordTrace tailWord_3628373 prefixEnd_3628373 1242066228530691805100615 := by
  unfold tailWord_3628373
  simp only [CollatzResearch.WordTrace]
  refine ⟨132337635284031772618521773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88225090189354515079014515 132337635284031772618521773)
  ·
    refine ⟨49626613231511914731945665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132337635284031772618521773 49626613231511914731945665)
    ·
      refine ⟨37219959923633936048959249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49626613231511914731945665 37219959923633936048959249)
      ·
        refine ⟨27914969942725452036719437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37219959923633936048959249 27914969942725452036719437)
        ·
          refine ⟨10468113728522044513769789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27914969942725452036719437 10468113728522044513769789)
          ·
            refine ⟨3925542648195766692663671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10468113728522044513769789 3925542648195766692663671)
            ·
              refine ⟨5888313972293650038995507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925542648195766692663671 5888313972293650038995507)
              ·
                refine ⟨8832470958440475058493261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888313972293650038995507 8832470958440475058493261)
                ·
                  refine ⟨3312176609415178146934973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8832470958440475058493261 3312176609415178146934973)
                  ·
                    refine ⟨1242066228530691805100615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312176609415178146934973 1242066228530691805100615)
                    ·
                      rfl

theorem cell22_3628373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3628373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628373 prefixEnd_3628373 := by exact prefixLift 3628373
  have htrace : WordTrace (prefixWord ++ tailWord_3628373) baseStart_3628373 baseEnd_3628373 := by
    simpa [prefixWord, tailWord_3628373, baseEnd_3628373] using wordTrace_append hprefix tailTrace_3628373
  have hstable : (prefixWord ++ tailWord_3628373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628373).length < 2 ^ (prefixWord ++ tailWord_3628373).sum := by decide
  have hdescent : baseEnd_3628373 < baseStart_3628373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628386 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3628386 : Nat := 118140960795 + 3628386 * 2 ^ 59
def prefixEnd_3628386 : Nat := 4983230072969 + 3 ^ 40 * 3628386 * 2
def baseEnd_3628386 : Nat := 414023559565454701508525

theorem tailTrace_3628386 : CollatzResearch.WordTrace tailWord_3628386 prefixEnd_3628386 414023559565454701508525 := by
  unfold tailWord_3628386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084527358246168959686253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88225406288656450559163341 33084527358246168959686253)
  ·
    refine ⟨12406697759342313359882345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33084527358246168959686253 12406697759342313359882345)
    ·
      refine ⟨9305023319506735019911759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12406697759342313359882345 9305023319506735019911759)
      ·
        refine ⟨13957534979260102529867639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305023319506735019911759 13957534979260102529867639)
        ·
          refine ⟨20936302468890153794801459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13957534979260102529867639 20936302468890153794801459)
          ·
            refine ⟨31404453703335230692202189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20936302468890153794801459 31404453703335230692202189)
            ·
              refine ⟨11776670138750711509575821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31404453703335230692202189 11776670138750711509575821)
              ·
                refine ⟨4416251302031516816090933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11776670138750711509575821 4416251302031516816090933)
                ·
                  refine ⟨414023559565454701508525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4416251302031516816090933 414023559565454701508525)
                  ·
                    rfl

theorem cell22_3628386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3628386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628386 prefixEnd_3628386 := by exact prefixLift 3628386
  have htrace : WordTrace (prefixWord ++ tailWord_3628386) baseStart_3628386 baseEnd_3628386 := by
    simpa [prefixWord, tailWord_3628386, baseEnd_3628386] using wordTrace_append hprefix tailTrace_3628386
  have hstable : (prefixWord ++ tailWord_3628386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628386).length < 2 ^ (prefixWord ++ tailWord_3628386).sum := by decide
  have hdescent : baseEnd_3628386 < baseStart_3628386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628399 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3628399 : Nat := 118140960795 + 3628399 * 2 ^ 59
def prefixEnd_3628399 : Nat := 4983230072969 + 3 ^ 40 * 3628399 * 2
def baseEnd_3628399 : Nat := 1242075128862036403950535

theorem tailTrace_3628399 : CollatzResearch.WordTrace tailWord_3628399 prefixEnd_3628399 1242075128862036403950535 := by
  unfold tailWord_3628399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132338583581937579058968251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88225722387958386039312167 132338583581937579058968251)
  ·
    refine ⟨198507875372906368588452377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132338583581937579058968251 198507875372906368588452377)
    ·
      refine ⟨148880906529679776441339283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198507875372906368588452377 148880906529679776441339283)
      ·
        refine ⟨223321359794519664662008925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148880906529679776441339283 223321359794519664662008925)
        ·
          refine ⟨83745509922944874248253347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223321359794519664662008925 83745509922944874248253347)
          ·
            refine ⟨125618264884417311372380021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83745509922944874248253347 125618264884417311372380021)
            ·
              refine ⟨11776712332914122941160627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125618264884417311372380021 11776712332914122941160627)
              ·
                refine ⟨17665068499371184411740941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11776712332914122941160627 17665068499371184411740941)
                ·
                  refine ⟨6624400687264194154402853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17665068499371184411740941 6624400687264194154402853)
                  ·
                    refine ⟨1242075128862036403950535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6624400687264194154402853 1242075128862036403950535)
                    ·
                      rfl

theorem cell22_3628399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3628399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628399 prefixEnd_3628399 := by exact prefixLift 3628399
  have htrace : WordTrace (prefixWord ++ tailWord_3628399) baseStart_3628399 baseEnd_3628399 := by
    simpa [prefixWord, tailWord_3628399, baseEnd_3628399] using wordTrace_append hprefix tailTrace_3628399
  have hstable : (prefixWord ++ tailWord_3628399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628399).length < 2 ^ (prefixWord ++ tailWord_3628399).sum := by decide
  have hdescent : baseEnd_3628399 < baseStart_3628399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628476 : List Nat := [2, 2, 2, 4, 2, 1, 9]
def baseStart_3628476 : Nat := 118140960795 + 3628476 * 2 ^ 59
def prefixEnd_3628476 : Nat := 4983230072969 + 3 ^ 40 * 3628476 * 2
def baseEnd_3628476 : Nat := 46003758797616069250937

theorem tailTrace_3628476 : CollatzResearch.WordTrace tailWord_3628476 prefixEnd_3628476 46003758797616069250937 := by
  unfold tailWord_3628476
  simp only [CollatzResearch.WordTrace]
  refine ⟨66170696001329310604760641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88227594668439080806347521 66170696001329310604760641)
  ·
    refine ⟨49628022000996982953570481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66170696001329310604760641 49628022000996982953570481)
    ·
      refine ⟨37221016500747737215177861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49628022000996982953570481 37221016500747737215177861)
      ·
        refine ⟨6978940593890200727845849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37221016500747737215177861 6978940593890200727845849)
        ·
          refine ⟨5234205445417650545884387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978940593890200727845849 5234205445417650545884387)
          ·
            refine ⟨7851308168126475818826581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234205445417650545884387 7851308168126475818826581)
            ·
              refine ⟨46003758797616069250937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7851308168126475818826581 46003758797616069250937)
              ·
                rfl

theorem cell22_3628476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 9].length) (baseStart_3628476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628476 prefixEnd_3628476 := by exact prefixLift 3628476
  have htrace : WordTrace (prefixWord ++ tailWord_3628476) baseStart_3628476 baseEnd_3628476 := by
    simpa [prefixWord, tailWord_3628476, baseEnd_3628476] using wordTrace_append hprefix tailTrace_3628476
  have hstable : (prefixWord ++ tailWord_3628476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628476).length < 2 ^ (prefixWord ++ tailWord_3628476).sum := by decide
  have hdescent : baseEnd_3628476 < baseStart_3628476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628491 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 3, 3]
def baseStart_3628491 : Nat := 118140960795 + 3628491 * 2 ^ 59
def prefixEnd_3628491 : Nat := 4983230072969 + 3 ^ 40 * 3628491 * 2
def baseEnd_3628491 : Nat := 1242106622342178830650253

theorem tailTrace_3628491 : CollatzResearch.WordTrace tailWord_3628491 prefixEnd_3628491 1242106622342178830650253 := by
  unfold tailWord_3628491
  simp only [CollatzResearch.WordTrace]
  refine ⟨132341939097604278771317327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88227959398402852514211551 132341939097604278771317327)
  ·
    refine ⟨198512908646406418156975991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132341939097604278771317327 198512908646406418156975991)
    ·
      refine ⟨297769362969609627235463987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198512908646406418156975991 297769362969609627235463987)
      ·
        refine ⟨446654044454414440853195981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297769362969609627235463987 446654044454414440853195981)
        ·
          refine ⟨167495266670405415319948493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446654044454414440853195981 167495266670405415319948493)
          ·
            refine ⟨62810725001402030744980685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167495266670405415319948493 62810725001402030744980685)
            ·
              refine ⟨23554021875525761529367757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62810725001402030744980685 23554021875525761529367757)
              ·
                refine ⟨8832758203322160573512909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23554021875525761529367757 8832758203322160573512909)
                ·
                  refine ⟨3312284326245810215067341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8832758203322160573512909 3312284326245810215067341)
                  ·
                    refine ⟨1242106622342178830650253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312284326245810215067341 1242106622342178830650253)
                    ·
                      rfl

theorem cell22_3628491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].length) (baseStart_3628491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628491 prefixEnd_3628491 := by exact prefixLift 3628491
  have htrace : WordTrace (prefixWord ++ tailWord_3628491) baseStart_3628491 baseEnd_3628491 := by
    simpa [prefixWord, tailWord_3628491, baseEnd_3628491] using wordTrace_append hprefix tailTrace_3628491
  have hstable : (prefixWord ++ tailWord_3628491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628491).length < 2 ^ (prefixWord ++ tailWord_3628491).sum := by decide
  have hdescent : baseEnd_3628491 < baseStart_3628491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628555 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 5]
def baseStart_3628555 : Nat := 118140960795 + 3628555 * 2 ^ 59
def prefixEnd_3628555 : Nat := 4983230072969 + 3 ^ 40 * 3628555 * 2
def baseEnd_3628555 : Nat := 414042843616701332350019

theorem tailTrace_3628555 : CollatzResearch.WordTrace tailWord_3628555 prefixEnd_3628555 414042843616701332350019 := by
  unfold tailWord_3628555
  simp only [CollatzResearch.WordTrace]
  refine ⟨132344273369372417701647119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88229515579581611801098079 132344273369372417701647119)
  ·
    refine ⟨198516410054058626552470679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132344273369372417701647119 198516410054058626552470679)
    ·
      refine ⟨297774615081087939828706019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198516410054058626552470679 297774615081087939828706019)
      ·
        refine ⟨446661922621631909743059029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297774615081087939828706019 446661922621631909743059029)
        ·
          refine ⟨5234319405722248942301473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 446661922621631909743059029 5234319405722248942301473)
          ·
            refine ⟨3925739554291686706726105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234319405722248942301473 3925739554291686706726105)
            ·
              refine ⟨2944304665718765030044579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925739554291686706726105 2944304665718765030044579)
              ·
                refine ⟨4416456998578147545066869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944304665718765030044579 4416456998578147545066869)
                ·
                  refine ⟨414042843616701332350019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4416456998578147545066869 414042843616701332350019)
                  ·
                    rfl

theorem cell22_3628555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 5].length) (baseStart_3628555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628555 prefixEnd_3628555 := by exact prefixLift 3628555
  have htrace : WordTrace (prefixWord ++ tailWord_3628555) baseStart_3628555 baseEnd_3628555 := by
    simpa [prefixWord, tailWord_3628555, baseEnd_3628555] using wordTrace_append hprefix tailTrace_3628555
  have hstable : (prefixWord ++ tailWord_3628555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628555).length < 2 ^ (prefixWord ++ tailWord_3628555).sum := by decide
  have hdescent : baseEnd_3628555 < baseStart_3628555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628568 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_3628568 : Nat := 118140960795 + 3628568 * 2 ^ 59
def prefixEnd_3628568 : Nat := 4983230072969 + 3 ^ 40 * 3628568 * 2
def baseEnd_3628568 : Nat := 1242132981015776296475017

theorem tailTrace_3628568 : CollatzResearch.WordTrace tailWord_3628568 prefixEnd_3628568 1242132981015776296475017 := by
  unfold tailWord_3628568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172373759162660460935179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88229831678883547281246905 66172373759162660460935179)
  ·
    refine ⟨99258560638743990691402769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66172373759162660460935179 99258560638743990691402769)
    ·
      refine ⟨74443920479057993018552077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99258560638743990691402769 74443920479057993018552077)
      ·
        refine ⟨27916470179646747381957029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74443920479057993018552077 27916470179646747381957029)
        ·
          refine ⟨5234338158683765134116943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27916470179646747381957029 5234338158683765134116943)
          ·
            refine ⟨7851507238025647701175415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234338158683765134116943 7851507238025647701175415)
            ·
              refine ⟨11777260857038471551763123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851507238025647701175415 11777260857038471551763123)
              ·
                refine ⟨17665891285557707327644685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777260857038471551763123 17665891285557707327644685)
                ·
                  refine ⟨6624709232084140247866757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17665891285557707327644685 6624709232084140247866757)
                  ·
                    refine ⟨1242132981015776296475017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6624709232084140247866757 1242132981015776296475017)
                    ·
                      rfl

theorem cell22_3628568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_3628568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628568 prefixEnd_3628568 := by exact prefixLift 3628568
  have htrace : WordTrace (prefixWord ++ tailWord_3628568) baseStart_3628568 baseEnd_3628568 := by
    simpa [prefixWord, tailWord_3628568, baseEnd_3628568] using wordTrace_append hprefix tailTrace_3628568
  have hstable : (prefixWord ++ tailWord_3628568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628568).length < 2 ^ (prefixWord ++ tailWord_3628568).sum := by decide
  have hdescent : baseEnd_3628568 < baseStart_3628568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628600 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_3628600 : Nat := 118140960795 + 3628600 * 2 ^ 59
def prefixEnd_3628600 : Nat := 4983230072969 + 3 ^ 40 * 3628600 * 2
def baseEnd_3628600 : Nat := 414047978423246293224973

theorem tailTrace_3628600 : CollatzResearch.WordTrace tailWord_3628600 prefixEnd_3628600 414047978423246293224973 := by
  unfold tailWord_3628600
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172957327104695193517627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88230609769472926924690169 66172957327104695193517627)
  ·
    refine ⟨99259435990657042790276441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66172957327104695193517627 99259435990657042790276441)
    ·
      refine ⟨74444576992992782092707331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99259435990657042790276441 74444576992992782092707331)
      ·
        refine ⟨111666865489489173139060997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74444576992992782092707331 111666865489489173139060997)
        ·
          refine ⟨20937537279279219963573937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111666865489489173139060997 20937537279279219963573937)
          ·
            refine ⟨15703152959459414972680453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20937537279279219963573937 15703152959459414972680453)
            ·
              refine ⟨2944341179898640307377585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15703152959459414972680453 2944341179898640307377585)
              ·
                refine ⟨2208255884923980230533189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944341179898640307377585 2208255884923980230533189)
                ·
                  refine ⟨414047978423246293224973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208255884923980230533189 414047978423246293224973)
                  ·
                    rfl

theorem cell22_3628600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_3628600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628600 prefixEnd_3628600 := by exact prefixLift 3628600
  have htrace : WordTrace (prefixWord ++ tailWord_3628600) baseStart_3628600 baseEnd_3628600 := by
    simpa [prefixWord, tailWord_3628600, baseEnd_3628600] using wordTrace_append hprefix tailTrace_3628600
  have hstable : (prefixWord ++ tailWord_3628600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628600).length < 2 ^ (prefixWord ++ tailWord_3628600).sum := by decide
  have hdescent : baseEnd_3628600 < baseStart_3628600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628628 : List Nat := [2, 4, 1, 1, 1, 2, 5, 6]
def baseStart_3628628 : Nat := 118140960795 + 3628628 * 2 ^ 59
def prefixEnd_3628628 : Nat := 4983230072969 + 3 ^ 40 * 3628628 * 2
def baseEnd_3628628 : Nat := 138017057804661793330537

theorem tailTrace_3628628 : CollatzResearch.WordTrace tailWord_3628628 prefixEnd_3628628 138017057804661793330537 := by
  unfold tailWord_3628628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66173467949053975584527269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88231290598738634112703025 66173467949053975584527269)
  ·
    refine ⟨12407525240447620422098863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66173467949053975584527269 12407525240447620422098863)
    ·
      refine ⟨18611287860671430633148295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407525240447620422098863 18611287860671430633148295)
      ·
        refine ⟨27916931791007145949722443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18611287860671430633148295 27916931791007145949722443)
        ·
          refine ⟨41875397686510718924583665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27916931791007145949722443 41875397686510718924583665)
          ·
            refine ⟨31406548264883039193437749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41875397686510718924583665 31406548264883039193437749)
            ·
              refine ⟨2944363899832784924384789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31406548264883039193437749 2944363899832784924384789)
              ·
                refine ⟨138017057804661793330537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944363899832784924384789 138017057804661793330537)
                ·
                  rfl

theorem cell22_3628628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_3628628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628628 prefixEnd_3628628 := by exact prefixLift 3628628
  have htrace : WordTrace (prefixWord ++ tailWord_3628628) baseStart_3628628 baseEnd_3628628 := by
    simpa [prefixWord, tailWord_3628628, baseEnd_3628628] using wordTrace_append hprefix tailTrace_3628628
  have hstable : (prefixWord ++ tailWord_3628628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628628).length < 2 ^ (prefixWord ++ tailWord_3628628).sum := by decide
  have hdescent : baseEnd_3628628 < baseStart_3628628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628731 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_3628731 : Nat := 118140960795 + 3628731 * 2 ^ 59
def prefixEnd_3628731 : Nat := 4983230072969 + 3 ^ 40 * 3628731 * 2
def baseEnd_3628731 : Nat := 1242188779246898204649517

theorem tailTrace_3628731 : CollatzResearch.WordTrace tailWord_3628731 prefixEnd_3628731 1242188779246898204649517 := by
  unfold tailWord_3628731
  simp only [CollatzResearch.WordTrace]
  refine ⟨132350692616734799760054047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88233795077823199840036031 132350692616734799760054047)
  ·
    refine ⟨198526038925102199640081071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132350692616734799760054047 198526038925102199640081071)
    ·
      refine ⟨297789058387653299460121607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198526038925102199640081071 297789058387653299460121607)
      ·
        refine ⟨446683587581479949190182411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297789058387653299460121607 446683587581479949190182411)
        ·
          refine ⟨670025381372219923785273617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446683587581479949190182411 670025381372219923785273617)
          ·
            refine ⟨502519036029164942838955213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670025381372219923785273617 502519036029164942838955213)
            ·
              refine ⟨188444638510936853564608205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502519036029164942838955213 188444638510936853564608205)
              ·
                refine ⟨70666739441601320086728077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188444638510936853564608205 70666739441601320086728077)
                ·
                  refine ⟨26500027290600495032523029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70666739441601320086728077 26500027290600495032523029)
                  ·
                    refine ⟨1242188779246898204649517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26500027290600495032523029 1242188779246898204649517)
                    ·
                      rfl

theorem cell22_3628731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_3628731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628731 prefixEnd_3628731 := by exact prefixLift 3628731
  have htrace : WordTrace (prefixWord ++ tailWord_3628731) baseStart_3628731 baseEnd_3628731 := by
    simpa [prefixWord, tailWord_3628731, baseEnd_3628731] using wordTrace_append hprefix tailTrace_3628731
  have hstable : (prefixWord ++ tailWord_3628731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628731).length < 2 ^ (prefixWord ++ tailWord_3628731).sum := by decide
  have hdescent : baseEnd_3628731 < baseStart_3628731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628733 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3628733 : Nat := 118140960795 + 3628733 * 2 ^ 59
def prefixEnd_3628733 : Nat := 4983230072969 + 3 ^ 40 * 3628733 * 2
def baseEnd_3628733 : Nat := 1242189463887770866099511

theorem tailTrace_3628733 : CollatzResearch.WordTrace tailWord_3628733 prefixEnd_3628733 1242189463887770866099511 := by
  unfold tailWord_3628733
  simp only [CollatzResearch.WordTrace]
  refine ⟨132350765562727554101626853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88233843708485036067751235 132350765562727554101626853)
  ·
    refine ⟨24815768543011416394055035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132350765562727554101626853 24815768543011416394055035)
    ·
      refine ⟨37223652814517124591082553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24815768543011416394055035 37223652814517124591082553)
      ·
        refine ⟨27917739610887843443311915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37223652814517124591082553 27917739610887843443311915)
        ·
          refine ⟨41876609416331765164967873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27917739610887843443311915 41876609416331765164967873)
          ·
            refine ⟨31407457062248823873725905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41876609416331765164967873 31407457062248823873725905)
            ·
              refine ⟨23555592796686617905294429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31407457062248823873725905 23555592796686617905294429)
              ·
                refine ⟨8833347298757481714485411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23555592796686617905294429 8833347298757481714485411)
                ·
                  refine ⟨13250020948136222571728117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833347298757481714485411 13250020948136222571728117)
                  ·
                    refine ⟨1242189463887770866099511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13250020948136222571728117 1242189463887770866099511)
                    ·
                      rfl

theorem cell22_3628733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3628733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628733 prefixEnd_3628733 := by exact prefixLift 3628733
  have htrace : WordTrace (prefixWord ++ tailWord_3628733) baseStart_3628733 baseEnd_3628733 := by
    simpa [prefixWord, tailWord_3628733, baseEnd_3628733] using wordTrace_append hprefix tailTrace_3628733
  have hstable : (prefixWord ++ tailWord_3628733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628733).length < 2 ^ (prefixWord ++ tailWord_3628733).sum := by decide
  have hdescent : baseEnd_3628733 < baseStart_3628733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628769 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 4]
def baseStart_3628769 : Nat := 118140960795 + 3628769 * 2 ^ 59
def prefixEnd_3628769 : Nat := 4983230072969 + 3 ^ 40 * 3628769 * 2
def baseEnd_3628769 : Nat := 414067262474492924066467

theorem tailTrace_3628769 : CollatzResearch.WordTrace tailWord_3628769 prefixEnd_3628769 414067262474492924066467 := by
  unfold tailWord_3628769
  simp only [CollatzResearch.WordTrace]
  refine ⟨132352078590597132249937361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88234719060398088166624907 132352078590597132249937361)
  ·
    refine ⟨99264058942947849187453021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132352078590597132249937361 99264058942947849187453021)
    ·
      refine ⟨37224022103605443445294883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99264058942947849187453021 37224022103605443445294883)
      ·
        refine ⟨55836033155408165167942325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37224022103605443445294883 55836033155408165167942325)
        ·
          refine ⟨5234628108319515484494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55836033155408165167942325 5234628108319515484494593)
          ·
            refine ⟨3925971081239636613370945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234628108319515484494593 3925971081239636613370945)
            ·
              refine ⟨2944478310929727460028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925971081239636613370945 2944478310929727460028209)
              ·
                refine ⟨2208358733197295595021157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944478310929727460028209 2208358733197295595021157)
                ·
                  refine ⟨414067262474492924066467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208358733197295595021157 414067262474492924066467)
                  ·
                    rfl

theorem cell22_3628769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_3628769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628769 prefixEnd_3628769 := by exact prefixLift 3628769
  have htrace : WordTrace (prefixWord ++ tailWord_3628769) baseStart_3628769 baseEnd_3628769 := by
    simpa [prefixWord, tailWord_3628769, baseEnd_3628769] using wordTrace_append hprefix tailTrace_3628769
  have hstable : (prefixWord ++ tailWord_3628769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628769).length < 2 ^ (prefixWord ++ tailWord_3628769).sum := by decide
  have hdescent : baseEnd_3628769 < baseStart_3628769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628808 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_3628808 : Nat := 118140960795 + 3628808 * 2 ^ 59
def prefixEnd_3628808 : Nat := 4983230072969 + 3 ^ 40 * 3628808 * 2
def baseEnd_3628808 : Nat := 414071712640165223491427

theorem tailTrace_3628808 : CollatzResearch.WordTrace tailWord_3628808 prefixEnd_3628808 414071712640165223491427 := by
  unfold tailWord_3628808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66176750518727920955303539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88235667358303894607071385 66176750518727920955303539)
  ·
    refine ⟨99265125778091881432955309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66176750518727920955303539 99265125778091881432955309)
    ·
      refine ⟨37224422166784455537358241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99265125778091881432955309 37224422166784455537358241)
      ·
        refine ⟨27918316625088341653018681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37224422166784455537358241 27918316625088341653018681)
        ·
          refine ⟨20938737468816256239764011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27918316625088341653018681 20938737468816256239764011)
          ·
            refine ⟨31408106203224384359646017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20938737468816256239764011 31408106203224384359646017)
            ·
              refine ⟨23556079652418288269734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31408106203224384359646017 23556079652418288269734513)
              ·
                refine ⟨17667059739313716202300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23556079652418288269734513 17667059739313716202300885)
                ·
                  refine ⟨414071712640165223491427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17667059739313716202300885 414071712640165223491427)
                  ·
                    rfl

theorem cell22_3628808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_3628808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628808 prefixEnd_3628808 := by exact prefixLift 3628808
  have htrace : WordTrace (prefixWord ++ tailWord_3628808) baseStart_3628808 baseEnd_3628808 := by
    simpa [prefixWord, tailWord_3628808, baseEnd_3628808] using wordTrace_append hprefix tailTrace_3628808
  have hstable : (prefixWord ++ tailWord_3628808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628808).length < 2 ^ (prefixWord ++ tailWord_3628808).sum := by decide
  have hdescent : baseEnd_3628808 < baseStart_3628808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628812 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_3628812 : Nat := 118140960795 + 3628812 * 2 ^ 59
def prefixEnd_3628812 : Nat := 4983230072969 + 3 ^ 40 * 3628812 * 2
def baseEnd_3628812 : Nat := 1242216507202240993374269

theorem tailTrace_3628812 : CollatzResearch.WordTrace tailWord_3628812 prefixEnd_3628812 1242216507202240993374269 := by
  unfold tailWord_3628812
  simp only [CollatzResearch.WordTrace]
  refine ⟨66176823464720675296876345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88235764619627567062501793 66176823464720675296876345)
  ·
    refine ⟨49632617598540506472657259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66176823464720675296876345 49632617598540506472657259)
    ·
      refine ⟨74448926397810759708985889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49632617598540506472657259 74448926397810759708985889)
      ·
        refine ⟨55836694798358069781739417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74448926397810759708985889 55836694798358069781739417)
        ·
          refine ⟨41877521098768552336304563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55836694798358069781739417 41877521098768552336304563)
          ·
            refine ⟨62816281648152828504456845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41877521098768552336304563 62816281648152828504456845)
            ·
              refine ⟨23556105618057310689171317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62816281648152828504456845 23556105618057310689171317)
              ·
                refine ⟨2208384901692872877109811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23556105618057310689171317 2208384901692872877109811)
                ·
                  refine ⟨3312577352539309315664717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208384901692872877109811 3312577352539309315664717)
                  ·
                    refine ⟨1242216507202240993374269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312577352539309315664717 1242216507202240993374269)
                    ·
                      rfl

theorem cell22_3628812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_3628812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628812 prefixEnd_3628812 := by exact prefixLift 3628812
  have htrace : WordTrace (prefixWord ++ tailWord_3628812) baseStart_3628812 baseEnd_3628812 := by
    simpa [prefixWord, tailWord_3628812, baseEnd_3628812] using wordTrace_append hprefix tailTrace_3628812
  have hstable : (prefixWord ++ tailWord_3628812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628812).length < 2 ^ (prefixWord ++ tailWord_3628812).sum := by decide
  have hdescent : baseEnd_3628812 < baseStart_3628812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628840 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3628840 : Nat := 118140960795 + 3628840 * 2 ^ 59
def prefixEnd_3628840 : Nat := 4983230072969 + 3 ^ 40 * 3628840 * 2
def baseEnd_3628840 : Nat := 1242226092174458253674183

theorem tailTrace_3628840 : CollatzResearch.WordTrace tailWord_3628840 prefixEnd_3628840 1242226092174458253674183 := by
  unfold tailWord_3628840
  simp only [CollatzResearch.WordTrace]
  refine ⟨66177334086669955687885987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88236445448893274250514649 66177334086669955687885987)
  ·
    refine ⟨99266001130004933531828981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66177334086669955687885987 99266001130004933531828981)
    ·
      refine ⟨9306187605937962518608967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99266001130004933531828981 9306187605937962518608967)
      ·
        refine ⟨13959281408906943777913451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9306187605937962518608967 13959281408906943777913451)
        ·
          refine ⟨20938922113360415666870177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959281408906943777913451 20938922113360415666870177)
          ·
            refine ⟨15704191585020311750152633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20938922113360415666870177 15704191585020311750152633)
            ·
              refine ⟨11778143688765233812614475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15704191585020311750152633 11778143688765233812614475)
              ·
                refine ⟨17667215533147850718921713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778143688765233812614475 17667215533147850718921713)
                ·
                  refine ⟨13250411649860888039191285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17667215533147850718921713 13250411649860888039191285)
                  ·
                    refine ⟨1242226092174458253674183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13250411649860888039191285 1242226092174458253674183)
                    ·
                      rfl

theorem cell22_3628840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3628840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628840 prefixEnd_3628840 := by exact prefixLift 3628840
  have htrace : WordTrace (prefixWord ++ tailWord_3628840) baseStart_3628840 baseEnd_3628840 := by
    simpa [prefixWord, tailWord_3628840, baseEnd_3628840] using wordTrace_append hprefix tailTrace_3628840
  have hstable : (prefixWord ++ tailWord_3628840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628840).length < 2 ^ (prefixWord ++ tailWord_3628840).sum := by decide
  have hdescent : baseEnd_3628840 < baseStart_3628840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628887 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 6]
def baseStart_3628887 : Nat := 118140960795 + 3628887 * 2 ^ 59
def prefixEnd_3628887 : Nat := 4983230072969 + 3 ^ 40 * 3628887 * 2
def baseEnd_3628887 : Nat := 414080727078321932583013

theorem tailTrace_3628887 : CollatzResearch.WordTrace tailWord_3628887 prefixEnd_3628887 414080727078321932583013 := by
  unfold tailWord_3628887
  simp only [CollatzResearch.WordTrace]
  refine ⟨132356382404169638402732915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88237588269446425601821943 132356382404169638402732915)
  ·
    refine ⟨198534573606254457604099373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132356382404169638402732915 198534573606254457604099373)
    ·
      refine ⟨74450465102345421601537265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198534573606254457604099373 74450465102345421601537265)
      ·
        refine ⟨55837848826759066201152949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74450465102345421601537265 55837848826759066201152949)
        ·
          refine ⟨5234798327508662456358089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55837848826759066201152949 5234798327508662456358089)
          ·
            refine ⟨3926098745631496842268567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234798327508662456358089 3926098745631496842268567)
            ·
              refine ⟨5889148118447245263402851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926098745631496842268567 5889148118447245263402851)
              ·
                refine ⟨8833722177670867895104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889148118447245263402851 8833722177670867895104277)
                ·
                  refine ⟨414080727078321932583013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8833722177670867895104277 414080727078321932583013)
                  ·
                    rfl

theorem cell22_3628887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].length) (baseStart_3628887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628887 prefixEnd_3628887 := by exact prefixLift 3628887
  have htrace : WordTrace (prefixWord ++ tailWord_3628887) baseStart_3628887 baseEnd_3628887 := by
    simpa [prefixWord, tailWord_3628887, baseEnd_3628887] using wordTrace_append hprefix tailTrace_3628887
  have hstable : (prefixWord ++ tailWord_3628887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628887).length < 2 ^ (prefixWord ++ tailWord_3628887).sum := by decide
  have hdescent : baseEnd_3628887 < baseStart_3628887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628906 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3628906 : Nat := 118140960795 + 3628906 * 2 ^ 59
def prefixEnd_3628906 : Nat := 4983230072969 + 3 ^ 40 * 3628906 * 2
def baseEnd_3628906 : Nat := 1242248685323256081523981

theorem tailTrace_3628906 : CollatzResearch.WordTrace tailWord_3628906 prefixEnd_3628906 1242248685323256081523981 := by
  unfold tailWord_3628906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089268847775201161918643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88238050260733869765116381 33089268847775201161918643)
  ·
    refine ⟨49633903271662801742877965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33089268847775201161918643 49633903271662801742877965)
    ·
      refine ⟨18612713726873550653579237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49633903271662801742877965 18612713726873550653579237)
      ·
        refine ⟨3489883823788790747546107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18612713726873550653579237 3489883823788790747546107)
        ·
          refine ⟨5234825735683186121319161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489883823788790747546107 5234825735683186121319161)
          ·
            refine ⟨3926119301762389590989371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234825735683186121319161 3926119301762389590989371)
            ·
              refine ⟨5889178952643584386484057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926119301762389590989371 5889178952643584386484057)
              ·
                refine ⟨4416884214482688289863043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5889178952643584386484057 4416884214482688289863043)
                ·
                  refine ⟨6625326321724032434794565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416884214482688289863043 6625326321724032434794565)
                  ·
                    refine ⟨1242248685323256081523981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625326321724032434794565 1242248685323256081523981)
                    ·
                      rfl

theorem cell22_3628906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3628906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628906 prefixEnd_3628906 := by exact prefixLift 3628906
  have htrace : WordTrace (prefixWord ++ tailWord_3628906) baseStart_3628906 baseEnd_3628906 := by
    simpa [prefixWord, tailWord_3628906, baseEnd_3628906] using wordTrace_append hprefix tailTrace_3628906
  have hstable : (prefixWord ++ tailWord_3628906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628906).length < 2 ^ (prefixWord ++ tailWord_3628906).sum := by decide
  have hdescent : baseEnd_3628906 < baseStart_3628906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628917 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3628917 : Nat := 118140960795 + 3628917 * 2 ^ 59
def prefixEnd_3628917 : Nat := 4983230072969 + 3 ^ 40 * 3628917 * 2
def baseEnd_3628917 : Nat := 1242252450848055719498947

theorem tailTrace_3628917 : CollatzResearch.WordTrace tailWord_3628917 prefixEnd_3628917 1242252450848055719498947 := by
  unfold tailWord_3628917
  simp only [CollatzResearch.WordTrace]
  refine ⟨132357476594060953526325005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88238317729373969017550003 132357476594060953526325005)
  ·
    refine ⟨49634053722772857572371877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132357476594060953526325005 49634053722772857572371877)
    ·
      refine ⟨9306385073019910794819727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49634053722772857572371877 9306385073019910794819727)
      ·
        refine ⟨13959577609529866192229591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9306385073019910794819727 13959577609529866192229591)
        ·
          refine ⟨20939366414294799288344387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959577609529866192229591 20939366414294799288344387)
          ·
            refine ⟨31409049621442198932516581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20939366414294799288344387 31409049621442198932516581)
            ·
              refine ⟨5889196804020412299846859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31409049621442198932516581 5889196804020412299846859)
              ·
                refine ⟨8833795206030618449770289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889196804020412299846859 8833795206030618449770289)
                ·
                  refine ⟨6625346404522963837327717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8833795206030618449770289 6625346404522963837327717)
                  ·
                    refine ⟨1242252450848055719498947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625346404522963837327717 1242252450848055719498947)
                    ·
                      rfl

theorem cell22_3628917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3628917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628917 prefixEnd_3628917 := by exact prefixLift 3628917
  have htrace : WordTrace (prefixWord ++ tailWord_3628917) baseStart_3628917 baseEnd_3628917 := by
    simpa [prefixWord, tailWord_3628917, baseEnd_3628917] using wordTrace_append hprefix tailTrace_3628917
  have hstable : (prefixWord ++ tailWord_3628917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628917).length < 2 ^ (prefixWord ++ tailWord_3628917).sum := by decide
  have hdescent : baseEnd_3628917 < baseStart_3628917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628938 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_3628938 : Nat := 118140960795 + 3628938 * 2 ^ 59
def prefixEnd_3628938 : Nat := 4983230072969 + 3 ^ 40 * 3628938 * 2
def baseEnd_3628938 : Nat := 414086546525739554907961

theorem tailTrace_3628938 : CollatzResearch.WordTrace tailWord_3628938 prefixEnd_3628938 414086546525739554907961 := by
  unfold tailWord_3628938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089560631746218528209867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88238828351323249408559645 33089560631746218528209867)
  ·
    refine ⟨49634340947619327792314801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33089560631746218528209867 49634340947619327792314801)
    ·
      refine ⟨37225755710714495844236101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49634340947619327792314801 37225755710714495844236101)
      ·
        refine ⟨6979829195758967970794269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37225755710714495844236101 6979829195758967970794269)
        ·
          refine ⟨2617435948409612989047851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6979829195758967970794269 2617435948409612989047851)
          ·
            refine ⟨3926153922614419483571777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617435948409612989047851 3926153922614419483571777)
            ·
              refine ⟨2944615441960814612678833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926153922614419483571777 2944615441960814612678833)
              ·
                refine ⟨2208461581470610959509125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944615441960814612678833 2208461581470610959509125)
                ·
                  refine ⟨414086546525739554907961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208461581470610959509125 414086546525739554907961)
                  ·
                    rfl

theorem cell22_3628938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_3628938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628938 prefixEnd_3628938 := by exact prefixLift 3628938
  have htrace : WordTrace (prefixWord ++ tailWord_3628938) baseStart_3628938 baseEnd_3628938 := by
    simpa [prefixWord, tailWord_3628938, baseEnd_3628938] using wordTrace_append hprefix tailTrace_3628938
  have hstable : (prefixWord ++ tailWord_3628938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628938).length < 2 ^ (prefixWord ++ tailWord_3628938).sum := by decide
  have hdescent : baseEnd_3628938 < baseStart_3628938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628943 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 13]
def baseStart_3628943 : Nat := 118140960795 + 3628943 * 2 ^ 59
def prefixEnd_3628943 : Nat := 4983230072969 + 3 ^ 40 * 3628943 * 2
def baseEnd_3628943 : Nat := 414087117059800106116289

theorem tailTrace_3628943 : CollatzResearch.WordTrace tailWord_3628943 prefixEnd_3628943 414087117059800106116289 := by
  unfold tailWord_3628943
  simp only [CollatzResearch.WordTrace]
  refine ⟨132358424891966759966771483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88238949927977839977847655 132358424891966759966771483)
  ·
    refine ⟨198537637337950139950157225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132358424891966759966771483 198537637337950139950157225)
    ·
      refine ⟨148903228003462604962617919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198537637337950139950157225 148903228003462604962617919)
      ·
        refine ⟨223354842005193907443926879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148903228003462604962617919 223354842005193907443926879)
        ·
          refine ⟨335032263007790861165890319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223354842005193907443926879 335032263007790861165890319)
          ·
            refine ⟨502548394511686291748835479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335032263007790861165890319 502548394511686291748835479)
            ·
              refine ⟨753822591767529437623253219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502548394511686291748835479 753822591767529437623253219)
              ·
                refine ⟨1130733887651294156434879829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753822591767529437623253219 1130733887651294156434879829)
                ·
                  refine ⟨414087117059800106116289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1130733887651294156434879829 414087117059800106116289)
                  ·
                    rfl

theorem cell22_3628943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_3628943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628943 prefixEnd_3628943 := by exact prefixLift 3628943
  have htrace : WordTrace (prefixWord ++ tailWord_3628943) baseStart_3628943 baseEnd_3628943 := by
    simpa [prefixWord, tailWord_3628943, baseEnd_3628943] using wordTrace_append hprefix tailTrace_3628943
  have hstable : (prefixWord ++ tailWord_3628943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628943).length < 2 ^ (prefixWord ++ tailWord_3628943).sum := by decide
  have hdescent : baseEnd_3628943 < baseStart_3628943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628968 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3628968 : Nat := 118140960795 + 3628968 * 2 ^ 59
def prefixEnd_3628968 : Nat := 4983230072969 + 3 ^ 40 * 3628968 * 2
def baseEnd_3628968 : Nat := 1242269909190308586473791

theorem tailTrace_3628968 : CollatzResearch.WordTrace tailWord_3628968 prefixEnd_3628968 1242269909190308586473791 := by
  unfold tailWord_3628968
  simp only [CollatzResearch.WordTrace]
  refine ⟨66179668358438094618215779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88239557811250792824287705 66179668358438094618215779)
  ·
    refine ⟨99269502537657141927323669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66179668358438094618215779 99269502537657141927323669)
    ·
      refine ⟨4653257931452678527843297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99269502537657141927323669 4653257931452678527843297)
      ·
        refine ⟨3489943448589508895882473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653257931452678527843297 3489943448589508895882473)
        ·
          refine ⟨2617457586442131671911855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489943448589508895882473 2617457586442131671911855)
          ·
            refine ⟨3926186379663197507867783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617457586442131671911855 3926186379663197507867783)
            ·
              refine ⟨5889279569494796261801675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926186379663197507867783 5889279569494796261801675)
              ·
                refine ⟨8833919354242194392702513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889279569494796261801675 8833919354242194392702513)
                ·
                  refine ⟨6625439515681645794526885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8833919354242194392702513 6625439515681645794526885)
                  ·
                    refine ⟨1242269909190308586473791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625439515681645794526885 1242269909190308586473791)
                    ·
                      rfl

theorem cell22_3628968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3628968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628968 prefixEnd_3628968 := by exact prefixLift 3628968
  have htrace : WordTrace (prefixWord ++ tailWord_3628968) baseStart_3628968 baseEnd_3628968 := by
    simpa [prefixWord, tailWord_3628968, baseEnd_3628968] using wordTrace_append hprefix tailTrace_3628968
  have hstable : (prefixWord ++ tailWord_3628968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628968).length < 2 ^ (prefixWord ++ tailWord_3628968).sum := by decide
  have hdescent : baseEnd_3628968 < baseStart_3628968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628981 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3628981 : Nat := 118140960795 + 3628981 * 2 ^ 59
def prefixEnd_3628981 : Nat := 4983230072969 + 3 ^ 40 * 3628981 * 2
def baseEnd_3628981 : Nat := 1242274359355980885898751

theorem tailTrace_3628981 : CollatzResearch.WordTrace tailWord_3628981 prefixEnd_3628981 1242274359355980885898751 := by
  unfold tailWord_3628981
  simp only [CollatzResearch.WordTrace]
  refine ⟨132359810865829092456654797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88239873910552728304436531 132359810865829092456654797)
  ·
    refine ⟨49634929074685909671245549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132359810865829092456654797 49634929074685909671245549)
    ·
      refine ⟨18613098403007216126717081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49634929074685909671245549 18613098403007216126717081)
      ·
        refine ⟨13959823802255412095037811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18613098403007216126717081 13959823802255412095037811)
        ·
          refine ⟨20939735703383118142556717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959823802255412095037811 20939735703383118142556717)
          ·
            refine ⟨7852400888768669303458769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20939735703383118142556717 7852400888768669303458769)
            ·
              refine ⟨5889300666576501977594077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852400888768669303458769 5889300666576501977594077)
              ·
                refine ⟨2208487749966188241597779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889300666576501977594077 2208487749966188241597779)
                ·
                  refine ⟨3312731624949282362396669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208487749966188241597779 3312731624949282362396669)
                  ·
                    refine ⟨1242274359355980885898751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312731624949282362396669 1242274359355980885898751)
                    ·
                      rfl

theorem cell22_3628981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3628981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3628981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3628981 prefixEnd_3628981 := by exact prefixLift 3628981
  have htrace : WordTrace (prefixWord ++ tailWord_3628981) baseStart_3628981 baseEnd_3628981 := by
    simpa [prefixWord, tailWord_3628981, baseEnd_3628981] using wordTrace_append hprefix tailTrace_3628981
  have hstable : (prefixWord ++ tailWord_3628981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628981).length < 2 ^ (prefixWord ++ tailWord_3628981).sum := by decide
  have hdescent : baseEnd_3628981 < baseStart_3628981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629035 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_3629035 : Nat := 118140960795 + 3629035 * 2 ^ 59
def prefixEnd_3629035 : Nat := 4983230072969 + 3 ^ 40 * 3629035 * 2
def baseEnd_3629035 : Nat := 1242292844659542745048585

theorem tailTrace_3629035 : CollatzResearch.WordTrace tailWord_3629035 prefixEnd_3629035 1242292844659542745048585 := by
  unfold tailWord_3629035
  simp only [CollatzResearch.WordTrace]
  refine ⟨132361780407633459679120559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88241186938422306452747039 132361780407633459679120559)
  ·
    refine ⟨198542670611450189518680839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132361780407633459679120559 198542670611450189518680839)
    ·
      refine ⟨297814005917175284278021259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198542670611450189518680839 297814005917175284278021259)
      ·
        refine ⟨446721008875762926417031889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297814005917175284278021259 446721008875762926417031889)
        ·
          refine ⟨335040756656822194812773917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446721008875762926417031889 335040756656822194812773917)
          ·
            refine ⟨125640283746308323054790219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335040756656822194812773917 125640283746308323054790219)
            ·
              refine ⟨188460425619462484582185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125640283746308323054790219 188460425619462484582185329)
              ·
                refine ⟨141345319214596863436638997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188460425619462484582185329 141345319214596863436638997)
                ·
                  refine ⟨6625561838184227973592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141345319214596863436638997 6625561838184227973592453)
                  ·
                    refine ⟨1242292844659542745048585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625561838184227973592453 1242292844659542745048585)
                    ·
                      rfl

theorem cell22_3629035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_3629035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629035 prefixEnd_3629035 := by exact prefixLift 3629035
  have htrace : WordTrace (prefixWord ++ tailWord_3629035) baseStart_3629035 baseEnd_3629035 := by
    simpa [prefixWord, tailWord_3629035, baseEnd_3629035] using wordTrace_append hprefix tailTrace_3629035
  have hstable : (prefixWord ++ tailWord_3629035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629035).length < 2 ^ (prefixWord ++ tailWord_3629035).sum := by decide
  have hdescent : baseEnd_3629035 < baseStart_3629035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629052 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3629052 : Nat := 118140960795 + 3629052 * 2 ^ 59
def prefixEnd_3629052 : Nat := 4983230072969 + 3 ^ 40 * 3629052 * 2
def baseEnd_3629052 : Nat := 1242298664106960367373533

theorem tailTrace_3629052 : CollatzResearch.WordTrace tailWord_3629052 prefixEnd_3629052 1242298664106960367373533 := by
  unfold tailWord_3629052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66181200224285935791244705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88241600299047914388326273 66181200224285935791244705)
  ·
    refine ⟨49635900168214451843433529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66181200224285935791244705 49635900168214451843433529)
    ·
      refine ⟨37226925126160838882575147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49635900168214451843433529 37226925126160838882575147)
      ·
        refine ⟨55840387689241258323862721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37226925126160838882575147 55840387689241258323862721)
        ·
          refine ⟨41880290766930943742897041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55840387689241258323862721 41880290766930943742897041)
          ·
            refine ⟨31410218075198207807172781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41880290766930943742897041 31410218075198207807172781)
            ·
              refine ⟨11778831778199327927689793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31410218075198207807172781 11778831778199327927689793)
              ·
                refine ⟨8834123833649495945767345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11778831778199327927689793 8834123833649495945767345)
                ·
                  refine ⟨6625592875237121959325509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8834123833649495945767345 6625592875237121959325509)
                  ·
                    refine ⟨1242298664106960367373533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625592875237121959325509 1242298664106960367373533)
                    ·
                      rfl

theorem cell22_3629052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3629052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629052 prefixEnd_3629052 := by exact prefixLift 3629052
  have htrace : WordTrace (prefixWord ++ tailWord_3629052) baseStart_3629052 baseEnd_3629052 := by
    simpa [prefixWord, tailWord_3629052, baseEnd_3629052] using wordTrace_append hprefix tailTrace_3629052
  have hstable : (prefixWord ++ tailWord_3629052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629052).length < 2 ^ (prefixWord ++ tailWord_3629052).sum := by decide
  have hdescent : baseEnd_3629052 < baseStart_3629052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629062 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3629062 : Nat := 118140960795 + 3629062 * 2 ^ 59
def prefixEnd_3629062 : Nat := 4983230072969 + 3 ^ 40 * 3629062 * 2
def baseEnd_3629062 : Nat := 414100695770441224874501

theorem tailTrace_3629062 : CollatzResearch.WordTrace tailWord_3629062 prefixEnd_3629062 414100695770441224874501 := by
  unfold tailWord_3629062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136336411829238852823545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88241843452357095526902293 4136336411829238852823545)
  ·
    refine ⟨3102252308871929139617659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4136336411829238852823545 3102252308871929139617659)
    ·
      refine ⟨4653378463307893709426489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3102252308871929139617659 4653378463307893709426489)
      ·
        refine ⟨3490033847480920282069867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653378463307893709426489 3490033847480920282069867)
        ·
          refine ⟨5235050771221380423104801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490033847480920282069867 5235050771221380423104801)
          ·
            refine ⟨3926288078416035317328601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235050771221380423104801 3926288078416035317328601)
            ·
              refine ⟨2944716058812026487996451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926288078416035317328601 2944716058812026487996451)
              ·
                refine ⟨4417074088218039731994677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944716058812026487996451 4417074088218039731994677)
                ·
                  refine ⟨414100695770441224874501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4417074088218039731994677 414100695770441224874501)
                  ·
                    rfl

theorem cell22_3629062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3629062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629062 prefixEnd_3629062 := by exact prefixLift 3629062
  have htrace : WordTrace (prefixWord ++ tailWord_3629062) baseStart_3629062 baseEnd_3629062 := by
    simpa [prefixWord, tailWord_3629062, baseEnd_3629062] using wordTrace_append hprefix tailTrace_3629062
  have hstable : (prefixWord ++ tailWord_3629062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629062).length < 2 ^ (prefixWord ++ tailWord_3629062).sum := by decide
  have hdescent : baseEnd_3629062 < baseStart_3629062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629116 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3629116 : Nat := 118140960795 + 3629116 * 2 ^ 59
def prefixEnd_3629116 : Nat := 4983230072969 + 3 ^ 40 * 3629116 * 2
def baseEnd_3629116 : Nat := 1242320572614885533773337

theorem tailTrace_3629116 : CollatzResearch.WordTrace tailWord_3629116 prefixEnd_3629116 1242320572614885533773337 := by
  unfold tailWord_3629116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66182367360170005256409601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88243156480226673675212801 66182367360170005256409601)
  ·
    refine ⟨49636775520127503942307201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66182367360170005256409601 49636775520127503942307201)
    ·
      refine ⟨37227581640095627956730401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49636775520127503942307201 37227581640095627956730401)
      ·
        refine ⟨27920686230071720967547801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37227581640095627956730401 27920686230071720967547801)
        ·
          refine ⟨20940514672553790725660851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27920686230071720967547801 20940514672553790725660851)
          ·
            refine ⟨31410772008830686088491277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20940514672553790725660851 31410772008830686088491277)
            ·
              refine ⟨11779039503311507283184229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31410772008830686088491277 11779039503311507283184229)
              ·
                refine ⟨2208569906870907615597043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11779039503311507283184229 2208569906870907615597043)
                ·
                  refine ⟨3312854860306361423395565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208569906870907615597043 3312854860306361423395565)
                  ·
                    refine ⟨1242320572614885533773337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312854860306361423395565 1242320572614885533773337)
                    ·
                      rfl

theorem cell22_3629116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3629116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629116 prefixEnd_3629116 := by exact prefixLift 3629116
  have htrace : WordTrace (prefixWord ++ tailWord_3629116) baseStart_3629116 baseEnd_3629116 := by
    simpa [prefixWord, tailWord_3629116, baseEnd_3629116] using wordTrace_append hprefix tailTrace_3629116
  have hstable : (prefixWord ++ tailWord_3629116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629116).length < 2 ^ (prefixWord ++ tailWord_3629116).sum := by decide
  have hdescent : baseEnd_3629116 < baseStart_3629116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629127 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3629127 : Nat := 118140960795 + 3629127 * 2 ^ 59
def prefixEnd_3629127 : Nat := 4983230072969 + 3 ^ 40 * 3629127 * 2
def baseEnd_3629127 : Nat := 1242324338139685171748303

theorem tailTrace_3629127 : CollatzResearch.WordTrace tailWord_3629127 prefixEnd_3629127 1242324338139685171748303 := by
  unfold tailWord_3629127
  simp only [CollatzResearch.WordTrace]
  refine ⟨132365135923300159391469635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88243423948866772927646423 132365135923300159391469635)
  ·
    refine ⟨198547703884950239087204453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132365135923300159391469635 198547703884950239087204453)
    ·
      refine ⟨37227694478428169828850835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198547703884950239087204453 37227694478428169828850835)
      ·
        refine ⟨55841541717642254743276253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37227694478428169828850835 55841541717642254743276253)
        ·
          refine ⟨20940578144115845528728595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55841541717642254743276253 20940578144115845528728595)
          ·
            refine ⟨31410867216173768293092893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20940578144115845528728595 31410867216173768293092893)
            ·
              refine ⟨11779075206065163109909835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31410867216173768293092893 11779075206065163109909835)
              ·
                refine ⟨17668612809097744664864753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11779075206065163109909835 17668612809097744664864753)
                ·
                  refine ⟨13251459606823308498648565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17668612809097744664864753 13251459606823308498648565)
                  ·
                    refine ⟨1242324338139685171748303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13251459606823308498648565 1242324338139685171748303)
                    ·
                      rfl

theorem cell22_3629127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3629127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629127 prefixEnd_3629127 := by exact prefixLift 3629127
  have htrace : WordTrace (prefixWord ++ tailWord_3629127) baseStart_3629127 baseEnd_3629127 := by
    simpa [prefixWord, tailWord_3629127, baseEnd_3629127] using wordTrace_append hprefix tailTrace_3629127
  have hstable : (prefixWord ++ tailWord_3629127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629127).length < 2 ^ (prefixWord ++ tailWord_3629127).sum := by decide
  have hdescent : baseEnd_3629127 < baseStart_3629127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629159 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3629159 : Nat := 118140960795 + 3629159 * 2 ^ 59
def prefixEnd_3629159 : Nat := 4983230072969 + 3 ^ 40 * 3629159 * 2
def baseEnd_3629159 : Nat := 1242335292393647754948205

theorem tailTrace_3629159 : CollatzResearch.WordTrace tailWord_3629159 prefixEnd_3629159 1242335292393647754948205 := by
  unfold tailWord_3629159
  simp only [CollatzResearch.WordTrace]
  refine ⟨132366303059184228856634531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88244202039456152571089687 132366303059184228856634531)
  ·
    refine ⟨198549454588776343284951797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132366303059184228856634531 198549454588776343284951797)
    ·
      refine ⟨18614011367697782182964231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198549454588776343284951797 18614011367697782182964231)
      ·
        refine ⟨27921017051546673274446347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18614011367697782182964231 27921017051546673274446347)
        ·
          refine ⟨41881525577320009911669521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27921017051546673274446347 41881525577320009911669521)
          ·
            refine ⟨31411144182990007433752141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41881525577320009911669521 31411144182990007433752141)
            ·
              refine ⟨11779179068621252787657053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31411144182990007433752141 11779179068621252787657053)
              ·
                refine ⟨4417192150732969795371395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11779179068621252787657053 4417192150732969795371395)
                ·
                  refine ⟨6625788226099454693057093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417192150732969795371395 6625788226099454693057093)
                  ·
                    refine ⟨1242335292393647754948205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625788226099454693057093 1242335292393647754948205)
                    ·
                      rfl

theorem cell22_3629159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3629159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629159 prefixEnd_3629159 := by exact prefixLift 3629159
  have htrace : WordTrace (prefixWord ++ tailWord_3629159) baseStart_3629159 baseEnd_3629159 := by
    simpa [prefixWord, tailWord_3629159, baseEnd_3629159] using wordTrace_append hprefix tailTrace_3629159
  have hstable : (prefixWord ++ tailWord_3629159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629159).length < 2 ^ (prefixWord ++ tailWord_3629159).sum := by decide
  have hdescent : baseEnd_3629159 < baseStart_3629159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629174 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_3629174 : Nat := 118140960795 + 3629174 * 2 ^ 59
def prefixEnd_3629174 : Nat := 4983230072969 + 3 ^ 40 * 3629174 * 2
def baseEnd_3629174 : Nat := 414113475733397571941053

theorem tailTrace_3629174 : CollatzResearch.WordTrace tailWord_3629174 prefixEnd_3629174 414113475733397571941053 := by
  unfold tailWord_3629174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272928134633117901151911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88244566769419924278953717 8272928134633117901151911)
  ·
    refine ⟨12409392201949676851727867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272928134633117901151911 12409392201949676851727867)
    ·
      refine ⟨18614088302924515277591801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409392201949676851727867 18614088302924515277591801)
      ·
        refine ⟨13960566227193386458193851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18614088302924515277591801 13960566227193386458193851)
        ·
          refine ⟨20940849340790079687290777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960566227193386458193851 20940849340790079687290777)
          ·
            refine ⟨15705637005592559765468083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20940849340790079687290777 15705637005592559765468083)
            ·
              refine ⟨23558455508388839648202125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15705637005592559765468083 23558455508388839648202125)
              ·
                refine ⟨8834420815645814868075797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23558455508388839648202125 8834420815645814868075797)
                ·
                  refine ⟨414113475733397571941053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8834420815645814868075797 414113475733397571941053)
                  ·
                    rfl

theorem cell22_3629174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_3629174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629174 prefixEnd_3629174 := by exact prefixLift 3629174
  have htrace : WordTrace (prefixWord ++ tailWord_3629174) baseStart_3629174 baseEnd_3629174 := by
    simpa [prefixWord, tailWord_3629174, baseEnd_3629174] using wordTrace_append hprefix tailTrace_3629174
  have hstable : (prefixWord ++ tailWord_3629174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629174).length < 2 ^ (prefixWord ++ tailWord_3629174).sum := by decide
  have hdescent : baseEnd_3629174 < baseStart_3629174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629187 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_3629187 : Nat := 118140960795 + 3629187 * 2 ^ 59
def prefixEnd_3629187 : Nat := 4983230072969 + 3 ^ 40 * 3629187 * 2
def baseEnd_3629187 : Nat := 1242344877365865015248119

theorem tailTrace_3629187 : CollatzResearch.WordTrace tailWord_3629187 prefixEnd_3629187 1242344877365865015248119 := by
  unfold tailWord_3629187
  simp only [CollatzResearch.WordTrace]
  refine ⟨132367324303082789638653815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88244882868721859759102543 132367324303082789638653815)
  ·
    refine ⟨198550986454624184457980723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132367324303082789638653815 198550986454624184457980723)
    ·
      refine ⟨297826479681936276686971085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198550986454624184457980723 297826479681936276686971085)
      ·
        refine ⟨111684929880726103757614157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297826479681936276686971085 111684929880726103757614157)
        ·
          refine ⟨41881848705272288909105309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111684929880726103757614157 41881848705272288909105309)
          ·
            refine ⟨15705693264477108340914491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41881848705272288909105309 15705693264477108340914491)
            ·
              refine ⟨23558539896715662511371737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15705693264477108340914491 23558539896715662511371737)
              ·
                refine ⟨17668904922536746883528803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23558539896715662511371737 17668904922536746883528803)
                ·
                  refine ⟨26503357383805120325293205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17668904922536746883528803 26503357383805120325293205)
                  ·
                    refine ⟨1242344877365865015248119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26503357383805120325293205 1242344877365865015248119)
                    ·
                      rfl

theorem cell22_3629187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_3629187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629187 prefixEnd_3629187 := by exact prefixLift 3629187
  have htrace : WordTrace (prefixWord ++ tailWord_3629187) baseStart_3629187 baseEnd_3629187 := by
    simpa [prefixWord, tailWord_3629187, baseEnd_3629187] using wordTrace_append hprefix tailTrace_3629187
  have hstable : (prefixWord ++ tailWord_3629187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629187).length < 2 ^ (prefixWord ++ tailWord_3629187).sum := by decide
  have hdescent : baseEnd_3629187 < baseStart_3629187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629189 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3629189 : Nat := 118140960795 + 3629189 * 2 ^ 59
def prefixEnd_3629189 : Nat := 4983230072969 + 3 ^ 40 * 3629189 * 2
def baseEnd_3629189 : Nat := 1242345562006737676698113

theorem tailTrace_3629189 : CollatzResearch.WordTrace tailWord_3629189 prefixEnd_3629189 1242345562006737676698113 := by
  unfold tailWord_3629189
  simp only [CollatzResearch.WordTrace]
  refine ⟨132367397249075543980226621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88244931499383695986817747 132367397249075543980226621)
  ·
    refine ⟨49637773968403328992584983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132367397249075543980226621 49637773968403328992584983)
    ·
      refine ⟨74456660952604993488877475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49637773968403328992584983 74456660952604993488877475)
      ·
        refine ⟨111684991428907490233316213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74456660952604993488877475 111684991428907490233316213)
        ·
          refine ⟨10470467946460077209373395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111684991428907490233316213 10470467946460077209373395)
          ·
            refine ⟨15705701919690115814060093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470467946460077209373395 15705701919690115814060093)
            ·
              refine ⟨5889638219883793430272535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15705701919690115814060093 5889638219883793430272535)
              ·
                refine ⟨8834457329825690145408803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889638219883793430272535 8834457329825690145408803)
                ·
                  refine ⟨13251685994738535218113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834457329825690145408803 13251685994738535218113205)
                  ·
                    refine ⟨1242345562006737676698113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13251685994738535218113205 1242345562006737676698113)
                    ·
                      rfl

theorem cell22_3629189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3629189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629189 prefixEnd_3629189 := by exact prefixLift 3629189
  have htrace : WordTrace (prefixWord ++ tailWord_3629189) baseStart_3629189 baseEnd_3629189 := by
    simpa [prefixWord, tailWord_3629189, baseEnd_3629189] using wordTrace_append hprefix tailTrace_3629189
  have hstable : (prefixWord ++ tailWord_3629189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629189).length < 2 ^ (prefixWord ++ tailWord_3629189).sum := by decide
  have hdescent : baseEnd_3629189 < baseStart_3629189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629208 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_3629208 : Nat := 118140960795 + 3629208 * 2 ^ 59
def prefixEnd_3629208 : Nat := 4983230072969 + 3 ^ 40 * 3629208 * 2
def baseEnd_3629208 : Nat := 414117355365009320157685

theorem tailTrace_3629208 : CollatzResearch.WordTrace tailWord_3629208 prefixEnd_3629208 414117355365009320157685 := by
  unfold tailWord_3629208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66184045118003355112584139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88245393490671140150112185 66184045118003355112584139)
  ·
    refine ⟨99276067677005032668876209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66184045118003355112584139 99276067677005032668876209)
    ·
      refine ⟨74457050757753774501657157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99276067677005032668876209 74457050757753774501657157)
      ·
        refine ⟨13960697017078832719060717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74457050757753774501657157 13960697017078832719060717)
        ·
          refine ⟨5235261381404562269647769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13960697017078832719060717 5235261381404562269647769)
          ·
            refine ⟨3926446036053421702235827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235261381404562269647769 3926446036053421702235827)
            ·
              refine ⟨5889669054080132553353741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926446036053421702235827 5889669054080132553353741)
              ·
                refine ⟨2208625895280049707507653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889669054080132553353741 2208625895280049707507653)
                ·
                  refine ⟨414117355365009320157685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208625895280049707507653 414117355365009320157685)
                  ·
                    rfl

theorem cell22_3629208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_3629208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629208 prefixEnd_3629208 := by exact prefixLift 3629208
  have htrace : WordTrace (prefixWord ++ tailWord_3629208) baseStart_3629208 baseEnd_3629208 := by
    simpa [prefixWord, tailWord_3629208, baseEnd_3629208] using wordTrace_append hprefix tailTrace_3629208
  have hstable : (prefixWord ++ tailWord_3629208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629208).length < 2 ^ (prefixWord ++ tailWord_3629208).sum := by decide
  have hdescent : baseEnd_3629208 < baseStart_3629208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629285 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_3629285 : Nat := 118140960795 + 3629285 * 2 ^ 59
def prefixEnd_3629285 : Nat := 4983230072969 + 3 ^ 40 * 3629285 * 2
def baseEnd_3629285 : Nat := 1242378424768625426297819

theorem tailTrace_3629285 : CollatzResearch.WordTrace tailWord_3629285 prefixEnd_3629285 1242378424768625426297819 := by
  unfold tailWord_3629285
  simp only [CollatzResearch.WordTrace]
  refine ⟨132370898656727752375721309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88247265771151834917147539 132370898656727752375721309)
  ·
    refine ⟨49639086996272907140895491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132370898656727752375721309 49639086996272907140895491)
    ·
      refine ⟨74458630494409360711343237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49639086996272907140895491 74458630494409360711343237)
      ·
        refine ⟨13960993217701755133376857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74458630494409360711343237 13960993217701755133376857)
        ·
          refine ⟨10470744913276316350032643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13960993217701755133376857 10470744913276316350032643)
          ·
            refine ⟨15706117369914474525048965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470744913276316350032643 15706117369914474525048965)
            ·
              refine ⟨2944897006858963973446681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15706117369914474525048965 2944897006858963973446681)
              ·
                refine ⟨2208672755144222980085011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944897006858963973446681 2208672755144222980085011)
                ·
                  refine ⟨3313009132716334470127517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208672755144222980085011 3313009132716334470127517)
                  ·
                    refine ⟨1242378424768625426297819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313009132716334470127517 1242378424768625426297819)
                    ·
                      rfl

theorem cell22_3629285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_3629285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629285 prefixEnd_3629285 := by exact prefixLift 3629285
  have htrace : WordTrace (prefixWord ++ tailWord_3629285) baseStart_3629285 baseEnd_3629285 := by
    simpa [prefixWord, tailWord_3629285, baseEnd_3629285] using wordTrace_append hprefix tailTrace_3629285
  have hstable : (prefixWord ++ tailWord_3629285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629285).length < 2 ^ (prefixWord ++ tailWord_3629285).sum := by decide
  have hdescent : baseEnd_3629285 < baseStart_3629285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629324 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_3629324 : Nat := 118140960795 + 3629324 * 2 ^ 59
def prefixEnd_3629324 : Nat := 4983230072969 + 3 ^ 40 * 3629324 * 2
def baseEnd_3629324 : Nat := 1242391775265642324572699

theorem tailTrace_3629324 : CollatzResearch.WordTrace tailWord_3629324 prefixEnd_3629324 1242391775265642324572699 := by
  unfold tailWord_3629324
  simp only [CollatzResearch.WordTrace]
  refine ⟨66186160551793231018195513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88248214069057641357594017 66186160551793231018195513)
  ·
    refine ⟨49639620413844923263646635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66186160551793231018195513 49639620413844923263646635)
    ·
      refine ⟨74459430620767384895469953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49639620413844923263646635 74459430620767384895469953)
      ·
        refine ⟨55844572965575538671602465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74459430620767384895469953 55844572965575538671602465)
        ·
          refine ⟨41883429724181654003701849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55844572965575538671602465 41883429724181654003701849)
          ·
            refine ⟨31412572293136240502776387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41883429724181654003701849 31412572293136240502776387)
            ·
              refine ⟨47118858439704360754164581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31412572293136240502776387 47118858439704360754164581)
              ·
                refine ⟨8834785957444567641405859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47118858439704360754164581 8834785957444567641405859)
                ·
                  refine ⟨13252178936166851462108789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834785957444567641405859 13252178936166851462108789)
                  ·
                    refine ⟨1242391775265642324572699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13252178936166851462108789 1242391775265642324572699)
                    ·
                      rfl

theorem cell22_3629324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_3629324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629324 prefixEnd_3629324 := by exact prefixLift 3629324
  have htrace : WordTrace (prefixWord ++ tailWord_3629324) baseStart_3629324 baseEnd_3629324 := by
    simpa [prefixWord, tailWord_3629324, baseEnd_3629324] using wordTrace_append hprefix tailTrace_3629324
  have hstable : (prefixWord ++ tailWord_3629324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629324).length < 2 ^ (prefixWord ++ tailWord_3629324).sum := by decide
  have hdescent : baseEnd_3629324 < baseStart_3629324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629339 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_3629339 : Nat := 118140960795 + 3629339 * 2 ^ 59
def prefixEnd_3629339 : Nat := 4983230072969 + 3 ^ 40 * 3629339 * 2
def baseEnd_3629339 : Nat := 1242396910072187285447653

theorem tailTrace_3629339 : CollatzResearch.WordTrace tailWord_3629339 prefixEnd_3629339 1242396910072187285447653 := by
  unfold tailWord_3629339
  simp only [CollatzResearch.WordTrace]
  refine ⟨132372868198532119598187071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88248578799021413065458047 132372868198532119598187071)
  ·
    refine ⟨198559302297798179397280607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132372868198532119598187071 198559302297798179397280607)
    ·
      refine ⟨297838953446697269095920911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198559302297798179397280607 297838953446697269095920911)
      ·
        refine ⟨446758430170045903643881367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297838953446697269095920911 446758430170045903643881367)
        ·
          refine ⟨670137645255068855465822051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446758430170045903643881367 670137645255068855465822051)
          ·
            refine ⟨1005206467882603283198733077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670137645255068855465822051 1005206467882603283198733077)
            ·
              refine ⟨47119053181997028899940613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1005206467882603283198733077 47119053181997028899940613)
              ·
                refine ⟨8834822471624442918738865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47119053181997028899940613 8834822471624442918738865)
                ·
                  refine ⟨6626116853718332189054149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8834822471624442918738865 6626116853718332189054149)
                  ·
                    refine ⟨1242396910072187285447653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6626116853718332189054149 1242396910072187285447653)
                    ·
                      rfl

theorem cell22_3629339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_3629339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629339 prefixEnd_3629339 := by exact prefixLift 3629339
  have htrace : WordTrace (prefixWord ++ tailWord_3629339) baseStart_3629339 baseEnd_3629339 := by
    simpa [prefixWord, tailWord_3629339, baseEnd_3629339] using wordTrace_append hprefix tailTrace_3629339
  have hstable : (prefixWord ++ tailWord_3629339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629339).length < 2 ^ (prefixWord ++ tailWord_3629339).sum := by decide
  have hdescent : baseEnd_3629339 < baseStart_3629339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629377 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 4]
def baseStart_3629377 : Nat := 118140960795 + 3629377 * 2 ^ 59
def prefixEnd_3629377 : Nat := 4983230072969 + 3 ^ 40 * 3629377 * 2
def baseEnd_3629377 : Nat := 414136639416255950999179

theorem tailTrace_3629377 : CollatzResearch.WordTrace tailWord_3629377 prefixEnd_3629377 414136639416255950999179 := by
  unfold tailWord_3629377
  simp only [CollatzResearch.WordTrace]
  refine ⟨132374254172394452088070385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88249502781596301392046923 132374254172394452088070385)
  ·
    refine ⟨99280690629295839066052789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132374254172394452088070385 99280690629295839066052789)
    ·
      refine ⟨9307564746496484912442449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99280690629295839066052789 9307564746496484912442449)
      ·
        refine ⟨6980673559872363684331837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9307564746496484912442449 6980673559872363684331837)
        ·
          refine ⟨2617752584952136381624439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6980673559872363684331837 2617752584952136381624439)
          ·
            refine ⟨3926628877428204572436659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617752584952136381624439 3926628877428204572436659)
            ·
              refine ⟨5889943316142306858654989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926628877428204572436659 5889943316142306858654989)
              ·
                refine ⟨2208728743553365071995621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889943316142306858654989 2208728743553365071995621)
                ·
                  refine ⟨414136639416255950999179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208728743553365071995621 414136639416255950999179)
                  ·
                    rfl

theorem cell22_3629377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_3629377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629377 prefixEnd_3629377 := by exact prefixLift 3629377
  have htrace : WordTrace (prefixWord ++ tailWord_3629377) baseStart_3629377 baseEnd_3629377 := by
    simpa [prefixWord, tailWord_3629377, baseEnd_3629377] using wordTrace_append hprefix tailTrace_3629377
  have hstable : (prefixWord ++ tailWord_3629377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629377).length < 2 ^ (prefixWord ++ tailWord_3629377).sum := by decide
  have hdescent : baseEnd_3629377 < baseStart_3629377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629399 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 7]
def baseStart_3629399 : Nat := 118140960795 + 3629399 * 2 ^ 59
def prefixEnd_3629399 : Nat := 4983230072969 + 3 ^ 40 * 3629399 * 2
def baseEnd_3629399 : Nat := 414139149766122376315823

theorem tailTrace_3629399 : CollatzResearch.WordTrace tailWord_3629399 prefixEnd_3629399 414139149766122376315823 := by
  unfold tailWord_3629399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132375056578314749845371251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88250037718876499896914167 132375056578314749845371251)
  ·
    refine ⟨198562584867472124768056877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132375056578314749845371251 198562584867472124768056877)
    ·
      refine ⟨74460969325302046788021329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198562584867472124768056877 74460969325302046788021329)
      ·
        refine ⟨55845726993976535091015997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74460969325302046788021329 55845726993976535091015997)
        ·
          refine ⟨20942147622741200659130999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55845726993976535091015997 20942147622741200659130999)
          ·
            refine ⟨31413221434111800988696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20942147622741200659130999 31413221434111800988696499)
            ·
              refine ⟨47119832151167701483044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31413221434111800988696499 47119832151167701483044749)
              ·
                refine ⟨17669937056687888056141781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47119832151167701483044749 17669937056687888056141781)
                ·
                  refine ⟨414139149766122376315823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17669937056687888056141781 414139149766122376315823)
                  ·
                    rfl

theorem cell22_3629399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_3629399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629399 prefixEnd_3629399 := by exact prefixLift 3629399
  have htrace : WordTrace (prefixWord ++ tailWord_3629399) baseStart_3629399 baseEnd_3629399 := by
    simpa [prefixWord, tailWord_3629399, baseEnd_3629399] using wordTrace_append hprefix tailTrace_3629399
  have hstable : (prefixWord ++ tailWord_3629399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629399).length < 2 ^ (prefixWord ++ tailWord_3629399).sum := by decide
  have hdescent : baseEnd_3629399 < baseStart_3629399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629450 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_3629450 : Nat := 118140960795 + 3629450 * 2 ^ 59
def prefixEnd_3629450 : Nat := 4983230072969 + 3 ^ 40 * 3629450 * 2
def baseEnd_3629450 : Nat := 414144969213539998640771

theorem tailTrace_3629450 : CollatzResearch.WordTrace tailWord_3629450 prefixEnd_3629450 414144969213539998640771 := by
  unfold tailWord_3629450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094229175282496388869451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88251277800753323703651869 33094229175282496388869451)
  ·
    refine ⟨49641343762923744583304177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33094229175282496388869451 49641343762923744583304177)
    ·
      refine ⟨37231007822192808437478133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49641343762923744583304177 37231007822192808437478133)
      ·
        refine ⟨3490406983330575791013575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37231007822192808437478133 3490406983330575791013575)
        ·
          refine ⟨5235610474995863686520363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490406983330575791013575 5235610474995863686520363)
          ·
            refine ⟨7853415712493795529780545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235610474995863686520363 7853415712493795529780545)
            ·
              refine ⟨5890061784370346647335409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853415712493795529780545 5890061784370346647335409)
              ·
                refine ⟨4417546338277759985501557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890061784370346647335409 4417546338277759985501557)
                ·
                  refine ⟨414144969213539998640771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4417546338277759985501557 414144969213539998640771)
                  ·
                    rfl

theorem cell22_3629450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_3629450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629450 prefixEnd_3629450 := by exact prefixLift 3629450
  have htrace : WordTrace (prefixWord ++ tailWord_3629450) baseStart_3629450 baseEnd_3629450 := by
    simpa [prefixWord, tailWord_3629450, baseEnd_3629450] using wordTrace_append hprefix tailTrace_3629450
  have hstable : (prefixWord ++ tailWord_3629450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629450).length < 2 ^ (prefixWord ++ tailWord_3629450).sum := by decide
  have hdescent : baseEnd_3629450 < baseStart_3629450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629454 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_3629454 : Nat := 118140960795 + 3629454 * 2 ^ 59
def prefixEnd_3629454 : Nat := 4983230072969 + 3 ^ 40 * 3629454 * 2
def baseEnd_3629454 : Nat := 1242436276922365318822301

theorem tailTrace_3629454 : CollatzResearch.WordTrace tailWord_3629454 prefixEnd_3629454 1242436276922365318822301 := by
  unfold tailWord_3629454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16547132824139436779827927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88251375062076996159082277 16547132824139436779827927)
  ·
    refine ⟨24820699236209155169741891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16547132824139436779827927 24820699236209155169741891)
    ·
      refine ⟨37231048854313732754612837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820699236209155169741891 37231048854313732754612837)
      ·
        refine ⟨6980821660183824891489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37231048854313732754612837 6980821660183824891489907)
        ·
          refine ⟨10471232490275737337234861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980821660183824891489907 10471232490275737337234861)
          ·
            refine ⟨3926712183853401501463073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10471232490275737337234861 3926712183853401501463073)
            ·
              refine ⟨2945034137890051126097305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926712183853401501463073 2945034137890051126097305)
              ·
                refine ⟨2208775603417538344572979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945034137890051126097305 2208775603417538344572979)
                ·
                  refine ⟨3313163405126307516859469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208775603417538344572979 3313163405126307516859469)
                  ·
                    refine ⟨1242436276922365318822301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313163405126307516859469 1242436276922365318822301)
                    ·
                      rfl

theorem cell22_3629454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_3629454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629454 prefixEnd_3629454 := by exact prefixLift 3629454
  have htrace : WordTrace (prefixWord ++ tailWord_3629454) baseStart_3629454 baseEnd_3629454 := by
    simpa [prefixWord, tailWord_3629454, baseEnd_3629454] using wordTrace_append hprefix tailTrace_3629454
  have hstable : (prefixWord ++ tailWord_3629454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629454).length < 2 ^ (prefixWord ++ tailWord_3629454).sum := by decide
  have hdescent : baseEnd_3629454 < baseStart_3629454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629476 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3629476 : Nat := 118140960795 + 3629476 * 2 ^ 59
def prefixEnd_3629476 : Nat := 4983230072969 + 3 ^ 40 * 3629476 * 2
def baseEnd_3629476 : Nat := 1242443807971964594772233

theorem tailTrace_3629476 : CollatzResearch.WordTrace tailWord_3629476 prefixEnd_3629476 1242443807971964594772233 := by
  unfold tailWord_3629476
  simp only [CollatzResearch.WordTrace]
  refine ⟨66188932499517895997962141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88251909999357194663949521 66188932499517895997962141)
  ·
    refine ⟨24820849687319210999235803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66188932499517895997962141 24820849687319210999235803)
    ·
      refine ⟨37231274530978816498853705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820849687319210999235803 37231274530978816498853705)
      ·
        refine ⟨27923455898234112374140279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37231274530978816498853705 27923455898234112374140279)
        ·
          refine ⟨41885183847351168561210419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27923455898234112374140279 41885183847351168561210419)
          ·
            refine ⟨62827775771026752841815629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41885183847351168561210419 62827775771026752841815629)
            ·
              refine ⟨23560415914135032315680861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62827775771026752841815629 23560415914135032315680861)
              ·
                refine ⟨8835155967800637118380323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23560415914135032315680861 8835155967800637118380323)
                ·
                  refine ⟨13252733951700955677570485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835155967800637118380323 13252733951700955677570485)
                  ·
                    refine ⟨1242443807971964594772233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13252733951700955677570485 1242443807971964594772233)
                    ·
                      rfl

theorem cell22_3629476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3629476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629476 prefixEnd_3629476 := by exact prefixLift 3629476
  have htrace : WordTrace (prefixWord ++ tailWord_3629476) baseStart_3629476 baseEnd_3629476 := by
    simpa [prefixWord, tailWord_3629476, baseEnd_3629476] using wordTrace_append hprefix tailTrace_3629476
  have hstable : (prefixWord ++ tailWord_3629476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629476).length < 2 ^ (prefixWord ++ tailWord_3629476).sum := by decide
  have hdescent : baseEnd_3629476 < baseStart_3629476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629572 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3629572 : Nat := 118140960795 + 3629572 * 2 ^ 59
def prefixEnd_3629572 : Nat := 4983230072969 + 3 ^ 40 * 3629572 * 2
def baseEnd_3629572 : Nat := 1242476670733852344371939

theorem tailTrace_3629572 : CollatzResearch.WordTrace tailWord_3629572 prefixEnd_3629572 1242476670733852344371939 := by
  unfold tailWord_3629572
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190683203344000195709485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88254244271125333594279313 66190683203344000195709485)
  ·
    refine ⟨24821506201254000073391057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66190683203344000195709485 24821506201254000073391057)
    ·
      refine ⟨18616129650940500055043293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24821506201254000073391057 18616129650940500055043293)
      ·
        refine ⟨6981048619102687520641235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18616129650940500055043293 6981048619102687520641235)
        ·
          refine ⟨10471572928654031280961853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981048619102687520641235 10471572928654031280961853)
          ·
            refine ⟨3926839848245261730360695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10471572928654031280961853 3926839848245261730360695)
            ·
              refine ⟨5890259772367892595541043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926839848245261730360695 5890259772367892595541043)
              ·
                refine ⟨8835389658551838893311565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890259772367892595541043 8835389658551838893311565)
                ·
                  refine ⟨3313271121956939584991837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8835389658551838893311565 3313271121956939584991837)
                  ·
                    refine ⟨1242476670733852344371939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313271121956939584991837 1242476670733852344371939)
                    ·
                      rfl

theorem cell22_3629572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3629572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629572 prefixEnd_3629572 := by exact prefixLift 3629572
  have htrace : WordTrace (prefixWord ++ tailWord_3629572) baseStart_3629572 baseEnd_3629572 := by
    simpa [prefixWord, tailWord_3629572, baseEnd_3629572] using wordTrace_append hprefix tailTrace_3629572
  have hstable : (prefixWord ++ tailWord_3629572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629572).length < 2 ^ (prefixWord ++ tailWord_3629572).sum := by decide
  have hdescent : baseEnd_3629572 < baseStart_3629572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629645 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3629645 : Nat := 118140960795 + 3629645 * 2 ^ 59
def prefixEnd_3629645 : Nat := 4983230072969 + 3 ^ 40 * 3629645 * 2
def baseEnd_3629645 : Nat := 1242501660125704487296715

theorem tailTrace_3629645 : CollatzResearch.WordTrace tailWord_3629645 prefixEnd_3629645 1242501660125704487296715 := by
  unfold tailWord_3629645
  simp only [CollatzResearch.WordTrace]
  refine ⟨132384028935423533858826389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88256019290282355905884259 132384028935423533858826389)
  ·
    refine ⟨6205501356347978149632487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132384028935423533858826389 6205501356347978149632487)
    ·
      refine ⟨9308252034521967224448731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205501356347978149632487 9308252034521967224448731)
      ·
        refine ⟨13962378051782950836673097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308252034521967224448731 13962378051782950836673097)
        ·
          refine ⟨10471783538837213127504823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13962378051782950836673097 10471783538837213127504823)
          ·
            refine ⟨15707675308255819691257235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10471783538837213127504823 15707675308255819691257235)
            ·
              refine ⟨23561512962383729536885853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15707675308255819691257235 23561512962383729536885853)
              ·
                refine ⟨8835567360893898576332195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23561512962383729536885853 8835567360893898576332195)
                ·
                  refine ⟨13253351041340847864498293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835567360893898576332195 13253351041340847864498293)
                  ·
                    refine ⟨1242501660125704487296715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13253351041340847864498293 1242501660125704487296715)
                    ·
                      rfl

theorem cell22_3629645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3629645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629645 prefixEnd_3629645 := by exact prefixLift 3629645
  have htrace : WordTrace (prefixWord ++ tailWord_3629645) baseStart_3629645 baseEnd_3629645 := by
    simpa [prefixWord, tailWord_3629645, baseEnd_3629645] using wordTrace_append hprefix tailTrace_3629645
  have hstable : (prefixWord ++ tailWord_3629645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629645).length < 2 ^ (prefixWord ++ tailWord_3629645).sum := by decide
  have hdescent : baseEnd_3629645 < baseStart_3629645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629660 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3629660 : Nat := 118140960795 + 3629660 * 2 ^ 59
def prefixEnd_3629660 : Nat := 4983230072969 + 3 ^ 40 * 3629660 * 2
def baseEnd_3629660 : Nat := 1242506794932249448171669

theorem tailTrace_3629660 : CollatzResearch.WordTrace tailWord_3629660 prefixEnd_3629660 1242506794932249448171669 := by
  unfold tailWord_3629660
  simp only [CollatzResearch.WordTrace]
  refine ⟨66192288015184595710311217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88256384020246127613748289 66192288015184595710311217)
  ·
    refine ⟨49644216011388446782733413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66192288015184595710311217 49644216011388446782733413)
    ·
      refine ⟨9308290502135333771762515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49644216011388446782733413 9308290502135333771762515)
      ·
        refine ⟨13962435753203000657643773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308290502135333771762515 13962435753203000657643773)
        ·
          refine ⟨5235913407451125246616415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13962435753203000657643773 5235913407451125246616415)
          ·
            refine ⟨7853870111176687869924623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235913407451125246616415 7853870111176687869924623)
            ·
              refine ⟨11780805166765031804886935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853870111176687869924623 11780805166765031804886935)
              ·
                refine ⟨17671207750147547707330403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11780805166765031804886935 17671207750147547707330403)
                ·
                  refine ⟨26506811625221321560995605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17671207750147547707330403 26506811625221321560995605)
                  ·
                    refine ⟨1242506794932249448171669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26506811625221321560995605 1242506794932249448171669)
                    ·
                      rfl

theorem cell22_3629660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3629660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629660 prefixEnd_3629660 := by exact prefixLift 3629660
  have htrace : WordTrace (prefixWord ++ tailWord_3629660) baseStart_3629660 baseEnd_3629660 := by
    simpa [prefixWord, tailWord_3629660, baseEnd_3629660] using wordTrace_append hprefix tailTrace_3629660
  have hstable : (prefixWord ++ tailWord_3629660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629660).length < 2 ^ (prefixWord ++ tailWord_3629660).sum := by decide
  have hdescent : baseEnd_3629660 < baseStart_3629660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629666 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3629666 : Nat := 118140960795 + 3629666 * 2 ^ 59
def prefixEnd_3629666 : Nat := 4983230072969 + 3 ^ 40 * 3629666 * 2
def baseEnd_3629666 : Nat := 1242508848854867432521651

theorem tailTrace_3629666 : CollatzResearch.WordTrace tailWord_3629666 prefixEnd_3629666 1242508848854867432521651 := by
  unfold tailWord_3629666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33096198717086863611335213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88256529912231636296893901 33096198717086863611335213)
  ·
    refine ⟨12411074518907573854250705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33096198717086863611335213 12411074518907573854250705)
    ·
      refine ⟨9308305889180680390688029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12411074518907573854250705 9308305889180680390688029)
      ·
        refine ⟨3490614708442755146508011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9308305889180680390688029 3490614708442755146508011)
        ·
          refine ⟨5235922062664132719762017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490614708442755146508011 5235922062664132719762017)
          ·
            refine ⟨3926941546998099539821513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235922062664132719762017 3926941546998099539821513)
            ·
              refine ⟨2945206160248574654866135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926941546998099539821513 2945206160248574654866135)
              ·
                refine ⟨4417809240372861982299203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945206160248574654866135 4417809240372861982299203)
                ·
                  refine ⟨6626713860559292973448805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417809240372861982299203 6626713860559292973448805)
                  ·
                    refine ⟨1242508848854867432521651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6626713860559292973448805 1242508848854867432521651)
                    ·
                      rfl

theorem cell22_3629666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3629666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629666 prefixEnd_3629666 := by exact prefixLift 3629666
  have htrace : WordTrace (prefixWord ++ tailWord_3629666) baseStart_3629666 baseEnd_3629666 := by
    simpa [prefixWord, tailWord_3629666, baseEnd_3629666] using wordTrace_append hprefix tailTrace_3629666
  have hstable : (prefixWord ++ tailWord_3629666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629666).length < 2 ^ (prefixWord ++ tailWord_3629666).sum := by decide
  have hdescent : baseEnd_3629666 < baseStart_3629666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629673 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_3629673 : Nat := 118140960795 + 3629673 * 2 ^ 59
def prefixEnd_3629673 : Nat := 4983230072969 + 3 ^ 40 * 3629673 * 2
def baseEnd_3629673 : Nat := 1242511245097921747596629

theorem tailTrace_3629673 : CollatzResearch.WordTrace tailWord_3629673 prefixEnd_3629673 1242511245097921747596629 := by
  unfold tailWord_3629673
  simp only [CollatzResearch.WordTrace]
  refine ⟨132385050179322094640845673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88256700119548063093897115 132385050179322094640845673)
  ·
    refine ⟨99288787634491570980634255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132385050179322094640845673 99288787634491570980634255)
    ·
      refine ⟨148933181451737356470951383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99288787634491570980634255 148933181451737356470951383)
      ·
        refine ⟨223399772177606034706427075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148933181451737356470951383 223399772177606034706427075)
        ·
          refine ⟨335099658266409052059640613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223399772177606034706427075 335099658266409052059640613)
          ·
            refine ⟨62831185924951697261182615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335099658266409052059640613 62831185924951697261182615)
            ·
              refine ⟨94246778887427545891773923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62831185924951697261182615 94246778887427545891773923)
              ·
                refine ⟨141370168331141318837660885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94246778887427545891773923 141370168331141318837660885)
                ·
                  refine ⟨3313363320261124660257677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141370168331141318837660885 3313363320261124660257677)
                  ·
                    refine ⟨1242511245097921747596629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313363320261124660257677 1242511245097921747596629)
                    ·
                      rfl

theorem cell22_3629673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_3629673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629673 prefixEnd_3629673 := by exact prefixLift 3629673
  have htrace : WordTrace (prefixWord ++ tailWord_3629673) baseStart_3629673 baseEnd_3629673 := by
    simpa [prefixWord, tailWord_3629673, baseEnd_3629673] using wordTrace_append hprefix tailTrace_3629673
  have hstable : (prefixWord ++ tailWord_3629673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629673).length < 2 ^ (prefixWord ++ tailWord_3629673).sum := by decide
  have hdescent : baseEnd_3629673 < baseStart_3629673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629724 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3629724 : Nat := 118140960795 + 3629724 * 2 ^ 59
def prefixEnd_3629724 : Nat := 4983230072969 + 3 ^ 40 * 3629724 * 2
def baseEnd_3629724 : Nat := 1242528703440174614571473

theorem tailTrace_3629724 : CollatzResearch.WordTrace tailWord_3629724 prefixEnd_3629724 1242528703440174614571473 := by
  unfold tailWord_3629724
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193455151068665175476113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88257940201424886900634817 66193455151068665175476113)
  ·
    refine ⟨49645091363301498881607085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66193455151068665175476113 49645091363301498881607085)
    ·
      refine ⟨18616909261238062080602657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49645091363301498881607085 18616909261238062080602657)
      ·
        refine ⟨13962681945928546560451993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18616909261238062080602657 13962681945928546560451993)
        ·
          refine ⟨10472011459446409920338995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13962681945928546560451993 10472011459446409920338995)
          ·
            refine ⟨15708017189169614880508493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472011459446409920338995 15708017189169614880508493)
            ·
              refine ⟨5890506445938605580190685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15708017189169614880508493 5890506445938605580190685)
              ·
                refine ⟨2208939917226977092571507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5890506445938605580190685 2208939917226977092571507)
                ·
                  refine ⟨3313409875840465638857261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208939917226977092571507 3313409875840465638857261)
                  ·
                    refine ⟨1242528703440174614571473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313409875840465638857261 1242528703440174614571473)
                    ·
                      rfl

theorem cell22_3629724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3629724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629724 prefixEnd_3629724 := by exact prefixLift 3629724
  have htrace : WordTrace (prefixWord ++ tailWord_3629724) baseStart_3629724 baseEnd_3629724 := by
    simpa [prefixWord, tailWord_3629724, baseEnd_3629724] using wordTrace_append hprefix tailTrace_3629724
  have hstable : (prefixWord ++ tailWord_3629724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629724).length < 2 ^ (prefixWord ++ tailWord_3629724).sum := by decide
  have hdescent : baseEnd_3629724 < baseStart_3629724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629733 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3629733 : Nat := 118140960795 + 3629733 * 2 ^ 59
def prefixEnd_3629733 : Nat := 4983230072969 + 3 ^ 40 * 3629733 * 2
def baseEnd_3629733 : Nat := 1242531784324101591096445

theorem tailTrace_3629733 : CollatzResearch.WordTrace tailWord_3629733 prefixEnd_3629733 1242531784324101591096445 := by
  unfold tailWord_3629733
  simp only [CollatzResearch.WordTrace]
  refine ⟨132387238559104724888029853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88258159039403149925353235 132387238559104724888029853)
  ·
    refine ⟨49645214459664271833011195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132387238559104724888029853 49645214459664271833011195)
    ·
      refine ⟨74467821689496407749516793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49645214459664271833011195 74467821689496407749516793)
      ·
        refine ⟨55850866267122305812137595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74467821689496407749516793 55850866267122305812137595)
        ·
          refine ⟨83776299400683458718206393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55850866267122305812137595 83776299400683458718206393)
          ·
            refine ⟨62832224550512594038654795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83776299400683458718206393 62832224550512594038654795)
            ·
              refine ⟨94248336825768891057982193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62832224550512594038654795 94248336825768891057982193)
              ·
                refine ⟨70686252619326668293486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94248336825768891057982193 70686252619326668293486645)
                ·
                  refine ⟨6626836183061875152514373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70686252619326668293486645 6626836183061875152514373)
                  ·
                    refine ⟨1242531784324101591096445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6626836183061875152514373 1242531784324101591096445)
                    ·
                      rfl

theorem cell22_3629733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3629733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629733 prefixEnd_3629733 := by exact prefixLift 3629733
  have htrace : WordTrace (prefixWord ++ tailWord_3629733) baseStart_3629733 baseEnd_3629733 := by
    simpa [prefixWord, tailWord_3629733, baseEnd_3629733] using wordTrace_append hprefix tailTrace_3629733
  have hstable : (prefixWord ++ tailWord_3629733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629733).length < 2 ^ (prefixWord ++ tailWord_3629733).sum := by decide
  have hdescent : baseEnd_3629733 < baseStart_3629733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629741 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3629741 : Nat := 118140960795 + 3629741 * 2 ^ 59
def prefixEnd_3629741 : Nat := 4983230072969 + 3 ^ 40 * 3629741 * 2
def baseEnd_3629741 : Nat := 1242534522887592236896421

theorem tailTrace_3629741 : CollatzResearch.WordTrace tailWord_3629741 prefixEnd_3629741 1242534522887592236896421 := by
  unfold tailWord_3629741
  simp only [CollatzResearch.WordTrace]
  refine ⟨132387530343075742254321077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88258353562050494836214051 132387530343075742254321077)
  ·
    refine ⟨12411330969663350836342601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132387530343075742254321077 12411330969663350836342601)
    ·
      refine ⟨9308498227247513127256951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12411330969663350836342601 9308498227247513127256951)
      ·
        refine ⟨13962747340871269690885427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308498227247513127256951 13962747340871269690885427)
        ·
          refine ⟨20944121011306904536328141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13962747340871269690885427 20944121011306904536328141)
          ·
            refine ⟨7854045379240089201123053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20944121011306904536328141 7854045379240089201123053)
            ·
              refine ⟨2945267017215033450421145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7854045379240089201123053 2945267017215033450421145)
              ·
                refine ⟨2208950262911275087815859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945267017215033450421145 2208950262911275087815859)
                ·
                  refine ⟨3313425394366912631723789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208950262911275087815859 3313425394366912631723789)
                  ·
                    refine ⟨1242534522887592236896421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313425394366912631723789 1242534522887592236896421)
                    ·
                      rfl

theorem cell22_3629741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3629741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629741 prefixEnd_3629741 := by exact prefixLift 3629741
  have htrace : WordTrace (prefixWord ++ tailWord_3629741) baseStart_3629741 baseEnd_3629741 := by
    simpa [prefixWord, tailWord_3629741, baseEnd_3629741] using wordTrace_append hprefix tailTrace_3629741
  have hstable : (prefixWord ++ tailWord_3629741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629741).length < 2 ^ (prefixWord ++ tailWord_3629741).sum := by decide
  have hdescent : baseEnd_3629741 < baseStart_3629741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629793 : List Nat := [1, 2, 3, 1, 4, 11]
def baseStart_3629793 : Nat := 118140960795 + 3629793 * 2 ^ 59
def prefixEnd_3629793 : Nat := 4983230072969 + 3 ^ 40 * 3629793 * 2
def baseEnd_3629793 : Nat := 15340152142596067093781

theorem tailTrace_3629793 : CollatzResearch.WordTrace tailWord_3629793 prefixEnd_3629793 15340152142596067093781 := by
  unfold tailWord_3629793
  simp only [CollatzResearch.WordTrace]
  refine ⟨132389426938887355135214033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88259617959258236756809355 132389426938887355135214033)
  ·
    refine ⟨99292070204165516351410525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132389426938887355135214033 99292070204165516351410525)
    ·
      refine ⟨37234526326562068631778947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99292070204165516351410525 37234526326562068631778947)
      ·
        refine ⟨55851789489843102947668421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37234526326562068631778947 55851789489843102947668421)
        ·
          refine ⟨10472210529345581802687829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55851789489843102947668421 10472210529345581802687829)
          ·
            refine ⟨15340152142596067093781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10472210529345581802687829 15340152142596067093781)
            ·
              rfl

theorem cell22_3629793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 11].length) (baseStart_3629793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629793 prefixEnd_3629793 := by exact prefixLift 3629793
  have htrace : WordTrace (prefixWord ++ tailWord_3629793) baseStart_3629793 baseEnd_3629793 := by
    simpa [prefixWord, tailWord_3629793, baseEnd_3629793] using wordTrace_append hprefix tailTrace_3629793
  have hstable : (prefixWord ++ tailWord_3629793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629793).length < 2 ^ (prefixWord ++ tailWord_3629793).sum := by decide
  have hdescent : baseEnd_3629793 < baseStart_3629793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629797 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_3629797 : Nat := 118140960795 + 3629797 * 2 ^ 59
def prefixEnd_3629797 : Nat := 4983230072969 + 3 ^ 40 * 3629797 * 2
def baseEnd_3629797 : Nat := 1242553692832026757496249

theorem tailTrace_3629797 : CollatzResearch.WordTrace tailWord_3629797 prefixEnd_3629797 1242553692832026757496249 := by
  unfold tailWord_3629797
  simp only [CollatzResearch.WordTrace]
  refine ⟨132389572830872863818359645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88259715220581909212239763 132389572830872863818359645)
  ·
    refine ⟨49646089811577323931884867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132389572830872863818359645 49646089811577323931884867)
    ·
      refine ⟨74469134717365985897827301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49646089811577323931884867 74469134717365985897827301)
      ·
        refine ⟨13962962759506122355842619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74469134717365985897827301 13962962759506122355842619)
        ·
          refine ⟨20944444139259183533763929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13962962759506122355842619 20944444139259183533763929)
          ·
            refine ⟨15708333104444387650322947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20944444139259183533763929 15708333104444387650322947)
            ·
              refine ⟨23562499656666581475484421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15708333104444387650322947 23562499656666581475484421)
              ·
                refine ⟨4417968685624984026653329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23562499656666581475484421 4417968685624984026653329)
                ·
                  refine ⟨3313476514218738019989997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417968685624984026653329 3313476514218738019989997)
                  ·
                    refine ⟨1242553692832026757496249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313476514218738019989997 1242553692832026757496249)
                    ·
                      rfl

theorem cell22_3629797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_3629797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629797 prefixEnd_3629797 := by exact prefixLift 3629797
  have htrace : WordTrace (prefixWord ++ tailWord_3629797) baseStart_3629797 baseEnd_3629797 := by
    simpa [prefixWord, tailWord_3629797, baseEnd_3629797] using wordTrace_append hprefix tailTrace_3629797
  have hstable : (prefixWord ++ tailWord_3629797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629797).length < 2 ^ (prefixWord ++ tailWord_3629797).sum := by decide
  have hdescent : baseEnd_3629797 < baseStart_3629797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629810 : List Nat := [3, 2, 1, 3, 1, 2, 3, 7]
def baseStart_3629810 : Nat := 118140960795 + 3629810 * 2 ^ 59
def prefixEnd_3629810 : Nat := 4983230072969 + 3 ^ 40 * 3629810 * 2
def baseEnd_3629810 : Nat := 138062015888633228546801

theorem tailTrace_3629810 : CollatzResearch.WordTrace tailWord_3629810 prefixEnd_3629810 138062015888633228546801 := by
  unfold tailWord_3629810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097511744956441759645721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88260031319883844692388589 33097511744956441759645721)
  ·
    refine ⟨24823133808717331319734291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33097511744956441759645721 24823133808717331319734291)
    ·
      refine ⟨37234700713075996979601437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24823133808717331319734291 37234700713075996979601437)
      ·
        refine ⟨13963012767403498867350539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37234700713075996979601437 13963012767403498867350539)
        ·
          refine ⟨20944519151105248301025809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13963012767403498867350539 20944519151105248301025809)
          ·
            refine ⟨15708389363328936225769357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20944519151105248301025809 15708389363328936225769357)
            ·
              refine ⟨5890646011248351084663509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15708389363328936225769357 5890646011248351084663509)
              ·
                refine ⟨138062015888633228546801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5890646011248351084663509 138062015888633228546801)
                ·
                  rfl

theorem cell22_3629810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_3629810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629810 prefixEnd_3629810 := by exact prefixLift 3629810
  have htrace : WordTrace (prefixWord ++ tailWord_3629810) baseStart_3629810 baseEnd_3629810 := by
    simpa [prefixWord, tailWord_3629810, baseEnd_3629810] using wordTrace_append hprefix tailTrace_3629810
  have hstable : (prefixWord ++ tailWord_3629810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629810).length < 2 ^ (prefixWord ++ tailWord_3629810).sum := by decide
  have hdescent : baseEnd_3629810 < baseStart_3629810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629823 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_3629823 : Nat := 118140960795 + 3629823 * 2 ^ 59
def prefixEnd_3629823 : Nat := 4983230072969 + 3 ^ 40 * 3629823 * 2
def baseEnd_3629823 : Nat := 1242562593163371356346169

theorem tailTrace_3629823 : CollatzResearch.WordTrace tailWord_3629823 prefixEnd_3629823 1242562593163371356346169 := by
  unfold tailWord_3629823
  simp only [CollatzResearch.WordTrace]
  refine ⟨132390521128778670258806123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88260347419185780172537415 132390521128778670258806123)
  ·
    refine ⟨198585781693168005388209185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132390521128778670258806123 198585781693168005388209185)
    ·
      refine ⟨148939336269876004041156889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198585781693168005388209185 148939336269876004041156889)
      ·
        refine ⟨111704502202407003030867667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148939336269876004041156889 111704502202407003030867667)
        ·
          refine ⟨167556753303610504546301501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111704502202407003030867667 167556753303610504546301501)
          ·
            refine ⟨62833782488853939204863063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167556753303610504546301501 62833782488853939204863063)
            ·
              refine ⟨94250673733280908807294595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62833782488853939204863063 94250673733280908807294595)
              ·
                refine ⟨141376010599921363210941893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94250673733280908807294595 141376010599921363210941893)
                ·
                  refine ⟨26508001987485255602051605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141376010599921363210941893 26508001987485255602051605)
                  ·
                    refine ⟨1242562593163371356346169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26508001987485255602051605 1242562593163371356346169)
                    ·
                      rfl

theorem cell22_3629823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_3629823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629823 prefixEnd_3629823 := by exact prefixLift 3629823
  have htrace : WordTrace (prefixWord ++ tailWord_3629823) baseStart_3629823 baseEnd_3629823 := by
    simpa [prefixWord, tailWord_3629823, baseEnd_3629823] using wordTrace_append hprefix tailTrace_3629823
  have hstable : (prefixWord ++ tailWord_3629823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629823).length < 2 ^ (prefixWord ++ tailWord_3629823).sum := by decide
  have hdescent : baseEnd_3629823 < baseStart_3629823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
