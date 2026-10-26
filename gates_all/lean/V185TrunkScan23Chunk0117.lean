import V185TrunkScan23Chunk0116

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_691948 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_691948 : Nat := 118140960795 + 691948 * 2 ^ 59
def prefixEnd_691948 : Nat := 4983230072969 + 3 ^ 40 * 691948 * 2
def baseEnd_691948 : Nat := 118433970639121327989265

theorem tailTrace_691948 : CollatzResearch.WordTrace tailWord_691948 prefixEnd_691948 118433970639121327989265 := by
  unfold tailWord_691948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618708448599023077546249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16824944598132030770061665 12618708448599023077546249)
  ·
    refine ⟨9464031336449267308159687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12618708448599023077546249 9464031336449267308159687)
    ·
      refine ⟨14196047004673900962239531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9464031336449267308159687 14196047004673900962239531)
      ·
        refine ⟨21294070507010851443359297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14196047004673900962239531 21294070507010851443359297)
        ·
          refine ⟨15970552880258138582519473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21294070507010851443359297 15970552880258138582519473)
          ·
            refine ⟨11977914660193603936889605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15970552880258138582519473 11977914660193603936889605)
            ·
              refine ⟨2245858998786300738166801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11977914660193603936889605 2245858998786300738166801)
              ·
                refine ⟨1684394249089725553625101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245858998786300738166801 1684394249089725553625101)
                ·
                  refine ⟨631647843408647082609413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1684394249089725553625101 631647843408647082609413)
                  ·
                    refine ⟨118433970639121327989265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631647843408647082609413 118433970639121327989265)
                    ·
                      rfl

theorem cell23_691948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_691948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691948 prefixEnd_691948 := by exact prefixLift 691948
  have htrace : WordTrace (prefixWord ++ tailWord_691948) baseStart_691948 baseEnd_691948 := by
    simpa [prefixWord, tailWord_691948, baseEnd_691948] using wordTrace_append hprefix tailTrace_691948
  have hstable : (prefixWord ++ tailWord_691948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691948).length < 2 ^ (prefixWord ++ tailWord_691948).sum := by decide
  have hdescent : baseEnd_691948 < baseStart_691948 := by decide
  rcases family_descends (prefixWord ++ tailWord_691948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691951 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_691951 : Nat := 118140960795 + 691951 * 2 ^ 59
def prefixEnd_691951 : Nat := 4983230072969 + 3 ^ 40 * 691951 * 2
def baseEnd_691951 : Nat := 355303452359327472230281

theorem tailTrace_691951 : CollatzResearch.WordTrace tailWord_691951 prefixEnd_691951 355303452359327472230281 := by
  unfold tailWord_691951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237526316187177667451707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16825017544124785111634471 25237526316187177667451707)
  ·
    refine ⟨37856289474280766501177561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25237526316187177667451707 37856289474280766501177561)
    ·
      refine ⟨28392217105710574875883171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37856289474280766501177561 28392217105710574875883171)
      ·
        refine ⟨42588325658565862313824757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28392217105710574875883171 42588325658565862313824757)
        ·
          refine ⟨3992655530490549591921071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42588325658565862313824757 3992655530490549591921071)
          ·
            refine ⟨5988983295735824387881607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992655530490549591921071 5988983295735824387881607)
            ·
              refine ⟨8983474943603736581822411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988983295735824387881607 8983474943603736581822411)
              ·
                refine ⟨13475212415405604872733617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8983474943603736581822411 13475212415405604872733617)
                ·
                  refine ⟨10106409311554203654550213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13475212415405604872733617 10106409311554203654550213)
                  ·
                    refine ⟨1894951745916413185228165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10106409311554203654550213 1894951745916413185228165)
                    ·
                      refine ⟨355303452359327472230281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1894951745916413185228165 355303452359327472230281)
                      ·
                        rfl

theorem cell23_691951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_691951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691951 prefixEnd_691951 := by exact prefixLift 691951
  have htrace : WordTrace (prefixWord ++ tailWord_691951) baseStart_691951 baseEnd_691951 := by
    simpa [prefixWord, tailWord_691951, baseEnd_691951] using wordTrace_append hprefix tailTrace_691951
  have hstable : (prefixWord ++ tailWord_691951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691951).length < 2 ^ (prefixWord ++ tailWord_691951).sum := by decide
  have hdescent : baseEnd_691951 < baseStart_691951 := by decide
  rcases family_descends (prefixWord ++ tailWord_691951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691965 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_691965 : Nat := 118140960795 + 691965 * 2 ^ 59
def prefixEnd_691965 : Nat := 4983230072969 + 3 ^ 40 * 691965 * 2
def baseEnd_691965 : Nat := 118436880362830139151739

theorem tailTrace_691965 : CollatzResearch.WordTrace tailWord_691965 prefixEnd_691965 118436880362830139151739 := by
  unfold tailWord_691965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238036938136458058461349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16825357958757638705640899 25238036938136458058461349)
  ·
    refine ⟨4732131925900585885961503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25238036938136458058461349 4732131925900585885961503)
    ·
      refine ⟨7098197888850878828942255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732131925900585885961503 7098197888850878828942255)
      ·
        refine ⟨10647296833276318243413383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098197888850878828942255 10647296833276318243413383)
        ·
          refine ⟨15970945249914477365120075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10647296833276318243413383 15970945249914477365120075)
          ·
            refine ⟨23956417874871716047680113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15970945249914477365120075 23956417874871716047680113)
            ·
              refine ⟨17967313406153787035760085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23956417874871716047680113 17967313406153787035760085)
              ·
                refine ⟨421108907956729383650627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17967313406153787035760085 421108907956729383650627)
                ·
                  refine ⟨631663361935094075475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421108907956729383650627 631663361935094075475941)
                  ·
                    refine ⟨118436880362830139151739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631663361935094075475941 118436880362830139151739)
                    ·
                      rfl

theorem cell23_691965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_691965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691965 prefixEnd_691965 := by exact prefixLift 691965
  have htrace : WordTrace (prefixWord ++ tailWord_691965) baseStart_691965 baseEnd_691965 := by
    simpa [prefixWord, tailWord_691965, baseEnd_691965] using wordTrace_append hprefix tailTrace_691965
  have hstable : (prefixWord ++ tailWord_691965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691965).length < 2 ^ (prefixWord ++ tailWord_691965).sum := by decide
  have hdescent : baseEnd_691965 < baseStart_691965 := by decide
  rcases family_descends (prefixWord ++ tailWord_691965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692039 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_692039 : Nat := 118140960795 + 692039 * 2 ^ 59
def prefixEnd_692039 : Nat := 4983230072969 + 3 ^ 40 * 692039 * 2
def baseEnd_692039 : Nat := 355348638656923127929877

theorem tailTrace_692039 : CollatzResearch.WordTrace tailWord_692039 prefixEnd_692039 355348638656923127929877 := by
  unfold tailWord_692039
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240735939868368696655171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827157293245579131103447 25240735939868368696655171)
  ·
    refine ⟨37861103909802553044982757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25240735939868368696655171 37861103909802553044982757)
    ·
      refine ⟨7098956983087978695934267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37861103909802553044982757 7098956983087978695934267)
      ·
        refine ⟨10648435474631968043901401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098956983087978695934267 10648435474631968043901401)
        ·
          refine ⟨7986326605973976032926051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10648435474631968043901401 7986326605973976032926051)
          ·
            refine ⟨11979489908960964049389077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986326605973976032926051 11979489908960964049389077)
            ·
              refine ⟨561538589482545189815113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11979489908960964049389077 561538589482545189815113)
              ·
                refine ⟨421153942111908892361335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561538589482545189815113 421153942111908892361335)
                ·
                  refine ⟨631730913167863338542003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421153942111908892361335 631730913167863338542003)
                  ·
                    refine ⟨947596369751795007813005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631730913167863338542003 947596369751795007813005)
                    ·
                      refine ⟨355348638656923127929877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 947596369751795007813005 355348638656923127929877)
                      ·
                        rfl

theorem cell23_692039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_692039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692039 prefixEnd_692039 := by exact prefixLift 692039
  have htrace : WordTrace (prefixWord ++ tailWord_692039) baseStart_692039 baseEnd_692039 := by
    simpa [prefixWord, tailWord_692039, baseEnd_692039] using wordTrace_append hprefix tailTrace_692039
  have hstable : (prefixWord ++ tailWord_692039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692039).length < 2 ^ (prefixWord ++ tailWord_692039).sum := by decide
  have hdescent : baseEnd_692039 < baseStart_692039 := by decide
  rcases family_descends (prefixWord ++ tailWord_692039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692055 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 6]
def baseStart_692055 : Nat := 118140960795 + 692055 * 2 ^ 59
def prefixEnd_692055 : Nat := 4983230072969 + 3 ^ 40 * 692055 * 2
def baseEnd_692055 : Nat := 118452284782465021776601

theorem tailTrace_692055 : CollatzResearch.WordTrace tailWord_692055 prefixEnd_692055 118452284782465021776601 := by
  unfold tailWord_692055
  simp only [CollatzResearch.WordTrace]
  refine ⟨25241319507810403429237619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827546338540268952825079 25241319507810403429237619)
  ·
    refine ⟨37861979261715605143856429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25241319507810403429237619 37861979261715605143856429)
    ·
      refine ⟨14198242223143351928946161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37861979261715605143856429 14198242223143351928946161)
      ·
        refine ⟨10648681667357513946709621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14198242223143351928946161 10648681667357513946709621)
        ·
          refine ⟨998313906314766932504027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10648681667357513946709621 998313906314766932504027)
          ·
            refine ⟨1497470859472150398756041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998313906314766932504027 1497470859472150398756041)
            ·
              refine ⟨1123103144604112799067031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497470859472150398756041 1123103144604112799067031)
              ·
                refine ⟨1684654716906169198600547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123103144604112799067031 1684654716906169198600547)
                ·
                  refine ⟨2526982075359253797900821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684654716906169198600547 2526982075359253797900821)
                  ·
                    refine ⟨118452284782465021776601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2526982075359253797900821 118452284782465021776601)
                    ·
                      rfl

theorem cell23_692055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_692055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692055 prefixEnd_692055 := by exact prefixLift 692055
  have htrace : WordTrace (prefixWord ++ tailWord_692055) baseStart_692055 baseEnd_692055 := by
    simpa [prefixWord, tailWord_692055, baseEnd_692055] using wordTrace_append hprefix tailTrace_692055
  have hstable : (prefixWord ++ tailWord_692055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692055).length < 2 ^ (prefixWord ++ tailWord_692055).sum := by decide
  have hdescent : baseEnd_692055 < baseStart_692055 := by decide
  rcases family_descends (prefixWord ++ tailWord_692055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692065 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_692065 : Nat := 118140960795 + 692065 * 2 ^ 59
def prefixEnd_692065 : Nat := 4983230072969 + 3 ^ 40 * 692065 * 2
def baseEnd_692065 : Nat := 355361989153940026204757

theorem tailTrace_692065 : CollatzResearch.WordTrace tailWord_692065 prefixEnd_692065 355361989153940026204757 := by
  unfold tailWord_692065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25241684237774175137101649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827789491849450091401099 25241684237774175137101649)
  ·
    refine ⟨18931263178330631352826237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25241684237774175137101649 18931263178330631352826237)
    ·
      refine ⟨7099223691873986757309839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18931263178330631352826237 7099223691873986757309839)
      ·
        refine ⟨10648835537810980135964759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7099223691873986757309839 10648835537810980135964759)
        ·
          refine ⟨15973253306716470203947139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10648835537810980135964759 15973253306716470203947139)
          ·
            refine ⟨23959879960074705305920709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15973253306716470203947139 23959879960074705305920709)
            ·
              refine ⟨4492477492514007244860133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23959879960074705305920709 4492477492514007244860133)
              ·
                refine ⟨842339529846376358411275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4492477492514007244860133 842339529846376358411275)
                ·
                  refine ⟨1263509294769564537616913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842339529846376358411275 1263509294769564537616913)
                  ·
                    refine ⟨947631971077173403212685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1263509294769564537616913 947631971077173403212685)
                    ·
                      refine ⟨355361989153940026204757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 947631971077173403212685 355361989153940026204757)
                      ·
                        rfl

theorem cell23_692065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_692065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692065 prefixEnd_692065 := by exact prefixLift 692065
  have htrace : WordTrace (prefixWord ++ tailWord_692065) baseStart_692065 baseEnd_692065 := by
    simpa [prefixWord, tailWord_692065, baseEnd_692065] using wordTrace_append hprefix tailTrace_692065
  have hstable : (prefixWord ++ tailWord_692065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692065).length < 2 ^ (prefixWord ++ tailWord_692065).sum := by decide
  have hdescent : baseEnd_692065 < baseStart_692065 := by decide
  rcases family_descends (prefixWord ++ tailWord_692065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692130 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_692130 : Nat := 118140960795 + 692130 * 2 ^ 59
def prefixEnd_692130 : Nat := 4983230072969 + 3 ^ 40 * 692130 * 2
def baseEnd_692130 : Nat := 355395365396482271891959

theorem tailTrace_692130 : CollatzResearch.WordTrace tailWord_692130 prefixEnd_692130 355395365396482271891959 := by
  unfold tailWord_692130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311013745634672809554461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16829369988359127492145229 6311013745634672809554461)
  ·
    refine ⟨2366630154613002303582923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6311013745634672809554461 2366630154613002303582923)
    ·
      refine ⟨3549945231919503455374385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366630154613002303582923 3549945231919503455374385)
      ·
        refine ⟨2662458923939627591530789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3549945231919503455374385 2662458923939627591530789)
        ·
          refine ⟨499211048238680173412023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2662458923939627591530789 499211048238680173412023)
          ·
            refine ⟨748816572358020260118035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499211048238680173412023 748816572358020260118035)
            ·
              refine ⟨1123224858537030390177053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748816572358020260118035 1123224858537030390177053)
              ·
                refine ⟨421209321951386396316395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1123224858537030390177053 421209321951386396316395)
                ·
                  refine ⟨631813982927079594474593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421209321951386396316395 631813982927079594474593)
                  ·
                    refine ⟨473860487195309695855945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 631813982927079594474593 473860487195309695855945)
                    ·
                      refine ⟨355395365396482271891959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473860487195309695855945 355395365396482271891959)
                      ·
                        rfl

theorem cell23_692130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_692130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692130 prefixEnd_692130 := by exact prefixLift 692130
  have htrace : WordTrace (prefixWord ++ tailWord_692130) baseStart_692130 baseEnd_692130 := by
    simpa [prefixWord, tailWord_692130, baseEnd_692130] using wordTrace_append hprefix tailTrace_692130
  have hstable : (prefixWord ++ tailWord_692130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692130).length < 2 ^ (prefixWord ++ tailWord_692130).sum := by decide
  have hdescent : baseEnd_692130 < baseStart_692130 := by decide
  rcases family_descends (prefixWord ++ tailWord_692130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692152 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_692152 : Nat := 118140960795 + 692152 * 2 ^ 59
def prefixEnd_692152 : Nat := 4983230072969 + 3 ^ 40 * 692152 * 2
def baseEnd_692152 : Nat := 355406661970881185816857

theorem tailTrace_692152 : CollatzResearch.WordTrace tailWord_692152 prefixEnd_692152 355406661970881185816857 := by
  unfold tailWord_692152
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622428694229494497759355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16829904925639325997012473 12622428694229494497759355)
  ·
    refine ⟨18933643041344241746639033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622428694229494497759355 18933643041344241746639033)
    ·
      refine ⟨14200232281008181309979275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18933643041344241746639033 14200232281008181309979275)
      ·
        refine ⟨21300348421512271964968913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14200232281008181309979275 21300348421512271964968913)
        ·
          refine ⟨15975261316134203973726685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21300348421512271964968913 15975261316134203973726685)
          ·
            refine ⟨5990722993550326490147507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15975261316134203973726685 5990722993550326490147507)
            ·
              refine ⟨8986084490325489735221261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990722993550326490147507 8986084490325489735221261)
              ·
                refine ⟨3369781683872058650707973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8986084490325489735221261 3369781683872058650707973)
                ·
                  refine ⟨631834065726010997007745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3369781683872058650707973 631834065726010997007745)
                  ·
                    refine ⟨473875549294508247755809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 631834065726010997007745 473875549294508247755809)
                    ·
                      refine ⟨355406661970881185816857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473875549294508247755809 355406661970881185816857)
                      ·
                        rfl

theorem cell23_692152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_692152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692152 prefixEnd_692152 := by exact prefixLift 692152
  have htrace : WordTrace (prefixWord ++ tailWord_692152) baseStart_692152 baseEnd_692152 := by
    simpa [prefixWord, tailWord_692152, baseEnd_692152] using wordTrace_append hprefix tailTrace_692152
  have hstable : (prefixWord ++ tailWord_692152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692152).length < 2 ^ (prefixWord ++ tailWord_692152).sum := by decide
  have hdescent : baseEnd_692152 < baseStart_692152 := by decide
  rcases family_descends (prefixWord ++ tailWord_692152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692218 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_692218 : Nat := 118140960795 + 692218 * 2 ^ 59
def prefixEnd_692218 : Nat := 4983230072969 + 3 ^ 40 * 692218 * 2
def baseEnd_692218 : Nat := 118480183898025975863851

theorem tailTrace_692218 : CollatzResearch.WordTrace tailWord_692218 prefixEnd_692218 118480183898025975863851 := by
  unfold tailWord_692218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311816151554970566855327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16831509737479921511614205 6311816151554970566855327)
  ·
    refine ⟨9467724227332455850282991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6311816151554970566855327 9467724227332455850282991)
    ·
      refine ⟨14201586340998683775424487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9467724227332455850282991 14201586340998683775424487)
      ·
        refine ⟨21302379511498025663136731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14201586340998683775424487 21302379511498025663136731)
        ·
          refine ⟨31953569267247038494705097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21302379511498025663136731 31953569267247038494705097)
          ·
            refine ⟨23965176950435278871028823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31953569267247038494705097 23965176950435278871028823)
            ·
              refine ⟨35947765425652918306543235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23965176950435278871028823 35947765425652918306543235)
              ·
                refine ⟨53921648138479377459814853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35947765425652918306543235 53921648138479377459814853)
                ·
                  refine ⟨10110309025964883273715285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53921648138479377459814853 10110309025964883273715285)
                  ·
                    refine ⟨118480183898025975863851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10110309025964883273715285 118480183898025975863851)
                    ·
                      rfl

theorem cell23_692218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_692218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692218 prefixEnd_692218 := by exact prefixLift 692218
  have htrace : WordTrace (prefixWord ++ tailWord_692218) baseStart_692218 baseEnd_692218 := by
    simpa [prefixWord, tailWord_692218, baseEnd_692218] using wordTrace_append hprefix tailTrace_692218
  have hstable : (prefixWord ++ tailWord_692218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692218).length < 2 ^ (prefixWord ++ tailWord_692218).sum := by decide
  have hdescent : baseEnd_692218 < baseStart_692218 := by decide
  rcases family_descends (prefixWord ++ tailWord_692218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692225 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_692225 : Nat := 118140960795 + 692225 * 2 ^ 59
def prefixEnd_692225 : Nat := 4983230072969 + 3 ^ 40 * 692225 * 2
def baseEnd_692225 : Nat := 355444146058659400204021

theorem tailTrace_692225 : CollatzResearch.WordTrace tailWord_692225 prefixEnd_692225 355444146058659400204021 := by
  unfold tailWord_692225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25247519917194522462926129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16831679944796348308617419 25247519917194522462926129)
  ·
    refine ⟨18935639937895891847194597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25247519917194522462926129 18935639937895891847194597)
    ·
      refine ⟨3550432488355479721348987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18935639937895891847194597 3550432488355479721348987)
      ·
        refine ⟨5325648732533219582023481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550432488355479721348987 5325648732533219582023481)
        ·
          refine ⟨3994236549399914686517611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325648732533219582023481 3994236549399914686517611)
          ·
            refine ⟨5991354824099872029776417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994236549399914686517611 5991354824099872029776417)
            ·
              refine ⟨4493516118074904022332313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991354824099872029776417 4493516118074904022332313)
              ·
                refine ⟨3370137088556178016749235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493516118074904022332313 3370137088556178016749235)
                ·
                  refine ⟨5055205632834267025123853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370137088556178016749235 5055205632834267025123853)
                  ·
                    refine ⟨1895702112312850134421445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5055205632834267025123853 1895702112312850134421445)
                    ·
                      refine ⟨355444146058659400204021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1895702112312850134421445 355444146058659400204021)
                      ·
                        rfl

theorem cell23_692225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_692225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692225 prefixEnd_692225 := by exact prefixLift 692225
  have htrace : WordTrace (prefixWord ++ tailWord_692225) baseStart_692225 baseEnd_692225 := by
    simpa [prefixWord, tailWord_692225, baseEnd_692225] using wordTrace_append hprefix tailTrace_692225
  have hstable : (prefixWord ++ tailWord_692225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692225).length < 2 ^ (prefixWord ++ tailWord_692225).sum := by decide
  have hdescent : baseEnd_692225 < baseStart_692225 := by decide
  rcases family_descends (prefixWord ++ tailWord_692225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692285 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_692285 : Nat := 118140960795 + 692285 * 2 ^ 59
def prefixEnd_692285 : Nat := 4983230072969 + 3 ^ 40 * 692285 * 2
def baseEnd_692285 : Nat := 355474954897929165453745

theorem tailTrace_692285 : CollatzResearch.WordTrace tailWord_692285 prefixEnd_692285 355474954897929165453745 := by
  unfold tailWord_692285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249708296977152710110309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16833138864651435140073539 25249708296977152710110309)
  ·
    refine ⟨4734320305683216133145683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25249708296977152710110309 4734320305683216133145683)
    ·
      refine ⟨7101480458524824199718525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4734320305683216133145683 7101480458524824199718525)
      ·
        refine ⟨2663055171946809074894447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7101480458524824199718525 2663055171946809074894447)
        ·
          refine ⟨3994582757920213612341671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663055171946809074894447 3994582757920213612341671)
          ·
            refine ⟨5991874136880320418512507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994582757920213612341671 5991874136880320418512507)
            ·
              refine ⟨8987811205320480627768761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991874136880320418512507 8987811205320480627768761)
              ·
                refine ⟨6740858403990360470826571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8987811205320480627768761 6740858403990360470826571)
                ·
                  refine ⟨10111287605985540706239857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740858403990360470826571 10111287605985540706239857)
                  ·
                    refine ⟨7583465704489155529679893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10111287605985540706239857 7583465704489155529679893)
                    ·
                      refine ⟨355474954897929165453745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7583465704489155529679893 355474954897929165453745)
                      ·
                        rfl

theorem cell23_692285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_692285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692285 prefixEnd_692285 := by exact prefixLift 692285
  have htrace : WordTrace (prefixWord ++ tailWord_692285) baseStart_692285 baseEnd_692285 := by
    simpa [prefixWord, tailWord_692285, baseEnd_692285] using wordTrace_append hprefix tailTrace_692285
  have hstable : (prefixWord ++ tailWord_692285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692285).length < 2 ^ (prefixWord ++ tailWord_692285).sum := by decide
  have hdescent : baseEnd_692285 < baseStart_692285 := by decide
  rcases family_descends (prefixWord ++ tailWord_692285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692312 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_692312 : Nat := 118140960795 + 692312 * 2 ^ 59
def prefixEnd_692312 : Nat := 4983230072969 + 3 ^ 40 * 692312 * 2
def baseEnd_692312 : Nat := 118496272958533519938707

theorem tailTrace_692312 : CollatzResearch.WordTrace tailWord_692312 prefixEnd_692312 118496272958533519938707 := by
  unfold tailWord_692312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625346533939668160671595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16833795378586224214228793 12625346533939668160671595)
  ·
    refine ⟨18938019800909502241007393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625346533939668160671595 18938019800909502241007393)
    ·
      refine ⟨14203514850682126680755545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18938019800909502241007393 14203514850682126680755545)
      ·
        refine ⟨10652636138011595010566659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14203514850682126680755545 10652636138011595010566659)
        ·
          refine ⟨15978954207017392515849989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10652636138011595010566659 15978954207017392515849989)
          ·
            refine ⟨2996053913815761096721873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15978954207017392515849989 2996053913815761096721873)
            ·
              refine ⟨2247040435361820822541405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996053913815761096721873 2247040435361820822541405)
              ·
                refine ⟨842640163260682808453027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2247040435361820822541405 842640163260682808453027)
                ·
                  refine ⟨1263960244891024212679541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842640163260682808453027 1263960244891024212679541)
                  ·
                    refine ⟨118496272958533519938707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1263960244891024212679541 118496272958533519938707)
                    ·
                      rfl

theorem cell23_692312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_692312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692312 prefixEnd_692312 := by exact prefixLift 692312
  have htrace : WordTrace (prefixWord ++ tailWord_692312) baseStart_692312 baseEnd_692312 := by
    simpa [prefixWord, tailWord_692312, baseEnd_692312] using wordTrace_append hprefix tailTrace_692312
  have hstable : (prefixWord ++ tailWord_692312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692312).length < 2 ^ (prefixWord ++ tailWord_692312).sum := by decide
  have hdescent : baseEnd_692312 < baseStart_692312 := by decide
  rcases family_descends (prefixWord ++ tailWord_692312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692349 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_692349 : Nat := 118140960795 + 692349 * 2 ^ 59
def prefixEnd_692349 : Nat := 4983230072969 + 3 ^ 40 * 692349 * 2
def baseEnd_692349 : Nat := 355507817659816915053451

theorem tailTrace_692349 : CollatzResearch.WordTrace tailWord_692349 prefixEnd_692349 355507817659816915053451 := by
  unfold tailWord_692349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252042568745291640440101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16834695045830194426960067 25252042568745291640440101)
  ·
    refine ⟨4734757981639742182582519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25252042568745291640440101 4734757981639742182582519)
    ·
      refine ⟨7102136972459613273873779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4734757981639742182582519 7102136972459613273873779)
      ·
        refine ⟨10653205458689419910810669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102136972459613273873779 10653205458689419910810669)
        ·
          refine ⟨3994952047008532466554001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10653205458689419910810669 3994952047008532466554001)
          ·
            refine ⟨2996214035256399349915501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994952047008532466554001 2996214035256399349915501)
            ·
              refine ⟨1123580263221149756218313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2996214035256399349915501 1123580263221149756218313)
              ·
                refine ⟨842685197415862317163735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123580263221149756218313 842685197415862317163735)
                ·
                  refine ⟨1264027796123793475745603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842685197415862317163735 1264027796123793475745603)
                  ·
                    refine ⟨1896041694185690213618405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1264027796123793475745603 1896041694185690213618405)
                    ·
                      refine ⟨355507817659816915053451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1896041694185690213618405 355507817659816915053451)
                      ·
                        rfl

theorem cell23_692349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_692349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692349 prefixEnd_692349 := by exact prefixLift 692349
  have htrace : WordTrace (prefixWord ++ tailWord_692349) baseStart_692349 baseEnd_692349 := by
    simpa [prefixWord, tailWord_692349, baseEnd_692349] using wordTrace_append hprefix tailTrace_692349
  have hstable : (prefixWord ++ tailWord_692349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692349).length < 2 ^ (prefixWord ++ tailWord_692349).sum := by decide
  have hdescent : baseEnd_692349 < baseStart_692349 := by decide
  rcases family_descends (prefixWord ++ tailWord_692349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692355 : List Nat := [1, 1, 1, 3, 3, 3, 2, 9]
def baseStart_692355 : Nat := 118140960795 + 692355 * 2 ^ 59
def prefixEnd_692355 : Nat := 4983230072969 + 3 ^ 40 * 692355 * 2
def baseEnd_692355 : Nat := 13167070316434958947349

theorem tailTrace_692355 : CollatzResearch.WordTrace tailWord_692355 prefixEnd_692355 13167070316434958947349 := by
  unfold tailWord_692355
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252261406723554665158519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16834840937815703110105679 25252261406723554665158519)
  ·
    refine ⟨37878392110085331997737779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25252261406723554665158519 37878392110085331997737779)
    ·
      refine ⟨56817588165127997996606669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37878392110085331997737779 56817588165127997996606669)
      ·
        refine ⟨21306595561922999248727501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56817588165127997996606669 21306595561922999248727501)
        ·
          refine ⟨7989973335721124718272813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21306595561922999248727501 7989973335721124718272813)
          ·
            refine ⟨2996240000895421769352305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7989973335721124718272813 2996240000895421769352305)
            ·
              refine ⟨2247180000671566327014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996240000895421769352305 2247180000671566327014229)
              ·
                refine ⟨13167070316434958947349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2247180000671566327014229 13167070316434958947349)
                ·
                  rfl

theorem cell23_692355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 9].length) (baseStart_692355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692355 prefixEnd_692355 := by exact prefixLift 692355
  have htrace : WordTrace (prefixWord ++ tailWord_692355) baseStart_692355 baseEnd_692355 := by
    simpa [prefixWord, tailWord_692355, baseEnd_692355] using wordTrace_append hprefix tailTrace_692355
  have hstable : (prefixWord ++ tailWord_692355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692355).length < 2 ^ (prefixWord ++ tailWord_692355).sum := by decide
  have hdescent : baseEnd_692355 < baseStart_692355 := by decide
  rcases family_descends (prefixWord ++ tailWord_692355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692362 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_692362 : Nat := 118140960795 + 692362 * 2 ^ 59
def prefixEnd_692362 : Nat := 4983230072969 + 3 ^ 40 * 692362 * 2
def baseEnd_692362 : Nat := 355514492908325364190891

theorem tailTrace_692362 : CollatzResearch.WordTrace tailWord_692362 prefixEnd_692362 355514492908325364190891 := by
  unfold tailWord_692362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313129179424548715165835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16835011145132129907108893 6313129179424548715165835)
  ·
    refine ⟨9469693769136823072748753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313129179424548715165835 9469693769136823072748753)
    ·
      refine ⟨7102270326852617304561565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9469693769136823072748753 7102270326852617304561565)
      ·
        refine ⟨2663351372569731489210587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7102270326852617304561565 2663351372569731489210587)
        ·
          refine ⟨3995027058854597233815881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663351372569731489210587 3995027058854597233815881)
          ·
            refine ⟨2996270294140947925361911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995027058854597233815881 2996270294140947925361911)
            ·
              refine ⟨4494405441211421888042867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996270294140947925361911 4494405441211421888042867)
              ·
                refine ⟨6741608161817132832064301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494405441211421888042867 6741608161817132832064301)
                ·
                  refine ⟨2528103060681424812024113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6741608161817132832064301 2528103060681424812024113)
                  ·
                    refine ⟨1896077295511068609018085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528103060681424812024113 1896077295511068609018085)
                    ·
                      refine ⟨355514492908325364190891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1896077295511068609018085 355514492908325364190891)
                      ·
                        rfl

theorem cell23_692362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_692362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692362 prefixEnd_692362 := by exact prefixLift 692362
  have htrace : WordTrace (prefixWord ++ tailWord_692362) baseStart_692362 baseEnd_692362 := by
    simpa [prefixWord, tailWord_692362, baseEnd_692362] using wordTrace_append hprefix tailTrace_692362
  have hstable : (prefixWord ++ tailWord_692362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692362).length < 2 ^ (prefixWord ++ tailWord_692362).sum := by decide
  have hdescent : baseEnd_692362 < baseStart_692362 := by decide
  rcases family_descends (prefixWord ++ tailWord_692362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692372 : List Nat := [2, 4, 2, 3, 12]
def baseStart_692372 : Nat := 118140960795 + 692372 * 2 ^ 59
def prefixEnd_692372 : Nat := 4983230072969 + 3 ^ 40 * 692372 * 2
def baseEnd_692372 : Nat := 487681245150713751805

theorem tailTrace_692372 : CollatzResearch.WordTrace tailWord_692372 prefixEnd_692372 487681245150713751805 := by
  unfold tailWord_692372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626440723830983284263685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16835254298441311045684913 12626440723830983284263685)
  ·
    refine ⟨2367457635718309365799441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12626440723830983284263685 2367457635718309365799441)
    ·
      refine ⟨1775593226788732024349581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2367457635718309365799441 1775593226788732024349581)
      ·
        refine ⟨665847460045774509131093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1775593226788732024349581 665847460045774509131093)
        ·
          refine ⟨487681245150713751805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 665847460045774509131093 487681245150713751805)
          ·
            rfl

theorem cell23_692372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 12].length) (baseStart_692372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692372 prefixEnd_692372 := by exact prefixLift 692372
  have htrace : WordTrace (prefixWord ++ tailWord_692372) baseStart_692372 baseEnd_692372 := by
    simpa [prefixWord, tailWord_692372, baseEnd_692372] using wordTrace_append hprefix tailTrace_692372
  have hstable : (prefixWord ++ tailWord_692372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692372).length < 2 ^ (prefixWord ++ tailWord_692372).sum := by decide
  have hdescent : baseEnd_692372 < baseStart_692372 := by decide
  rcases family_descends (prefixWord ++ tailWord_692372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692376 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_692376 : Nat := 118140960795 + 692376 * 2 ^ 59
def prefixEnd_692376 : Nat := 4983230072969 + 3 ^ 40 * 692376 * 2
def baseEnd_692376 : Nat := 118507227212496103138609

theorem tailTrace_692376 : CollatzResearch.WordTrace tailWord_692376 prefixEnd_692376 118507227212496103138609 := by
  unfold tailWord_692376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626513669823737625836491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16835351559764983501115321 12626513669823737625836491)
  ·
    refine ⟨18939770504735606438754737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12626513669823737625836491 18939770504735606438754737)
    ·
      refine ⟨14204827878551704829066053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18939770504735606438754737 14204827878551704829066053)
      ·
        refine ⟨2663405227228444655449885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14204827878551704829066053 2663405227228444655449885)
        ·
          refine ⟨998776960210666745793707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2663405227228444655449885 998776960210666745793707)
          ·
            refine ⟨1498165440316000118690561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998776960210666745793707 1498165440316000118690561)
            ·
              refine ⟨1123624080237000089017921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498165440316000118690561 1123624080237000089017921)
              ·
                refine ⟨842718060177750066763441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123624080237000089017921 842718060177750066763441)
                ·
                  refine ⟨632038545133312550072581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842718060177750066763441 632038545133312550072581)
                  ·
                    refine ⟨118507227212496103138609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632038545133312550072581 118507227212496103138609)
                    ·
                      rfl

theorem cell23_692376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_692376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692376 prefixEnd_692376 := by exact prefixLift 692376
  have htrace : WordTrace (prefixWord ++ tailWord_692376) baseStart_692376 baseEnd_692376 := by
    simpa [prefixWord, tailWord_692376, baseEnd_692376] using wordTrace_append hprefix tailTrace_692376
  have hstable : (prefixWord ++ tailWord_692376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692376).length < 2 ^ (prefixWord ++ tailWord_692376).sum := by decide
  have hdescent : baseEnd_692376 < baseStart_692376 := by decide
  rcases family_descends (prefixWord ++ tailWord_692376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692404 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_692404 : Nat := 118140960795 + 692404 * 2 ^ 59
def prefixEnd_692404 : Nat := 4983230072969 + 3 ^ 40 * 692404 * 2
def baseEnd_692404 : Nat := 355536059095814199865699

theorem tailTrace_692404 : CollatzResearch.WordTrace tailWord_692404 prefixEnd_692404 355536059095814199865699 := by
  unfold tailWord_692404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627024291773018016846133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16836032389030690689128177 12627024291773018016846133)
  ·
    refine ⟨1183783527353720439079325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12627024291773018016846133 1183783527353720439079325)
    ·
      refine ⟨443918822757645164654747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1183783527353720439079325 443918822757645164654747)
      ·
        refine ⟨665878234136467746982121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443918822757645164654747 665878234136467746982121)
        ·
          refine ⟨499408675602350810236591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665878234136467746982121 499408675602350810236591)
          ·
            refine ⟨749113013403526215354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499408675602350810236591 749113013403526215354887)
            ·
              refine ⟨1123669520105289323032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749113013403526215354887 1123669520105289323032331)
              ·
                refine ⟨1685504280157933984548497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123669520105289323032331 1685504280157933984548497)
                ·
                  refine ⟨1264128210118450488411373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685504280157933984548497 1264128210118450488411373)
                  ·
                    refine ⟨474048078794418933154265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264128210118450488411373 474048078794418933154265)
                    ·
                      refine ⟨355536059095814199865699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474048078794418933154265 355536059095814199865699)
                      ·
                        rfl

theorem cell23_692404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_692404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692404 prefixEnd_692404 := by exact prefixLift 692404
  have htrace : WordTrace (prefixWord ++ tailWord_692404) baseStart_692404 baseEnd_692404 := by
    simpa [prefixWord, tailWord_692404, baseEnd_692404] using wordTrace_append hprefix tailTrace_692404
  have hstable : (prefixWord ++ tailWord_692404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692404).length < 2 ^ (prefixWord ++ tailWord_692404).sum := by decide
  have hdescent : baseEnd_692404 < baseStart_692404 := by decide
  rcases family_descends (prefixWord ++ tailWord_692404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692409 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 3, 3, 2]
def baseStart_692409 : Nat := 118140960795 + 692409 * 2 ^ 59
def prefixEnd_692409 : Nat := 4983230072969 + 3 ^ 40 * 692409 * 2
def baseEnd_692409 : Nat := 355538626499086680303175

theorem tailTrace_692409 : CollatzResearch.WordTrace tailWord_692409 prefixEnd_692409 355538626499086680303175 := by
  unfold tailWord_692409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254230948527921887624281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16836153965685281258416187 25254230948527921887624281)
  ·
    refine ⟨18940673211395941415718211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25254230948527921887624281 18940673211395941415718211)
    ·
      refine ⟨28411009817093912123577317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18940673211395941415718211 28411009817093912123577317)
      ·
        refine ⟨5327064340705108523170747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28411009817093912123577317 5327064340705108523170747)
        ·
          refine ⟨7990596511057662784756121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327064340705108523170747 7990596511057662784756121)
          ·
            refine ⟨5992947383293247088567091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7990596511057662784756121 5992947383293247088567091)
            ·
              refine ⟨8989421074939870632850637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992947383293247088567091 8989421074939870632850637)
              ·
                refine ⟨3371032903102451487318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8989421074939870632850637 3371032903102451487318989)
                ·
                  refine ⟨1264137338663419307744621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3371032903102451487318989 1264137338663419307744621)
                  ·
                    refine ⟨474051501998782240404233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264137338663419307744621 474051501998782240404233)
                    ·
                      refine ⟨355538626499086680303175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474051501998782240404233 355538626499086680303175)
                      ·
                        rfl

theorem cell23_692409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_692409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692409 prefixEnd_692409 := by exact prefixLift 692409
  have htrace : WordTrace (prefixWord ++ tailWord_692409) baseStart_692409 baseEnd_692409 := by
    simpa [prefixWord, tailWord_692409, baseEnd_692409] using wordTrace_append hprefix tailTrace_692409
  have hstable : (prefixWord ++ tailWord_692409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692409).length < 2 ^ (prefixWord ++ tailWord_692409).sum := by decide
  have hdescent : baseEnd_692409 < baseStart_692409 := by decide
  rcases family_descends (prefixWord ++ tailWord_692409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692415 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 8]
def baseStart_692415 : Nat := 118140960795 + 692415 * 2 ^ 59
def prefixEnd_692415 : Nat := 4983230072969 + 3 ^ 40 * 692415 * 2
def baseEnd_692415 : Nat := 118513902461004552276049

theorem tailTrace_692415 : CollatzResearch.WordTrace tailWord_692415 prefixEnd_692415 118513902461004552276049 := by
  unfold tailWord_692415
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254449786506184912342699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16836299857670789941561799 25254449786506184912342699)
  ·
    refine ⟨37881674679759277368514049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25254449786506184912342699 37881674679759277368514049)
    ·
      refine ⟨28411256009819458026385537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37881674679759277368514049 28411256009819458026385537)
      ·
        refine ⟨21308442007364593519789153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28411256009819458026385537 21308442007364593519789153)
        ·
          refine ⟨15981331505523445139841865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21308442007364593519789153 15981331505523445139841865)
          ·
            refine ⟨11985998629142583854881399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15981331505523445139841865 11985998629142583854881399)
            ·
              refine ⟨17978997943713875782322099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11985998629142583854881399 17978997943713875782322099)
              ·
                refine ⟨26968496915570813673483149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17978997943713875782322099 26968496915570813673483149)
                ·
                  refine ⟨10113186343339055127556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26968496915570813673483149 10113186343339055127556181)
                  ·
                    refine ⟨118513902461004552276049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10113186343339055127556181 118513902461004552276049)
                    ·
                      rfl

theorem cell23_692415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_692415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692415 prefixEnd_692415 := by exact prefixLift 692415
  have htrace : WordTrace (prefixWord ++ tailWord_692415) baseStart_692415 baseEnd_692415 := by
    simpa [prefixWord, tailWord_692415, baseEnd_692415] using wordTrace_append hprefix tailTrace_692415
  have hstable : (prefixWord ++ tailWord_692415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692415).length < 2 ^ (prefixWord ++ tailWord_692415).sum := by decide
  have hdescent : baseEnd_692415 < baseStart_692415 := by decide
  rcases family_descends (prefixWord ++ tailWord_692415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692417 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_692417 : Nat := 118140960795 + 692417 * 2 ^ 59
def prefixEnd_692417 : Nat := 4983230072969 + 3 ^ 40 * 692417 * 2
def baseEnd_692417 : Nat := 355542734344322649003139

theorem tailTrace_692417 : CollatzResearch.WordTrace tailWord_692417 prefixEnd_692417 355542734344322649003139 := by
  unfold tailWord_692417
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254522732498939253915505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16836348488332626169277003 25254522732498939253915505)
  ·
    refine ⟨18940892049374204440436629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25254522732498939253915505 18940892049374204440436629)
    ·
      refine ⟨887854314814415833145467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18940892049374204440436629 887854314814415833145467)
      ·
        refine ⟨1331781472221623749718201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887854314814415833145467 1331781472221623749718201)
        ·
          refine ⟨998836104166217812288651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331781472221623749718201 998836104166217812288651)
          ·
            refine ⟨1498254156249326718432977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998836104166217812288651 1498254156249326718432977)
            ·
              refine ⟨1123690617186995038824733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498254156249326718432977 1123690617186995038824733)
              ·
                refine ⟨421383981445123139559275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1123690617186995038824733 421383981445123139559275)
                ·
                  refine ⟨632075972167684709338913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421383981445123139559275 632075972167684709338913)
                  ·
                    refine ⟨474056979125763532004185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632075972167684709338913 474056979125763532004185)
                    ·
                      refine ⟨355542734344322649003139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474056979125763532004185 355542734344322649003139)
                      ·
                        rfl

theorem cell23_692417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_692417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692417 prefixEnd_692417 := by exact prefixLift 692417
  have htrace : WordTrace (prefixWord ++ tailWord_692417) baseStart_692417 baseEnd_692417 := by
    simpa [prefixWord, tailWord_692417, baseEnd_692417] using wordTrace_append hprefix tailTrace_692417
  have hstable : (prefixWord ++ tailWord_692417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692417).length < 2 ^ (prefixWord ++ tailWord_692417).sum := by decide
  have hdescent : baseEnd_692417 < baseStart_692417 := by decide
  rcases family_descends (prefixWord ++ tailWord_692417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692426 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_692426 : Nat := 118140960795 + 692426 * 2 ^ 59
def prefixEnd_692426 : Nat := 4983230072969 + 3 ^ 40 * 692426 * 2
def baseEnd_692426 : Nat := 355547355670213113790597

theorem tailTrace_692426 : CollatzResearch.WordTrace tailWord_692426 prefixEnd_692426 355547355670213113790597 := by
  unfold tailWord_692426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313712747366583447748283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16836567326310889193995421 6313712747366583447748283)
  ·
    refine ⟨9470569121049875171622425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313712747366583447748283 9470569121049875171622425)
    ·
      refine ⟨7102926840787406378716819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9470569121049875171622425 7102926840787406378716819)
      ·
        refine ⟨10654390261181109568075229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102926840787406378716819 10654390261181109568075229)
        ·
          refine ⟨3995396347942916088028211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10654390261181109568075229 3995396347942916088028211)
          ·
            refine ⟨5993094521914374132042317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995396347942916088028211 5993094521914374132042317)
            ·
              refine ⟨2247410445717890299515869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5993094521914374132042317 2247410445717890299515869)
              ·
                refine ⟨842778917144208862318451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2247410445717890299515869 842778917144208862318451)
                ·
                  refine ⟨1264168375716313293477677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842778917144208862318451 1264168375716313293477677)
                  ·
                    refine ⟨474063140893617485054129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264168375716313293477677 474063140893617485054129)
                    ·
                      refine ⟨355547355670213113790597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474063140893617485054129 355547355670213113790597)
                      ·
                        rfl

theorem cell23_692426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_692426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692426 prefixEnd_692426 := by exact prefixLift 692426
  have htrace : WordTrace (prefixWord ++ tailWord_692426) baseStart_692426 baseEnd_692426 := by
    simpa [prefixWord, tailWord_692426, baseEnd_692426] using wordTrace_append hprefix tailTrace_692426
  have hstable : (prefixWord ++ tailWord_692426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692426).length < 2 ^ (prefixWord ++ tailWord_692426).sum := by decide
  have hdescent : baseEnd_692426 < baseStart_692426 := by decide
  rcases family_descends (prefixWord ++ tailWord_692426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_692435 : Nat := 118140960795 + 692435 * 2 ^ 59
def prefixEnd_692435 : Nat := 4983230072969 + 3 ^ 40 * 692435 * 2
def baseEnd_692435 : Nat := 355551976996103578578055

theorem tailTrace_692435 : CollatzResearch.WordTrace tailWord_692435 prefixEnd_692435 355551976996103578578055 := by
  unfold tailWord_692435
  simp only [CollatzResearch.WordTrace]
  refine ⟨25255179246433728328070759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16836786164289152218713839 25255179246433728328070759)
  ·
    refine ⟨37882768869650592492106139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25255179246433728328070759 37882768869650592492106139)
    ·
      refine ⟨56824153304475888738159209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37882768869650592492106139 56824153304475888738159209)
      ·
        refine ⟨42618114978356916553619407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56824153304475888738159209 42618114978356916553619407)
        ·
          refine ⟨63927172467535374830429111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42618114978356916553619407 63927172467535374830429111)
          ·
            refine ⟨95890758701303062245643667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63927172467535374830429111 95890758701303062245643667)
            ·
              refine ⟨143836138051954593368465501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95890758701303062245643667 143836138051954593368465501)
              ·
                refine ⟨53938551769482972513174563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143836138051954593368465501 53938551769482972513174563)
                ·
                  refine ⟨80907827654224458769761845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53938551769482972513174563 80907827654224458769761845)
                  ·
                    refine ⟨7585108842583543009665173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80907827654224458769761845 7585108842583543009665173)
                    ·
                      refine ⟨355551976996103578578055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7585108842583543009665173 355551976996103578578055)
                      ·
                        rfl

theorem cell23_692435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_692435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692435 prefixEnd_692435 := by exact prefixLift 692435
  have htrace : WordTrace (prefixWord ++ tailWord_692435) baseStart_692435 baseEnd_692435 := by
    simpa [prefixWord, tailWord_692435, baseEnd_692435] using wordTrace_append hprefix tailTrace_692435
  have hstable : (prefixWord ++ tailWord_692435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692435).length < 2 ^ (prefixWord ++ tailWord_692435).sum := by decide
  have hdescent : baseEnd_692435 < baseStart_692435 := by decide
  rcases family_descends (prefixWord ++ tailWord_692435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692442 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_692442 : Nat := 118140960795 + 692442 * 2 ^ 59
def prefixEnd_692442 : Nat := 4983230072969 + 3 ^ 40 * 692442 * 2
def baseEnd_692442 : Nat := 355555571360685051190523

theorem tailTrace_692442 : CollatzResearch.WordTrace tailWord_692442 prefixEnd_692442 355555571360685051190523 := by
  unfold tailWord_692442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313858639352092130893895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16836956371605579015717053 6313858639352092130893895)
  ·
    refine ⟨9470787959028138196340843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313858639352092130893895 9470787959028138196340843)
    ·
      refine ⟨14206181938542207294511265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9470787959028138196340843 14206181938542207294511265)
      ·
        refine ⟨10654636453906655470883449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14206181938542207294511265 10654636453906655470883449)
        ·
          refine ⟨7990977340429991603162587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10654636453906655470883449 7990977340429991603162587)
          ·
            refine ⟨11986466010644987404743881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990977340429991603162587 11986466010644987404743881)
            ·
              refine ⟨8989849507983740553557911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11986466010644987404743881 8989849507983740553557911)
              ·
                refine ⟨13484774261975610830336867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989849507983740553557911 13484774261975610830336867)
                ·
                  refine ⟨20227161392963416245505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13484774261975610830336867 20227161392963416245505301)
                  ·
                    refine ⟨948148190295160136508061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20227161392963416245505301 948148190295160136508061)
                    ·
                      refine ⟨355555571360685051190523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948148190295160136508061 355555571360685051190523)
                      ·
                        rfl

theorem cell23_692442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_692442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692442 prefixEnd_692442 := by exact prefixLift 692442
  have htrace : WordTrace (prefixWord ++ tailWord_692442) baseStart_692442 baseEnd_692442 := by
    simpa [prefixWord, tailWord_692442, baseEnd_692442] using wordTrace_append hprefix tailTrace_692442
  have hstable : (prefixWord ++ tailWord_692442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692442).length < 2 ^ (prefixWord ++ tailWord_692442).sum := by decide
  have hdescent : baseEnd_692442 < baseStart_692442 := by decide
  rcases family_descends (prefixWord ++ tailWord_692442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692456 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_692456 : Nat := 118140960795 + 692456 * 2 ^ 59
def prefixEnd_692456 : Nat := 4983230072969 + 3 ^ 40 * 692456 * 2
def baseEnd_692456 : Nat := 355562760089847996415459

theorem tailTrace_692456 : CollatzResearch.WordTrace tailWord_692456 prefixEnd_692456 355562760089847996415459 := by
  unfold tailWord_692456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627972589678824457292611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16837296786238432609723481 12627972589678824457292611)
  ·
    refine ⟨18941958884518236685938917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12627972589678824457292611 18941958884518236685938917)
    ·
      refine ⟨3551617290847169378613547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18941958884518236685938917 3551617290847169378613547)
      ·
        refine ⟨5327425936270754067920321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551617290847169378613547 5327425936270754067920321)
        ·
          refine ⟨3995569452203065550940241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5327425936270754067920321 3995569452203065550940241)
          ·
            refine ⟨2996677089152299163205181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995569452203065550940241 2996677089152299163205181)
            ·
              refine ⟨1123753908432112186201943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2996677089152299163205181 1123753908432112186201943)
              ·
                refine ⟨1685630862648168279302915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123753908432112186201943 1685630862648168279302915)
                ·
                  refine ⟨2528446293972252418954373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685630862648168279302915 2528446293972252418954373)
                  ·
                    refine ⟨474083680119797328553945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2528446293972252418954373 474083680119797328553945)
                    ·
                      refine ⟨355562760089847996415459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474083680119797328553945 355562760089847996415459)
                      ·
                        rfl

theorem cell23_692456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_692456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692456 prefixEnd_692456 := by exact prefixLift 692456
  have htrace : WordTrace (prefixWord ++ tailWord_692456) baseStart_692456 baseEnd_692456 := by
    simpa [prefixWord, tailWord_692456, baseEnd_692456] using wordTrace_append hprefix tailTrace_692456
  have hstable : (prefixWord ++ tailWord_692456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692456).length < 2 ^ (prefixWord ++ tailWord_692456).sum := by decide
  have hdescent : baseEnd_692456 < baseStart_692456 := by decide
  rcases family_descends (prefixWord ++ tailWord_692456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692472 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_692472 : Nat := 118140960795 + 692472 * 2 ^ 59
def prefixEnd_692472 : Nat := 4983230072969 + 3 ^ 40 * 692472 * 2
def baseEnd_692472 : Nat := 355570975780319933815385

theorem tailTrace_692472 : CollatzResearch.WordTrace tailWord_692472 prefixEnd_692472 355570975780319933815385 := by
  unfold tailWord_692472
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628264373649841823583835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16837685831533122431445113 12628264373649841823583835)
  ·
    refine ⟨18942396560474762735375753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12628264373649841823583835 18942396560474762735375753)
    ·
      refine ⟨14206797420356072051531815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18942396560474762735375753 14206797420356072051531815)
      ·
        refine ⟨21310196130534108077297723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14206797420356072051531815 21310196130534108077297723)
        ·
          refine ⟨31965294195801162115946585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21310196130534108077297723 31965294195801162115946585)
          ·
            refine ⟨23973970646850871586959939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31965294195801162115946585 23973970646850871586959939)
            ·
              refine ⟨35960955970276307380439909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23973970646850871586959939 35960955970276307380439909)
              ·
                refine ⟨6742679244426807633832483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35960955970276307380439909 6742679244426807633832483)
                ·
                  refine ⟨10114018866640211450748725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742679244426807633832483 10114018866640211450748725)
                  ·
                    refine ⟨948189268747519823507693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10114018866640211450748725 948189268747519823507693)
                    ·
                      refine ⟨355570975780319933815385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948189268747519823507693 355570975780319933815385)
                      ·
                        rfl

theorem cell23_692472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_692472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692472 prefixEnd_692472 := by exact prefixLift 692472
  have htrace : WordTrace (prefixWord ++ tailWord_692472) baseStart_692472 baseEnd_692472 := by
    simpa [prefixWord, tailWord_692472, baseEnd_692472] using wordTrace_append hprefix tailTrace_692472
  have hstable : (prefixWord ++ tailWord_692472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692472).length < 2 ^ (prefixWord ++ tailWord_692472).sum := by decide
  have hdescent : baseEnd_692472 < baseStart_692472 := by decide
  rcases family_descends (prefixWord ++ tailWord_692472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692552 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 8]
def baseStart_692552 : Nat := 118140960795 + 692552 * 2 ^ 59
def prefixEnd_692552 : Nat := 4983230072969 + 3 ^ 40 * 692552 * 2
def baseEnd_692552 : Nat := 39512450470297735646113

theorem tailTrace_692552 : CollatzResearch.WordTrace tailWord_692552 prefixEnd_692552 39512450470297735646113 := by
  unfold tailWord_692552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629723293504928655039955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16839631058006571540053273 12629723293504928655039955)
  ·
    refine ⟨18944584940257392982559933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12629723293504928655039955 18944584940257392982559933)
    ·
      refine ⟨7104219352596522368459975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18944584940257392982559933 7104219352596522368459975)
      ·
        refine ⟨10656329028894783552689963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104219352596522368459975 10656329028894783552689963)
        ·
          refine ⟨15984493543342175329034945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10656329028894783552689963 15984493543342175329034945)
          ·
            refine ⟨11988370157506631496776209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15984493543342175329034945 11988370157506631496776209)
            ·
              refine ⟨8991277618129973622582157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11988370157506631496776209 8991277618129973622582157)
              ·
                refine ⟨3371729106798740108468309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8991277618129973622582157 3371729106798740108468309)
                ·
                  refine ⟨39512450470297735646113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3371729106798740108468309 39512450470297735646113)
                  ·
                    rfl

theorem cell23_692552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_692552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692552 prefixEnd_692552 := by exact prefixLift 692552
  have htrace : WordTrace (prefixWord ++ tailWord_692552) baseStart_692552 baseEnd_692552 := by
    simpa [prefixWord, tailWord_692552, baseEnd_692552] using wordTrace_append hprefix tailTrace_692552
  have hstable : (prefixWord ++ tailWord_692552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692552).length < 2 ^ (prefixWord ++ tailWord_692552).sum := by decide
  have hdescent : baseEnd_692552 < baseStart_692552 := by decide
  rcases family_descends (prefixWord ++ tailWord_692552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692583 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_692583 : Nat := 118140960795 + 692583 * 2 ^ 59
def prefixEnd_692583 : Nat := 4983230072969 + 3 ^ 40 * 692583 * 2
def baseEnd_692583 : Nat := 355627972132968999527375

theorem tailTrace_692583 : CollatzResearch.WordTrace tailWord_692583 prefixEnd_692583 355627972132968999527375 := by
  unfold tailWord_692583
  simp only [CollatzResearch.WordTrace]
  refine ⟨25260577249897549604458403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16840384833265033069638935 25260577249897549604458403)
  ·
    refine ⟨37890865874846324406687605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25260577249897549604458403 37890865874846324406687605)
    ·
      refine ⟨3552268675766842913126963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37890865874846324406687605 3552268675766842913126963)
      ·
        refine ⟨5328403013650264369690445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552268675766842913126963 5328403013650264369690445)
        ·
          refine ⟨1998151130118849138633917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5328403013650264369690445 1998151130118849138633917)
          ·
            refine ⟨749306673794568426987719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1998151130118849138633917 749306673794568426987719)
            ·
              refine ⟨1123960010691852640481579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749306673794568426987719 1123960010691852640481579)
              ·
                refine ⟨1685940016037778960722369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123960010691852640481579 1685940016037778960722369)
                ·
                  refine ⟨1264455012028334220541777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685940016037778960722369 1264455012028334220541777)
                  ·
                    refine ⟨948341259021250665406333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264455012028334220541777 948341259021250665406333)
                    ·
                      refine ⟨355627972132968999527375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948341259021250665406333 355627972132968999527375)
                      ·
                        rfl

theorem cell23_692583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_692583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692583 prefixEnd_692583 := by exact prefixLift 692583
  have htrace : WordTrace (prefixWord ++ tailWord_692583) baseStart_692583 baseEnd_692583 := by
    simpa [prefixWord, tailWord_692583, baseEnd_692583] using wordTrace_append hprefix tailTrace_692583
  have hstable : (prefixWord ++ tailWord_692583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692583).length < 2 ^ (prefixWord ++ tailWord_692583).sum := by decide
  have hdescent : baseEnd_692583 < baseStart_692583 := by decide
  rcases family_descends (prefixWord ++ tailWord_692583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692639 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_692639 : Nat := 118140960795 + 692639 * 2 ^ 59
def prefixEnd_692639 : Nat := 4983230072969 + 3 ^ 40 * 692639 * 2
def baseEnd_692639 : Nat := 355656727049620780427117

theorem tailTrace_692639 : CollatzResearch.WordTrace tailWord_692639 prefixEnd_692639 355656727049620780427117 := by
  unfold tailWord_692639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262619737694671168496971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16841746491796447445664647 25262619737694671168496971)
  ·
    refine ⟨37893929606542006752745457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25262619737694671168496971 37893929606542006752745457)
    ·
      refine ⟨28420447204906505064559093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37893929606542006752745457 28420447204906505064559093)
      ·
        refine ⟨2664416925459984849802415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28420447204906505064559093 2664416925459984849802415)
        ·
          refine ⟨3996625388189977274703623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664416925459984849802415 3996625388189977274703623)
          ·
            refine ⟨5994938082284965912055435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996625388189977274703623 5994938082284965912055435)
            ·
              refine ⟨8992407123427448868083153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994938082284965912055435 8992407123427448868083153)
              ·
                refine ⟨6744305342570586651062365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992407123427448868083153 6744305342570586651062365)
                ·
                  refine ⟨2529114503463969994148387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6744305342570586651062365 2529114503463969994148387)
                  ·
                    refine ⟨3793671755195954991222581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529114503463969994148387 3793671755195954991222581)
                    ·
                      refine ⟨355656727049620780427117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3793671755195954991222581 355656727049620780427117)
                      ·
                        rfl

theorem cell23_692639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_692639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692639 prefixEnd_692639 := by exact prefixLift 692639
  have htrace : WordTrace (prefixWord ++ tailWord_692639) baseStart_692639 baseEnd_692639 := by
    simpa [prefixWord, tailWord_692639, baseEnd_692639] using wordTrace_append hprefix tailTrace_692639
  have hstable : (prefixWord ++ tailWord_692639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692639).length < 2 ^ (prefixWord ++ tailWord_692639).sum := by decide
  have hdescent : baseEnd_692639 < baseStart_692639 := by decide
  rcases family_descends (prefixWord ++ tailWord_692639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692647 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_692647 : Nat := 118140960795 + 692647 * 2 ^ 59
def prefixEnd_692647 : Nat := 4983230072969 + 3 ^ 40 * 692647 * 2
def baseEnd_692647 : Nat := 355660834894856749127081

theorem tailTrace_692647 : CollatzResearch.WordTrace tailWord_692647 prefixEnd_692647 355660834894856749127081 := by
  unfold tailWord_692647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262911521665688534788195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16841941014443792356525463 25262911521665688534788195)
  ·
    refine ⟨37894367282498532802182293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25262911521665688534788195 37894367282498532802182293)
    ·
      refine ⟨1776298466367118725102295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37894367282498532802182293 1776298466367118725102295)
      ·
        refine ⟨2664447699550678087653443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776298466367118725102295 2664447699550678087653443)
        ·
          refine ⟨3996671549326017131480165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664447699550678087653443 3996671549326017131480165)
          ·
            refine ⟨749375915498628212152531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3996671549326017131480165 749375915498628212152531)
            ·
              refine ⟨1124063873247942318228797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749375915498628212152531 1124063873247942318228797)
              ·
                refine ⟨421523952467978369335799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124063873247942318228797 421523952467978369335799)
                ·
                  refine ⟨632285928701967554003699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421523952467978369335799 632285928701967554003699)
                  ·
                    refine ⟨948428893052951331005549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632285928701967554003699 948428893052951331005549)
                    ·
                      refine ⟨355660834894856749127081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948428893052951331005549 355660834894856749127081)
                      ·
                        rfl

theorem cell23_692647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_692647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692647 prefixEnd_692647 := by exact prefixLift 692647
  have htrace : WordTrace (prefixWord ++ tailWord_692647) baseStart_692647 baseEnd_692647 := by
    simpa [prefixWord, tailWord_692647, baseEnd_692647] using wordTrace_append hprefix tailTrace_692647
  have hstable : (prefixWord ++ tailWord_692647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692647).length < 2 ^ (prefixWord ++ tailWord_692647).sum := by decide
  have hdescent : baseEnd_692647 < baseStart_692647 := by decide
  rcases family_descends (prefixWord ++ tailWord_692647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692649 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_692649 : Nat := 118140960795 + 692649 * 2 ^ 59
def prefixEnd_692649 : Nat := 4983230072969 + 3 ^ 40 * 692649 * 2
def baseEnd_692649 : Nat := 355661861856165741302071

theorem tailTrace_692649 : CollatzResearch.WordTrace tailWord_692649 prefixEnd_692649 355661861856165741302071 := by
  unfold tailWord_692649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262984467658442876361001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16841989645105628584240667 25262984467658442876361001)
  ·
    refine ⟨18947238350743832157270751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25262984467658442876361001 18947238350743832157270751)
    ·
      refine ⟨28420857526115748235906127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18947238350743832157270751 28420857526115748235906127)
      ·
        refine ⟨42631286289173622353859191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28420857526115748235906127 42631286289173622353859191)
        ·
          refine ⟨63946929433760433530788787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42631286289173622353859191 63946929433760433530788787)
          ·
            refine ⟨95920394150640650296183181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63946929433760433530788787 95920394150640650296183181)
            ·
              refine ⟨35970147806490243861068693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95920394150640650296183181 35970147806490243861068693)
              ·
                refine ⟨1686100678429230180987595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35970147806490243861068693 1686100678429230180987595)
                ·
                  refine ⟨2529151017643845271481393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686100678429230180987595 2529151017643845271481393)
                  ·
                    refine ⟨1896863263232883953611045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529151017643845271481393 1896863263232883953611045)
                    ·
                      refine ⟨355661861856165741302071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1896863263232883953611045 355661861856165741302071)
                      ·
                        rfl

theorem cell23_692649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_692649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692649 prefixEnd_692649 := by exact prefixLift 692649
  have htrace : WordTrace (prefixWord ++ tailWord_692649) baseStart_692649 baseEnd_692649 := by
    simpa [prefixWord, tailWord_692649, baseEnd_692649] using wordTrace_append hprefix tailTrace_692649
  have hstable : (prefixWord ++ tailWord_692649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692649).length < 2 ^ (prefixWord ++ tailWord_692649).sum := by decide
  have hdescent : baseEnd_692649 < baseStart_692649 := by decide
  rcases family_descends (prefixWord ++ tailWord_692649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692670 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_692670 : Nat := 118140960795 + 692670 * 2 ^ 59
def prefixEnd_692670 : Nat := 4983230072969 + 3 ^ 40 * 692670 * 2
def baseEnd_692670 : Nat := 355672644949910159139475

theorem tailTrace_692670 : CollatzResearch.WordTrace tailWord_692670 prefixEnd_692670 355672644949910159139475 := by
  unfold tailWord_692670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157968800072795432859433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16842500267054908975250309 3157968800072795432859433)
  ·
    refine ⟨2368476600054596574644575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3157968800072795432859433 2368476600054596574644575)
    ·
      refine ⟨3552714900081894861966863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368476600054596574644575 3552714900081894861966863)
      ·
        refine ⟨5329072350122842292950295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552714900081894861966863 5329072350122842292950295)
        ·
          refine ⟨7993608525184263439425443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329072350122842292950295 7993608525184263439425443)
          ·
            refine ⟨11990412787776395159138165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993608525184263439425443 11990412787776395159138165)
            ·
              refine ⟨1124101198854037046169203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11990412787776395159138165 1124101198854037046169203)
              ·
                refine ⟨1686151798281055569253805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124101198854037046169203 1686151798281055569253805)
                ·
                  refine ⟨632306924355395838470177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1686151798281055569253805 632306924355395838470177)
                  ·
                    refine ⟨474230193266546878852633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632306924355395838470177 474230193266546878852633)
                    ·
                      refine ⟨355672644949910159139475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474230193266546878852633 355672644949910159139475)
                      ·
                        rfl

theorem cell23_692670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_692670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692670 prefixEnd_692670 := by exact prefixLift 692670
  have htrace : WordTrace (prefixWord ++ tailWord_692670) baseStart_692670 baseEnd_692670 := by
    simpa [prefixWord, tailWord_692670, baseEnd_692670] using wordTrace_append hprefix tailTrace_692670
  have hstable : (prefixWord ++ tailWord_692670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692670).length < 2 ^ (prefixWord ++ tailWord_692670).sum := by decide
  have hdescent : baseEnd_692670 < baseStart_692670 := by decide
  rcases family_descends (prefixWord ++ tailWord_692670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692680 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_692680 : Nat := 118140960795 + 692680 * 2 ^ 59
def prefixEnd_692680 : Nat := 4983230072969 + 3 ^ 40 * 692680 * 2
def baseEnd_692680 : Nat := 118559259918818373338143

theorem tailTrace_692680 : CollatzResearch.WordTrace tailWord_692680 prefixEnd_692680 118559259918818373338143 := by
  unfold tailWord_692680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632057565273067585369747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16842743420364090113826329 12632057565273067585369747)
  ·
    refine ⟨18948086347909601378054621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632057565273067585369747 18948086347909601378054621)
    ·
      refine ⟨7105532380466100516770483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18948086347909601378054621 7105532380466100516770483)
      ·
        refine ⟨10658298570699150775155725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105532380466100516770483 10658298570699150775155725)
        ·
          refine ⟨3996861964012181540683397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10658298570699150775155725 3996861964012181540683397)
          ·
            refine ⟨749411618252284038878137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3996861964012181540683397 749411618252284038878137)
            ·
              refine ⟨562058713689213029158603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749411618252284038878137 562058713689213029158603)
              ·
                refine ⟨843088070533819543737905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562058713689213029158603 843088070533819543737905)
                ·
                  refine ⟨632316052900364657803429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843088070533819543737905 632316052900364657803429)
                  ·
                    refine ⟨118559259918818373338143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632316052900364657803429 118559259918818373338143)
                    ·
                      rfl

theorem cell23_692680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_692680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692680 prefixEnd_692680 := by exact prefixLift 692680
  have htrace : WordTrace (prefixWord ++ tailWord_692680) baseStart_692680 baseEnd_692680 := by
    simpa [prefixWord, tailWord_692680, baseEnd_692680] using wordTrace_append hprefix tailTrace_692680
  have hstable : (prefixWord ++ tailWord_692680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692680).length < 2 ^ (prefixWord ++ tailWord_692680).sum := by decide
  have hdescent : baseEnd_692680 < baseStart_692680 := by decide
  rcases family_descends (prefixWord ++ tailWord_692680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692686 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_692686 : Nat := 118140960795 + 692686 * 2 ^ 59
def prefixEnd_692686 : Nat := 4983230072969 + 3 ^ 40 * 692686 * 2
def baseEnd_692686 : Nat := 355680860640382096539401

theorem tailTrace_692686 : CollatzResearch.WordTrace tailWord_692686 prefixEnd_692686 355680860640382096539401 := by
  unfold tailWord_692686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158041746065549774432239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16842889312349598796971941 3158041746065549774432239)
  ·
    refine ⟨4737062619098324661648359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3158041746065549774432239 4737062619098324661648359)
    ·
      refine ⟨7105593928647486992472539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4737062619098324661648359 7105593928647486992472539)
      ·
        refine ⟨10658390892971230488708809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105593928647486992472539 10658390892971230488708809)
        ·
          refine ⟨7993793169728422866531607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10658390892971230488708809 7993793169728422866531607)
          ·
            refine ⟨11990689754592634299797411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993793169728422866531607 11990689754592634299797411)
            ·
              refine ⟨17986034631888951449696117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11990689754592634299797411 17986034631888951449696117)
              ·
                refine ⟨1686190746739589198409011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17986034631888951449696117 1686190746739589198409011)
                ·
                  refine ⟨2529286120109383797613517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686190746739589198409011 2529286120109383797613517)
                  ·
                    refine ⟨948482295041018924105069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529286120109383797613517 948482295041018924105069)
                    ·
                      refine ⟨355680860640382096539401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948482295041018924105069 355680860640382096539401)
                      ·
                        rfl

theorem cell23_692686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_692686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692686 prefixEnd_692686 := by exact prefixLift 692686
  have htrace : WordTrace (prefixWord ++ tailWord_692686) baseStart_692686 baseEnd_692686 := by
    simpa [prefixWord, tailWord_692686, baseEnd_692686] using wordTrace_append hprefix tailTrace_692686
  have hstable : (prefixWord ++ tailWord_692686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692686).length < 2 ^ (prefixWord ++ tailWord_692686).sum := by decide
  have hdescent : baseEnd_692686 < baseStart_692686 := by decide
  rcases family_descends (prefixWord ++ tailWord_692686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692690 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_692690 : Nat := 118140960795 + 692690 * 2 ^ 59
def prefixEnd_692690 : Nat := 4983230072969 + 3 ^ 40 * 692690 * 2
def baseEnd_692690 : Nat := 355682914563000080889383

theorem tailTrace_692690 : CollatzResearch.WordTrace tailWord_692690 prefixEnd_692690 355682914563000080889383 := by
  unfold tailWord_692690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316119965127476719650881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16842986573673271252402349 6316119965127476719650881)
  ·
    refine ⟨4737089973845607539738161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6316119965127476719650881 4737089973845607539738161)
    ·
      refine ⟨3552817480384205654803621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4737089973845607539738161 3552817480384205654803621)
      ·
        refine ⟨666153277572038560275679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3552817480384205654803621 666153277572038560275679)
        ·
          refine ⟨999229916358057840413519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666153277572038560275679 999229916358057840413519)
          ·
            refine ⟨1498844874537086760620279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999229916358057840413519 1498844874537086760620279)
            ·
              refine ⟨2248267311805630140930419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498844874537086760620279 2248267311805630140930419)
              ·
                refine ⟨3372400967708445211395629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248267311805630140930419 3372400967708445211395629)
                ·
                  refine ⟨1264650362890666954273361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3372400967708445211395629 1264650362890666954273361)
                  ·
                    refine ⟨948487772168000215705021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264650362890666954273361 948487772168000215705021)
                    ·
                      refine ⟨355682914563000080889383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948487772168000215705021 355682914563000080889383)
                      ·
                        rfl

theorem cell23_692690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_692690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692690 prefixEnd_692690 := by exact prefixLift 692690
  have htrace : WordTrace (prefixWord ++ tailWord_692690) baseStart_692690 baseEnd_692690 := by
    simpa [prefixWord, tailWord_692690, baseEnd_692690] using wordTrace_append hprefix tailTrace_692690
  have hstable : (prefixWord ++ tailWord_692690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692690).length < 2 ^ (prefixWord ++ tailWord_692690).sum := by decide
  have hdescent : baseEnd_692690 < baseStart_692690 := by decide
  rcases family_descends (prefixWord ++ tailWord_692690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692719 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 6]
def baseStart_692719 : Nat := 118140960795 + 692719 * 2 ^ 59
def prefixEnd_692719 : Nat := 4983230072969 + 3 ^ 40 * 692719 * 2
def baseEnd_692719 : Nat := 118565935167326822475583

theorem tailTrace_692719 : CollatzResearch.WordTrace tailWord_692719 prefixEnd_692719 118565935167326822475583 := by
  unfold tailWord_692719
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265537577404844831409211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16843691718269896554272807 25265537577404844831409211)
  ·
    refine ⟨37898306366107267247113817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25265537577404844831409211 37898306366107267247113817)
    ·
      refine ⟨28423729774580450435335363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37898306366107267247113817 28423729774580450435335363)
      ·
        refine ⟨42635594661870675653003045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28423729774580450435335363 42635594661870675653003045)
        ·
          refine ⟨7994173999100751684938071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42635594661870675653003045 7994173999100751684938071)
          ·
            refine ⟨11991260998651127527407107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994173999100751684938071 11991260998651127527407107)
            ·
              refine ⟨17986891497976691291110661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991260998651127527407107 17986891497976691291110661)
              ·
                refine ⟨3372542155870629617083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17986891497976691291110661 3372542155870629617083249)
                ·
                  refine ⟨2529406616902972212812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3372542155870629617083249 2529406616902972212812437)
                  ·
                    refine ⟨118565935167326822475583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2529406616902972212812437 118565935167326822475583)
                    ·
                      rfl

theorem cell23_692719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_692719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692719 prefixEnd_692719 := by exact prefixLift 692719
  have htrace : WordTrace (prefixWord ++ tailWord_692719) baseStart_692719 baseEnd_692719 := by
    simpa [prefixWord, tailWord_692719, baseEnd_692719] using wordTrace_append hprefix tailTrace_692719
  have hstable : (prefixWord ++ tailWord_692719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692719).length < 2 ^ (prefixWord ++ tailWord_692719).sum := by decide
  have hdescent : baseEnd_692719 < baseStart_692719 := by decide
  rcases family_descends (prefixWord ++ tailWord_692719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692726 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_692726 : Nat := 118140960795 + 692726 * 2 ^ 59
def prefixEnd_692726 : Nat := 4983230072969 + 3 ^ 40 * 692726 * 2
def baseEnd_692726 : Nat := 355701399866561940039217

theorem tailTrace_692726 : CollatzResearch.WordTrace tailWord_692726 prefixEnd_692726 355701399866561940039217 := by
  unfold tailWord_692726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579112055523717814182127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16843861925586323351276021 1579112055523717814182127)
  ·
    refine ⟨2368668083285576721273191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579112055523717814182127 2368668083285576721273191)
    ·
      refine ⟨3553002124928365081909787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368668083285576721273191 3553002124928365081909787)
      ·
        refine ⟨5329503187392547622864681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553002124928365081909787 5329503187392547622864681)
        ·
          refine ⟨3997127390544410717148511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329503187392547622864681 3997127390544410717148511)
          ·
            refine ⟨5995691085816616075722767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997127390544410717148511 5995691085816616075722767)
            ·
              refine ⟨8993536628724924113584151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995691085816616075722767 8993536628724924113584151)
              ·
                refine ⟨13490304943087386170376227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993536628724924113584151 13490304943087386170376227)
                ·
                  refine ⟨20235457414631079255564341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13490304943087386170376227 20235457414631079255564341)
                  ·
                    refine ⟨1897074132621663680209157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20235457414631079255564341 1897074132621663680209157)
                    ·
                      refine ⟨355701399866561940039217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1897074132621663680209157 355701399866561940039217)
                      ·
                        rfl

theorem cell23_692726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_692726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692726 prefixEnd_692726 := by exact prefixLift 692726
  have htrace : WordTrace (prefixWord ++ tailWord_692726) baseStart_692726 baseEnd_692726 := by
    simpa [prefixWord, tailWord_692726, baseEnd_692726] using wordTrace_append hprefix tailTrace_692726
  have hstable : (prefixWord ++ tailWord_692726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692726).length < 2 ^ (prefixWord ++ tailWord_692726).sum := by decide
  have hdescent : baseEnd_692726 < baseStart_692726 := by decide
  rcases family_descends (prefixWord ++ tailWord_692726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692729 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_692729 : Nat := 118140960795 + 692729 * 2 ^ 59
def prefixEnd_692729 : Nat := 4983230072969 + 3 ^ 40 * 692729 * 2
def baseEnd_692729 : Nat := 355702940308525428301703

theorem tailTrace_692729 : CollatzResearch.WordTrace tailWord_692729 prefixEnd_692729 355702940308525428301703 := by
  unfold tailWord_692729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265902307368616539273241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16843934871579077692848827 25265902307368616539273241)
  ·
    refine ⟨18949426730526462404454931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25265902307368616539273241 18949426730526462404454931)
    ·
      refine ⟨28424140095789693606682397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18949426730526462404454931 28424140095789693606682397)
      ·
        refine ⟨10659052535921135102505899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28424140095789693606682397 10659052535921135102505899)
        ·
          refine ⟨15988578803881702653758849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659052535921135102505899 15988578803881702653758849)
          ·
            refine ⟨11991434102911276990319137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15988578803881702653758849 11991434102911276990319137)
            ·
              refine ⟨8993575577183457742739353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11991434102911276990319137 8993575577183457742739353)
              ·
                refine ⟨6745181682887593307054515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993575577183457742739353 6745181682887593307054515)
                ·
                  refine ⟨10117772524331389960581773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745181682887593307054515 10117772524331389960581773)
                  ·
                    refine ⟨3794164696624271235218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10117772524331389960581773 3794164696624271235218165)
                    ·
                      refine ⟨355702940308525428301703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3794164696624271235218165 355702940308525428301703)
                      ·
                        rfl

theorem cell23_692729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_692729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692729 prefixEnd_692729 := by exact prefixLift 692729
  have htrace : WordTrace (prefixWord ++ tailWord_692729) baseStart_692729 baseEnd_692729 := by
    simpa [prefixWord, tailWord_692729, baseEnd_692729] using wordTrace_append hprefix tailTrace_692729
  have hstable : (prefixWord ++ tailWord_692729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692729).length < 2 ^ (prefixWord ++ tailWord_692729).sum := by decide
  have hdescent : baseEnd_692729 < baseStart_692729 := by decide
  rcases family_descends (prefixWord ++ tailWord_692729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692746 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_692746 : Nat := 118140960795 + 692746 * 2 ^ 59
def prefixEnd_692746 : Nat := 4983230072969 + 3 ^ 40 * 692746 * 2
def baseEnd_692746 : Nat := 355711669479651861789125

theorem tailTrace_692746 : CollatzResearch.WordTrace tailWord_692746 prefixEnd_692746 355711669479651861789125 := by
  unfold tailWord_692746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316630587076757110660523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16844348232204685628428061 6316630587076757110660523)
  ·
    refine ⟨9474945880615135665990785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316630587076757110660523 9474945880615135665990785)
    ·
      refine ⟨7106209410461351749493089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9474945880615135665990785 7106209410461351749493089)
      ·
        refine ⟨5329657057846013812119817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7106209410461351749493089 5329657057846013812119817)
        ·
          refine ⟨3997242793384510359089863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329657057846013812119817 3997242793384510359089863)
          ·
            refine ⟨5995864190076765538634795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997242793384510359089863 5995864190076765538634795)
            ·
              refine ⟨8993796285115148307952193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995864190076765538634795 8993796285115148307952193)
              ·
                refine ⟨6745347213836361230964145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993796285115148307952193 6745347213836361230964145)
                ·
                  refine ⟨5059010410377270923223109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745347213836361230964145 5059010410377270923223109)
                  ·
                    refine ⟨948564451945738298104333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059010410377270923223109 948564451945738298104333)
                    ·
                      refine ⟨355711669479651861789125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948564451945738298104333 355711669479651861789125)
                      ·
                        rfl

theorem cell23_692746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_692746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692746 prefixEnd_692746 := by exact prefixLift 692746
  have htrace : WordTrace (prefixWord ++ tailWord_692746) baseStart_692746 baseEnd_692746 := by
    simpa [prefixWord, tailWord_692746, baseEnd_692746] using wordTrace_append hprefix tailTrace_692746
  have hstable : (prefixWord ++ tailWord_692746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692746).length < 2 ^ (prefixWord ++ tailWord_692746).sum := by decide
  have hdescent : baseEnd_692746 < baseStart_692746 := by decide
  rcases family_descends (prefixWord ++ tailWord_692746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692796 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_692796 : Nat := 118140960795 + 692796 * 2 ^ 59
def prefixEnd_692796 : Nat := 4983230072969 + 3 ^ 40 * 692796 * 2
def baseEnd_692796 : Nat := 118579114504125555387965

theorem tailTrace_692796 : CollatzResearch.WordTrace tailWord_692796 prefixEnd_692796 118579114504125555387965 := by
  unfold tailWord_692796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634172999062943490981121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16845563998750591321308161 12634172999062943490981121)
  ·
    refine ⟨9475629749297207618235841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12634172999062943490981121 9475629749297207618235841)
    ·
      refine ⟨7106722311972905713676881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9475629749297207618235841 7106722311972905713676881)
      ·
        refine ⟨5330041733979679285257661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7106722311972905713676881 5330041733979679285257661)
        ·
          refine ⟨1998765650242379731971623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5330041733979679285257661 1998765650242379731971623)
          ·
            refine ⟨2998148475363569597957435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998765650242379731971623 2998148475363569597957435)
            ·
              refine ⟨4497222713045354396936153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998148475363569597957435 4497222713045354396936153)
              ·
                refine ⟨3372917034784015797702115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497222713045354396936153 3372917034784015797702115)
                ·
                  refine ⟨5059375552176023696553173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372917034784015797702115 5059375552176023696553173)
                  ·
                    refine ⟨118579114504125555387965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5059375552176023696553173 118579114504125555387965)
                    ·
                      rfl

theorem cell23_692796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_692796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692796 prefixEnd_692796 := by exact prefixLift 692796
  have htrace : WordTrace (prefixWord ++ tailWord_692796) baseStart_692796 baseEnd_692796 := by
    simpa [prefixWord, tailWord_692796, baseEnd_692796] using wordTrace_append hprefix tailTrace_692796
  have hstable : (prefixWord ++ tailWord_692796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692796).length < 2 ^ (prefixWord ++ tailWord_692796).sum := by decide
  have hdescent : baseEnd_692796 < baseStart_692796 := by decide
  rcases family_descends (prefixWord ++ tailWord_692796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692813 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_692813 : Nat := 118140960795 + 692813 * 2 ^ 59
def prefixEnd_692813 : Nat := 4983230072969 + 3 ^ 40 * 692813 * 2
def baseEnd_692813 : Nat := 118582024227834366550439

theorem tailTrace_692813 : CollatzResearch.WordTrace tailWord_692813 prefixEnd_692813 118582024227834366550439 := by
  unfold tailWord_692813
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268966039064298885331093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16845977359376199256887395 25268966039064298885331093)
  ·
    refine ⟨1184482783081139010249895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25268966039064298885331093 1184482783081139010249895)
    ·
      refine ⟨1776724174621708515374843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184482783081139010249895 1776724174621708515374843)
      ·
        refine ⟨2665086261932562773062265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776724174621708515374843 2665086261932562773062265)
        ·
          refine ⟨1998814696449422079796699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665086261932562773062265 1998814696449422079796699)
          ·
            refine ⟨2998222044674133119695049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998814696449422079796699 2998222044674133119695049)
            ·
              refine ⟨2248666533505599839771287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998222044674133119695049 2248666533505599839771287)
              ·
                refine ⟨3372999800258399759656931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248666533505599839771287 3372999800258399759656931)
                ·
                  refine ⟨5059499700387599639485397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372999800258399759656931 5059499700387599639485397)
                  ·
                    refine ⟨118582024227834366550439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5059499700387599639485397 118582024227834366550439)
                    ·
                      rfl

theorem cell23_692813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_692813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692813 prefixEnd_692813 := by exact prefixLift 692813
  have htrace : WordTrace (prefixWord ++ tailWord_692813) baseStart_692813 baseEnd_692813 := by
    simpa [prefixWord, tailWord_692813, baseEnd_692813] using wordTrace_append hprefix tailTrace_692813
  have hstable : (prefixWord ++ tailWord_692813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692813).length < 2 ^ (prefixWord ++ tailWord_692813).sum := by decide
  have hdescent : baseEnd_692813 < baseStart_692813 := by decide
  rcases family_descends (prefixWord ++ tailWord_692813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692819 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_692819 : Nat := 118140960795 + 692819 * 2 ^ 59
def prefixEnd_692819 : Nat := 4983230072969 + 3 ^ 40 * 692819 * 2
def baseEnd_692819 : Nat := 355749153567430076176289

theorem tailTrace_692819 : CollatzResearch.WordTrace tailWord_692819 prefixEnd_692819 355749153567430076176289 := by
  unfold tailWord_692819
  simp only [CollatzResearch.WordTrace]
  refine ⟨25269184877042561910049511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16846123251361707940033007 25269184877042561910049511)
  ·
    refine ⟨37903777315563842865074267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25269184877042561910049511 37903777315563842865074267)
    ·
      refine ⟨56855665973345764297611401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37903777315563842865074267 56855665973345764297611401)
      ·
        refine ⟨42641749480009323223208551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56855665973345764297611401 42641749480009323223208551)
        ·
          refine ⟨63962624220013984834812827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42641749480009323223208551 63962624220013984834812827)
          ·
            refine ⟨95943936330020977252219241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63962624220013984834812827 95943936330020977252219241)
            ·
              refine ⟨71957952247515732939164431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95943936330020977252219241 71957952247515732939164431)
              ·
                refine ⟨107936928371273599408746647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71957952247515732939164431 107936928371273599408746647)
                ·
                  refine ⟨161905392556910399113119971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107936928371273599408746647 161905392556910399113119971)
                  ·
                    refine ⟨242858088835365598669679957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161905392556910399113119971 242858088835365598669679957)
                    ·
                      refine ⟨355749153567430076176289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 242858088835365598669679957 355749153567430076176289)
                      ·
                        rfl

theorem cell23_692819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_692819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692819 prefixEnd_692819 := by exact prefixLift 692819
  have htrace : WordTrace (prefixWord ++ tailWord_692819) baseStart_692819 baseEnd_692819 := by
    simpa [prefixWord, tailWord_692819, baseEnd_692819] using wordTrace_append hprefix tailTrace_692819
  have hstable : (prefixWord ++ tailWord_692819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692819).length < 2 ^ (prefixWord ++ tailWord_692819).sum := by decide
  have hdescent : baseEnd_692819 < baseStart_692819 := by decide
  rcases family_descends (prefixWord ++ tailWord_692819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692833 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_692833 : Nat := 118140960795 + 692833 * 2 ^ 59
def prefixEnd_692833 : Nat := 4983230072969 + 3 ^ 40 * 692833 * 2
def baseEnd_692833 : Nat := 355756342296593021401225

theorem tailTrace_692833 : CollatzResearch.WordTrace tailWord_692833 prefixEnd_692833 355756342296593021401225 := by
  unfold tailWord_692833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25269695498991842301059153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16846463665994561534039435 25269695498991842301059153)
  ·
    refine ⟨18952271624243881725794365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25269695498991842301059153 18952271624243881725794365)
    ·
      refine ⟨7107101859091455647172887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18952271624243881725794365 7107101859091455647172887)
      ·
        refine ⟨10660652788637183470759331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107101859091455647172887 10660652788637183470759331)
        ·
          refine ⟨15990979182955775206138997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10660652788637183470759331 15990979182955775206138997)
          ·
            refine ⟨1499154298402103925575531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15990979182955775206138997 1499154298402103925575531)
            ·
              refine ⟨2248731447603155888363297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499154298402103925575531 2248731447603155888363297)
              ·
                refine ⟨1686548585702366916272473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248731447603155888363297 1686548585702366916272473)
                ·
                  refine ⟨1264911439276775187204355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686548585702366916272473 1264911439276775187204355)
                  ·
                    refine ⟨1897367158915162780806533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1264911439276775187204355 1897367158915162780806533)
                    ·
                      refine ⟨355756342296593021401225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1897367158915162780806533 355756342296593021401225)
                      ·
                        rfl

theorem cell23_692833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_692833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692833 prefixEnd_692833 := by exact prefixLift 692833
  have htrace : WordTrace (prefixWord ++ tailWord_692833) baseStart_692833 baseEnd_692833 := by
    simpa [prefixWord, tailWord_692833, baseEnd_692833] using wordTrace_append hprefix tailTrace_692833
  have hstable : (prefixWord ++ tailWord_692833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692833).length < 2 ^ (prefixWord ++ tailWord_692833).sum := by decide
  have hdescent : baseEnd_692833 < baseStart_692833 := by decide
  rcases family_descends (prefixWord ++ tailWord_692833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692834 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_692834 : Nat := 118140960795 + 692834 * 2 ^ 59
def prefixEnd_692834 : Nat := 4983230072969 + 3 ^ 40 * 692834 * 2
def baseEnd_692834 : Nat := 39528539530805279720969

theorem tailTrace_692834 : CollatzResearch.WordTrace tailWord_692834 prefixEnd_692834 39528539530805279720969 := by
  unfold tailWord_692834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317432992997054867961389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16846487981325479647897037 6317432992997054867961389)
  ·
    refine ⟨2369037372373895575485521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6317432992997054867961389 2369037372373895575485521)
    ·
      refine ⟨1776778029280421681614141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2369037372373895575485521 1776778029280421681614141)
      ·
        refine ⟨666291760980158130605303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1776778029280421681614141 666291760980158130605303)
        ·
          refine ⟨999437641470237195907955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666291760980158130605303 999437641470237195907955)
          ·
            refine ⟨1499156462205355793861933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999437641470237195907955 1499156462205355793861933)
            ·
              refine ⟨562183673327008422698225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499156462205355793861933 562183673327008422698225)
              ·
                refine ⟨421637754995256317023669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562183673327008422698225 421637754995256317023669)
                ·
                  refine ⟨39528539530805279720969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 421637754995256317023669 39528539530805279720969)
                  ·
                    rfl

theorem cell23_692834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_692834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692834 prefixEnd_692834 := by exact prefixLift 692834
  have htrace : WordTrace (prefixWord ++ tailWord_692834) baseStart_692834 baseEnd_692834 := by
    simpa [prefixWord, tailWord_692834, baseEnd_692834] using wordTrace_append hprefix tailTrace_692834
  have hstable : (prefixWord ++ tailWord_692834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692834).length < 2 ^ (prefixWord ++ tailWord_692834).sum := by decide
  have hdescent : baseEnd_692834 < baseStart_692834 := by decide
  rcases family_descends (prefixWord ++ tailWord_692834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692856 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 6]
def baseStart_692856 : Nat := 118140960795 + 692856 * 2 ^ 59
def prefixEnd_692856 : Nat := 4983230072969 + 3 ^ 40 * 692856 * 2
def baseEnd_692856 : Nat := 39529794705738492379291

theorem tailTrace_692856 : CollatzResearch.WordTrace tailWord_692856 prefixEnd_692856 39529794705738492379291 := by
  unfold tailWord_692856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635267188954258614573211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16847022918605678152764281 12635267188954258614573211)
  ·
    refine ⟨18952900783431387921859817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12635267188954258614573211 18952900783431387921859817)
    ·
      refine ⟨14214675587573540941394863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18952900783431387921859817 14214675587573540941394863)
      ·
        refine ⟨21322013381360311412092295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214675587573540941394863 21322013381360311412092295)
        ·
          refine ⟨31983020072040467118138443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21322013381360311412092295 31983020072040467118138443)
          ·
            refine ⟨47974530108060700677207665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31983020072040467118138443 47974530108060700677207665)
            ·
              refine ⟨35980897581045525507905749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47974530108060700677207665 35980897581045525507905749)
              ·
                refine ⟨843302287055754504091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35980897581045525507905749 843302287055754504091541)
                ·
                  refine ⟨39529794705738492379291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 843302287055754504091541 39529794705738492379291)
                  ·
                    rfl

theorem cell23_692856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_692856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692856 prefixEnd_692856 := by exact prefixLift 692856
  have htrace : WordTrace (prefixWord ++ tailWord_692856) baseStart_692856 baseEnd_692856 := by
    simpa [prefixWord, tailWord_692856, baseEnd_692856] using wordTrace_append hprefix tailTrace_692856
  have hstable : (prefixWord ++ tailWord_692856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692856).length < 2 ^ (prefixWord ++ tailWord_692856).sum := by decide
  have hdescent : baseEnd_692856 < baseStart_692856 := by decide
  rcases family_descends (prefixWord ++ tailWord_692856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692883 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 3]
def baseStart_692883 : Nat := 118140960795 + 692883 * 2 ^ 59
def prefixEnd_692883 : Nat := 4983230072969 + 3 ^ 40 * 692883 * 2
def baseEnd_692883 : Nat := 355782016329317825775995

theorem tailTrace_692883 : CollatzResearch.WordTrace tailWord_692883 prefixEnd_692883 355782016329317825775995 := by
  unfold tailWord_692883
  simp only [CollatzResearch.WordTrace]
  refine ⟨25271519148810700840379303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16847679432540467226919535 25271519148810700840379303)
  ·
    refine ⟨37907278723216051260568955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25271519148810700840379303 37907278723216051260568955)
    ·
      refine ⟨56860918084824076890853433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37907278723216051260568955 56860918084824076890853433)
      ·
        refine ⟨42645688563618057668140075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56860918084824076890853433 42645688563618057668140075)
        ·
          refine ⟨63968532845427086502210113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42645688563618057668140075 63968532845427086502210113)
          ·
            refine ⟨47976399634070314876657585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63968532845427086502210113 47976399634070314876657585)
            ·
              refine ⟨35982299725552736157493189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47976399634070314876657585 35982299725552736157493189)
              ·
                refine ⟨6746681198541138029529973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35982299725552736157493189 6746681198541138029529973)
                ·
                  refine ⟨632501362363231690268435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6746681198541138029529973 632501362363231690268435)
                  ·
                    refine ⟨948752043544847535402653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632501362363231690268435 948752043544847535402653)
                    ·
                      refine ⟨355782016329317825775995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948752043544847535402653 355782016329317825775995)
                      ·
                        rfl

theorem cell23_692883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_692883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692883 prefixEnd_692883 := by exact prefixLift 692883
  have htrace : WordTrace (prefixWord ++ tailWord_692883) baseStart_692883 baseEnd_692883 := by
    simpa [prefixWord, tailWord_692883, baseEnd_692883] using wordTrace_append hprefix tailTrace_692883
  have hstable : (prefixWord ++ tailWord_692883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692883).length < 2 ^ (prefixWord ++ tailWord_692883).sum := by decide
  have hdescent : baseEnd_692883 < baseStart_692883 := by decide
  rcases family_descends (prefixWord ++ tailWord_692883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692900 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_692900 : Nat := 118140960795 + 692900 * 2 ^ 59
def prefixEnd_692900 : Nat := 4983230072969 + 3 ^ 40 * 692900 * 2
def baseEnd_692900 : Nat := 355790745500444259263417

theorem tailTrace_692900 : CollatzResearch.WordTrace tailWord_692900 prefixEnd_692900 355790745500444259263417 := by
  unfold tailWord_692900
  simp only [CollatzResearch.WordTrace]
  refine ⟨12636069594874556371874077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16848092793166075162498769 12636069594874556371874077)
  ·
    refine ⟨4738526098077958639452779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12636069594874556371874077 4738526098077958639452779)
    ·
      refine ⟨7107789147116937959179169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738526098077958639452779 7107789147116937959179169)
      ·
        refine ⟨5330841860337703469384377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7107789147116937959179169 5330841860337703469384377)
        ·
          refine ⟨3998131395253277602038283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330841860337703469384377 3998131395253277602038283)
          ·
            refine ⟨5997197092879916403057425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998131395253277602038283 5997197092879916403057425)
            ·
              refine ⟨4497897819659937302293069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5997197092879916403057425 4497897819659937302293069)
              ·
                refine ⟨1686711682372476488359901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497897819659937302293069 1686711682372476488359901)
                ·
                  refine ⟨632516880889678683134963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1686711682372476488359901 632516880889678683134963)
                  ·
                    refine ⟨948775321334518024702445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632516880889678683134963 948775321334518024702445)
                    ·
                      refine ⟨355790745500444259263417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948775321334518024702445 355790745500444259263417)
                      ·
                        rfl

theorem cell23_692900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_692900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692900 prefixEnd_692900 := by exact prefixLift 692900
  have htrace : WordTrace (prefixWord ++ tailWord_692900) baseStart_692900 baseEnd_692900 := by
    simpa [prefixWord, tailWord_692900, baseEnd_692900] using wordTrace_append hprefix tailTrace_692900
  have hstable : (prefixWord ++ tailWord_692900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692900).length < 2 ^ (prefixWord ++ tailWord_692900).sum := by decide
  have hdescent : baseEnd_692900 < baseStart_692900 := by decide
  rcases family_descends (prefixWord ++ tailWord_692900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692917 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_692917 : Nat := 118140960795 + 692917 * 2 ^ 59
def prefixEnd_692917 : Nat := 4983230072969 + 3 ^ 40 * 692917 * 2
def baseEnd_692917 : Nat := 355799474671570692750839

theorem tailTrace_692917 : CollatzResearch.WordTrace tailWord_692917 prefixEnd_692917 355799474671570692750839 := by
  unfold tailWord_692917
  simp only [CollatzResearch.WordTrace]
  refine ⟨25272759230687524647117005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16848506153791683098078003 25272759230687524647117005)
  ·
    refine ⟨9477284711507821742668877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25272759230687524647117005 9477284711507821742668877)
    ·
      refine ⟨3553981766815433153500829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9477284711507821742668877 3553981766815433153500829)
      ·
        refine ⟨1332743162555787432562811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3553981766815433153500829 1332743162555787432562811)
        ·
          refine ⟨1999114743833681148844217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332743162555787432562811 1999114743833681148844217)
          ·
            refine ⟨1499336057875260861633163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999114743833681148844217 1499336057875260861633163)
            ·
              refine ⟨2249004086812891292449745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499336057875260861633163 2249004086812891292449745)
              ·
                refine ⟨1686753065109668469337309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249004086812891292449745 1686753065109668469337309)
                ·
                  refine ⟨632532399416125676001491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1686753065109668469337309 632532399416125676001491)
                  ·
                    refine ⟨948798599124188514002237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632532399416125676001491 948798599124188514002237)
                    ·
                      refine ⟨355799474671570692750839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948798599124188514002237 355799474671570692750839)
                      ·
                        rfl

theorem cell23_692917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_692917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692917 prefixEnd_692917 := by exact prefixLift 692917
  have htrace : WordTrace (prefixWord ++ tailWord_692917) baseStart_692917 baseEnd_692917 := by
    simpa [prefixWord, tailWord_692917, baseEnd_692917] using wordTrace_append hprefix tailTrace_692917
  have hstable : (prefixWord ++ tailWord_692917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692917).length < 2 ^ (prefixWord ++ tailWord_692917).sum := by decide
  have hdescent : baseEnd_692917 < baseStart_692917 := by decide
  rcases family_descends (prefixWord ++ tailWord_692917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692927 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 2, 3, 2]
def baseStart_692927 : Nat := 118140960795 + 692927 * 2 ^ 59
def prefixEnd_692927 : Nat := 4983230072969 + 3 ^ 40 * 692927 * 2
def baseEnd_692927 : Nat := 355804609478115653625793

theorem tailTrace_692927 : CollatzResearch.WordTrace tailWord_692927 prefixEnd_692927 355804609478115653625793 := by
  unfold tailWord_692927
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273123960651296354981035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16848749307100864236654023 25273123960651296354981035)
  ·
    refine ⟨37909685940976944532471553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25273123960651296354981035 37909685940976944532471553)
    ·
      refine ⟨28432264455732708399353665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37909685940976944532471553 28432264455732708399353665)
      ·
        refine ⟨21324198341799531299515249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28432264455732708399353665 21324198341799531299515249)
        ·
          refine ⟨15993148756349648474636437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21324198341799531299515249 15993148756349648474636437)
          ·
            refine ⟨749678847953889772248583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15993148756349648474636437 749678847953889772248583)
            ·
              refine ⟨1124518271930834658372875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749678847953889772248583 1124518271930834658372875)
              ·
                refine ⟨1686777407896251987559313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124518271930834658372875 1686777407896251987559313)
                ·
                  refine ⟨1265083055922188990669485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686777407896251987559313 1265083055922188990669485)
                  ·
                    refine ⟨474406145970820871501057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265083055922188990669485 474406145970820871501057)
                    ·
                      refine ⟨355804609478115653625793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474406145970820871501057 355804609478115653625793)
                      ·
                        rfl

theorem cell23_692927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_692927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_692927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_692927 prefixEnd_692927 := by exact prefixLift 692927
  have htrace : WordTrace (prefixWord ++ tailWord_692927) baseStart_692927 baseEnd_692927 := by
    simpa [prefixWord, tailWord_692927, baseEnd_692927] using wordTrace_append hprefix tailTrace_692927
  have hstable : (prefixWord ++ tailWord_692927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692927).length < 2 ^ (prefixWord ++ tailWord_692927).sum := by decide
  have hdescent : baseEnd_692927 < baseStart_692927 := by decide
  rcases family_descends (prefixWord ++ tailWord_692927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693013 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_693013 : Nat := 118140960795 + 693013 * 2 ^ 59
def prefixEnd_693013 : Nat := 4983230072969 + 3 ^ 40 * 693013 * 2
def baseEnd_693013 : Nat := 355848768814402317150397

theorem tailTrace_693013 : CollatzResearch.WordTrace tailWord_693013 prefixEnd_693013 355848768814402317150397 := by
  unfold tailWord_693013
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276260638339733042611693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16850840425559822028407795 25276260638339733042611693)
  ·
    refine ⟨9478597739377399890979385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25276260638339733042611693 9478597739377399890979385)
    ·
      refine ⟨7108948304533049918234539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9478597739377399890979385 7108948304533049918234539)
      ·
        refine ⟨10663422456799574877351809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108948304533049918234539 10663422456799574877351809)
        ·
          refine ⟨7997566842599681158013857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10663422456799574877351809 7997566842599681158013857)
          ·
            refine ⟨5998175131949760868510393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997566842599681158013857 5998175131949760868510393)
            ·
              refine ⟨4498631348962320651382795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998175131949760868510393 4498631348962320651382795)
              ·
                refine ⟨6747947023443480977074193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4498631348962320651382795 6747947023443480977074193)
                ·
                  refine ⟨5060960267582610732805645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6747947023443480977074193 5060960267582610732805645)
                  ·
                    refine ⟨1897860100343479024802117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5060960267582610732805645 1897860100343479024802117)
                    ·
                      refine ⟨355848768814402317150397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1897860100343479024802117 355848768814402317150397)
                      ·
                        rfl

theorem cell23_693013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_693013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693013 prefixEnd_693013 := by exact prefixLift 693013
  have htrace : WordTrace (prefixWord ++ tailWord_693013) baseStart_693013 baseEnd_693013 := by
    simpa [prefixWord, tailWord_693013, baseEnd_693013] using wordTrace_append hprefix tailTrace_693013
  have hstable : (prefixWord ++ tailWord_693013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693013).length < 2 ^ (prefixWord ++ tailWord_693013).sum := by decide
  have hdescent : baseEnd_693013 < baseStart_693013 := by decide
  rcases family_descends (prefixWord ++ tailWord_693013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693024 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3]
def baseStart_693024 : Nat := 118140960795 + 693024 * 2 ^ 59
def prefixEnd_693024 : Nat := 4983230072969 + 3 ^ 40 * 693024 * 2
def baseEnd_693024 : Nat := 355854417101601774112847

theorem tailTrace_693024 : CollatzResearch.WordTrace tailWord_693024 prefixEnd_693024 355854417101601774112847 := by
  unfold tailWord_693024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638330920649940960631063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16851107894199921280841417 12638330920649940960631063)
  ·
    refine ⟨18957496380974911440946595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12638330920649940960631063 18957496380974911440946595)
    ·
      refine ⟨28436244571462367161419893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957496380974911440946595 28436244571462367161419893)
      ·
        refine ⟨2665897928574596921383115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28436244571462367161419893 2665897928574596921383115)
        ·
          refine ⟨3998846892861895382074673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665897928574596921383115 3998846892861895382074673)
          ·
            refine ⟨2999135169646421536556005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998846892861895382074673 2999135169646421536556005)
            ·
              refine ⟨562337844308704038104251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2999135169646421536556005 562337844308704038104251)
              ·
                refine ⟨843506766463056057156377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562337844308704038104251 843506766463056057156377)
                ·
                  refine ⟨632630074847292042867283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843506766463056057156377 632630074847292042867283)
                  ·
                    refine ⟨948945112270938064300925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632630074847292042867283 948945112270938064300925)
                    ·
                      refine ⟨355854417101601774112847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948945112270938064300925 355854417101601774112847)
                      ·
                        rfl

theorem cell23_693024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_693024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693024 prefixEnd_693024 := by exact prefixLift 693024
  have htrace : WordTrace (prefixWord ++ tailWord_693024) baseStart_693024 baseEnd_693024 := by
    simpa [prefixWord, tailWord_693024, baseEnd_693024] using wordTrace_append hprefix tailTrace_693024
  have hstable : (prefixWord ++ tailWord_693024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693024).length < 2 ^ (prefixWord ++ tailWord_693024).sum := by decide
  have hdescent : baseEnd_693024 < baseStart_693024 := by decide
  rcases family_descends (prefixWord ++ tailWord_693024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_693033 : Nat := 118140960795 + 693033 * 2 ^ 59
def prefixEnd_693033 : Nat := 4983230072969 + 3 ^ 40 * 693033 * 2
def baseEnd_693033 : Nat := 355859038427492238900305

theorem tailTrace_693033 : CollatzResearch.WordTrace tailWord_693033 prefixEnd_693033 355859038427492238900305 := by
  unfold tailWord_693033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276990098267276458339753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16851326732178184305559835 25276990098267276458339753)
  ·
    refine ⟨18957742573700457343754815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25276990098267276458339753 18957742573700457343754815)
    ·
      refine ⟨28436613860550686015632223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957742573700457343754815 28436613860550686015632223)
      ·
        refine ⟨42654920790826029023448335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28436613860550686015632223 42654920790826029023448335)
        ·
          refine ⟨63982381186239043535172503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42654920790826029023448335 63982381186239043535172503)
          ·
            refine ⟨95973571779358565302758755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63982381186239043535172503 95973571779358565302758755)
            ·
              refine ⟨143960357669037847954138133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95973571779358565302758755 143960357669037847954138133)
              ·
                refine ⟨6748141765736149122850225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143960357669037847954138133 6748141765736149122850225)
                ·
                  refine ⟨5061106324302111842137669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6748141765736149122850225 5061106324302111842137669)
                  ·
                    refine ⟨948957435806645970400813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061106324302111842137669 948957435806645970400813)
                    ·
                      refine ⟨355859038427492238900305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 948957435806645970400813 355859038427492238900305)
                      ·
                        rfl

theorem cell23_693033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_693033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693033 prefixEnd_693033 := by exact prefixLift 693033
  have htrace : WordTrace (prefixWord ++ tailWord_693033) baseStart_693033 baseEnd_693033 := by
    simpa [prefixWord, tailWord_693033, baseEnd_693033] using wordTrace_append hprefix tailTrace_693033
  have hstable : (prefixWord ++ tailWord_693033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693033).length < 2 ^ (prefixWord ++ tailWord_693033).sum := by decide
  have hdescent : baseEnd_693033 < baseStart_693033 := by decide
  rcases family_descends (prefixWord ++ tailWord_693033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693064 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_693064 : Nat := 118140960795 + 693064 * 2 ^ 59
def prefixEnd_693064 : Nat := 4983230072969 + 3 ^ 40 * 693064 * 2
def baseEnd_693064 : Nat := 355874956327781617612663

theorem tailTrace_693064 : CollatzResearch.WordTrace tailWord_693064 prefixEnd_693064 355874956327781617612663 := by
  unfold tailWord_693064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639060380577484376359123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16852080507436645835145497 12639060380577484376359123)
  ·
    refine ⟨18958590570866226564538685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12639060380577484376359123 18958590570866226564538685)
    ·
      refine ⟨7109471464074834961702007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18958590570866226564538685 7109471464074834961702007)
      ·
        refine ⟨10664207196112252442553011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7109471464074834961702007 10664207196112252442553011)
        ·
          refine ⟨15996310794168378663829517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10664207196112252442553011 15996310794168378663829517)
          ·
            refine ⟨5998616547813141998936069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15996310794168378663829517 5998616547813141998936069)
            ·
              refine ⟨1124740602714964124800513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5998616547813141998936069 1124740602714964124800513)
              ·
                refine ⟨843555452036223093600385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124740602714964124800513 843555452036223093600385)
                ·
                  refine ⟨632666589027167320200289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843555452036223093600385 632666589027167320200289)
                  ·
                    refine ⟨474499941770375490150217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632666589027167320200289 474499941770375490150217)
                    ·
                      refine ⟨355874956327781617612663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474499941770375490150217 355874956327781617612663)
                      ·
                        rfl

theorem cell23_693064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_693064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693064 prefixEnd_693064 := by exact prefixLift 693064
  have htrace : WordTrace (prefixWord ++ tailWord_693064) baseStart_693064 baseEnd_693064 := by
    simpa [prefixWord, tailWord_693064, baseEnd_693064] using wordTrace_append hprefix tailTrace_693064
  have hstable : (prefixWord ++ tailWord_693064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693064).length < 2 ^ (prefixWord ++ tailWord_693064).sum := by decide
  have hdescent : baseEnd_693064 < baseStart_693064 := by decide
  rcases family_descends (prefixWord ++ tailWord_693064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693093 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_693093 : Nat := 118140960795 + 693093 * 2 ^ 59
def prefixEnd_693093 : Nat := 4983230072969 + 3 ^ 40 * 693093 * 2
def baseEnd_693093 : Nat := 355889847266762004150029

theorem tailTrace_693093 : CollatzResearch.WordTrace tailWord_693093 prefixEnd_693093 355889847266762004150029 := by
  unfold tailWord_693093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279178478049906705523933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16852785652033271137015955 25279178478049906705523933)
  ·
    refine ⟨9479691929268715014571475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25279178478049906705523933 9479691929268715014571475)
    ·
      refine ⟨14219537893903072521857213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479691929268715014571475 14219537893903072521857213)
      ·
        refine ⟨5332326710213652195696455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14219537893903072521857213 5332326710213652195696455)
        ·
          refine ⟨7998490065320478293544683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332326710213652195696455 7998490065320478293544683)
          ·
            refine ⟨11997735097980717440317025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998490065320478293544683 11997735097980717440317025)
            ·
              refine ⟨8998301323485538080237769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11997735097980717440317025 8998301323485538080237769)
              ·
                refine ⟨6748725992614153560178327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8998301323485538080237769 6748725992614153560178327)
                ·
                  refine ⟨10123088988921230340267491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748725992614153560178327 10123088988921230340267491)
                  ·
                    refine ⟨15184633483381845510401237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10123088988921230340267491 15184633483381845510401237)
                    ·
                      refine ⟨355889847266762004150029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15184633483381845510401237 355889847266762004150029)
                      ·
                        rfl

theorem cell23_693093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_693093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693093 prefixEnd_693093 := by exact prefixLift 693093
  have htrace : WordTrace (prefixWord ++ tailWord_693093) baseStart_693093 baseEnd_693093 := by
    simpa [prefixWord, tailWord_693093, baseEnd_693093] using wordTrace_append hprefix tailTrace_693093
  have hstable : (prefixWord ++ tailWord_693093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693093).length < 2 ^ (prefixWord ++ tailWord_693093).sum := by decide
  have hdescent : baseEnd_693093 < baseStart_693093 := by decide
  rcases family_descends (prefixWord ++ tailWord_693093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_693163 : Nat := 118140960795 + 693163 * 2 ^ 59
def prefixEnd_693163 : Nat := 4983230072969 + 3 ^ 40 * 693163 * 2
def baseEnd_693163 : Nat := 355925790912576730274707

theorem tailTrace_693163 : CollatzResearch.WordTrace tailWord_693163 prefixEnd_693163 355925790912576730274707 := by
  unfold tailWord_693163
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281731587796308660572143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16854487725197539107048095 25281731587796308660572143)
  ·
    refine ⟨37922597381694462990858215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25281731587796308660572143 37922597381694462990858215)
    ·
      refine ⟨56883896072541694486287323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37922597381694462990858215 56883896072541694486287323)
      ·
        refine ⟨85325844108812541729430985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56883896072541694486287323 85325844108812541729430985)
        ·
          refine ⟨63994383081609406297073239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85325844108812541729430985 63994383081609406297073239)
          ·
            refine ⟨95991574622414109445609859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63994383081609406297073239 95991574622414109445609859)
            ·
              refine ⟨143987361933621164168414789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95991574622414109445609859 143987361933621164168414789)
              ·
                refine ⟨26997630362553968281577773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143987361933621164168414789 26997630362553968281577773)
                ·
                  refine ⟨10124111385957738105591665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26997630362553968281577773 10124111385957738105591665)
                  ·
                    refine ⟨7593083539468303579193749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10124111385957738105591665 7593083539468303579193749)
                    ·
                      refine ⟨355925790912576730274707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7593083539468303579193749 355925790912576730274707)
                      ·
                        rfl

theorem cell23_693163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_693163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693163 prefixEnd_693163 := by exact prefixLift 693163
  have htrace : WordTrace (prefixWord ++ tailWord_693163) baseStart_693163 baseEnd_693163 := by
    simpa [prefixWord, tailWord_693163, baseEnd_693163] using wordTrace_append hprefix tailTrace_693163
  have hstable : (prefixWord ++ tailWord_693163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693163).length < 2 ^ (prefixWord ++ tailWord_693163).sum := by decide
  have hdescent : baseEnd_693163 < baseStart_693163 := by decide
  rcases family_descends (prefixWord ++ tailWord_693163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693181 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_693181 : Nat := 118140960795 + 693181 * 2 ^ 59
def prefixEnd_693181 : Nat := 4983230072969 + 3 ^ 40 * 693181 * 2
def baseEnd_693181 : Nat := 118645011188119219949875

theorem tailTrace_693181 : CollatzResearch.WordTrace tailWord_693181 prefixEnd_693181 118645011188119219949875 := by
  unfold tailWord_693181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282388101731097734727397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16854925401154065156484931 25282388101731097734727397)
  ·
    refine ⟨4740447769074580825261387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25282388101731097734727397 4740447769074580825261387)
    ·
      refine ⟨7110671653611871237892081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740447769074580825261387 7110671653611871237892081)
      ·
        refine ⟨5333003740208903428419061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110671653611871237892081 5333003740208903428419061)
        ·
          refine ⟨499969100644584696414287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5333003740208903428419061 499969100644584696414287)
          ·
            refine ⟨749953650966877044621431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499969100644584696414287 749953650966877044621431)
            ·
              refine ⟨1124930476450315566932147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749953650966877044621431 1124930476450315566932147)
              ·
                refine ⟨1687395714675473350398221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124930476450315566932147 1687395714675473350398221)
                ·
                  refine ⟨632773393003302506399333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1687395714675473350398221 632773393003302506399333)
                  ·
                    refine ⟨118645011188119219949875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632773393003302506399333 118645011188119219949875)
                    ·
                      rfl

theorem cell23_693181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_693181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693181 prefixEnd_693181 := by exact prefixLift 693181
  have htrace : WordTrace (prefixWord ++ tailWord_693181) baseStart_693181 baseEnd_693181 := by
    simpa [prefixWord, tailWord_693181, baseEnd_693181] using wordTrace_append hprefix tailTrace_693181
  have hstable : (prefixWord ++ tailWord_693181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693181).length < 2 ^ (prefixWord ++ tailWord_693181).sum := by decide
  have hdescent : baseEnd_693181 < baseStart_693181 := by decide
  rcases family_descends (prefixWord ++ tailWord_693181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693238 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_693238 : Nat := 118140960795 + 693238 * 2 ^ 59
def prefixEnd_693238 : Nat := 4983230072969 + 3 ^ 40 * 693238 * 2
def baseEnd_693238 : Nat := 355964301961663936836863

theorem tailTrace_693238 : CollatzResearch.WordTrace tailWord_693238 prefixEnd_693238 355964301961663936836863 := by
  unfold tailWord_693238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580279191407787279347023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16856311375016397646368245 1580279191407787279347023)
  ·
    refine ⟨2370418787111680919020535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1580279191407787279347023 2370418787111680919020535)
    ·
      refine ⟨3555628180667521378530803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370418787111680919020535 3555628180667521378530803)
      ·
        refine ⟨5333442271001282067796205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555628180667521378530803 5333442271001282067796205)
        ·
          refine ⟨2000040851625480775423577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5333442271001282067796205 2000040851625480775423577)
          ·
            refine ⟨1500030638719110581567683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000040851625480775423577 1500030638719110581567683)
            ·
              refine ⟨2250045958078665872351525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500030638719110581567683 2250045958078665872351525)
              ·
                refine ⟨421883617139749851065911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2250045958078665872351525 421883617139749851065911)
                ·
                  refine ⟨632825425709624776598867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421883617139749851065911 632825425709624776598867)
                  ·
                    refine ⟨949238138564437164898301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632825425709624776598867 949238138564437164898301)
                    ·
                      refine ⟨355964301961663936836863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 949238138564437164898301 355964301961663936836863)
                      ·
                        rfl

theorem cell23_693238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_693238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693238 prefixEnd_693238 := by exact prefixLift 693238
  have htrace : WordTrace (prefixWord ++ tailWord_693238) baseStart_693238 baseEnd_693238 := by
    simpa [prefixWord, tailWord_693238, baseEnd_693238] using wordTrace_append hprefix tailTrace_693238
  have hstable : (prefixWord ++ tailWord_693238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693238).length < 2 ^ (prefixWord ++ tailWord_693238).sum := by decide
  have hdescent : baseEnd_693238 < baseStart_693238 := by decide
  rcases family_descends (prefixWord ++ tailWord_693238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693240 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_693240 : Nat := 118140960795 + 693240 * 2 ^ 59
def prefixEnd_693240 : Nat := 4983230072969 + 3 ^ 40 * 693240 * 2
def baseEnd_693240 : Nat := 355965328922972929011853

theorem tailTrace_693240 : CollatzResearch.WordTrace tailWord_693240 prefixEnd_693240 355965328922972929011853 := by
  unfold tailWord_693240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642270004258675405562587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16856360005678233874083449 12642270004258675405562587)
  ·
    refine ⟨18963405006388013108343881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12642270004258675405562587 18963405006388013108343881)
    ·
      refine ⟨14222553754791009831257911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18963405006388013108343881 14222553754791009831257911)
      ·
        refine ⟨21333830632186514746886867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222553754791009831257911 21333830632186514746886867)
        ·
          refine ⟨32000745948279772120330301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21333830632186514746886867 32000745948279772120330301)
          ·
            refine ⟨12000279730604914545123863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32000745948279772120330301 12000279730604914545123863)
            ·
              refine ⟨18000419595907371817685795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12000279730604914545123863 18000419595907371817685795)
              ·
                refine ⟨27000629393861057726528693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18000419595907371817685795 27000629393861057726528693)
                ·
                  refine ⟨2531309005674474161862065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27000629393861057726528693 2531309005674474161862065)
                  ·
                    refine ⟨1898481754255855621396549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531309005674474161862065 1898481754255855621396549)
                    ·
                      refine ⟨355965328922972929011853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1898481754255855621396549 355965328922972929011853)
                      ·
                        rfl

theorem cell23_693240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_693240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693240 prefixEnd_693240 := by exact prefixLift 693240
  have htrace : WordTrace (prefixWord ++ tailWord_693240) baseStart_693240 baseEnd_693240 := by
    simpa [prefixWord, tailWord_693240, baseEnd_693240] using wordTrace_append hprefix tailTrace_693240
  have hstable : (prefixWord ++ tailWord_693240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693240).length < 2 ^ (prefixWord ++ tailWord_693240).sum := by decide
  have hdescent : baseEnd_693240 < baseStart_693240 := by decide
  rcases family_descends (prefixWord ++ tailWord_693240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693281 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_693281 : Nat := 118140960795 + 693281 * 2 ^ 59
def prefixEnd_693281 : Nat := 4983230072969 + 3 ^ 40 * 693281 * 2
def baseEnd_693281 : Nat := 355986381629807268599165

theorem tailTrace_693281 : CollatzResearch.WordTrace tailWord_693281 prefixEnd_693281 355986381629807268599165 := by
  unfold tailWord_693281
  simp only [CollatzResearch.WordTrace]
  refine ⟨25286035401368814813367697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16857356934245876542245131 25286035401368814813367697)
  ·
    refine ⟨18964526551026611110025773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25286035401368814813367697 18964526551026611110025773)
    ·
      refine ⟨7111697456634979166259665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18964526551026611110025773 7111697456634979166259665)
      ·
        refine ⟨5333773092476234374694749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7111697456634979166259665 5333773092476234374694749)
        ·
          refine ⟨2000164909678587890510531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5333773092476234374694749 2000164909678587890510531)
          ·
            refine ⟨3000247364517881835765797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000164909678587890510531 3000247364517881835765797)
            ·
              refine ⟨562546380847102844206087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3000247364517881835765797 562546380847102844206087)
              ·
                refine ⟨843819571270654266309131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562546380847102844206087 843819571270654266309131)
                ·
                  refine ⟨1265729356905981399463697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843819571270654266309131 1265729356905981399463697)
                  ·
                    refine ⟨949297017679486049597773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1265729356905981399463697 949297017679486049597773)
                    ·
                      refine ⟨355986381629807268599165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 949297017679486049597773 355986381629807268599165)
                      ·
                        rfl

theorem cell23_693281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_693281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693281 prefixEnd_693281 := by exact prefixLift 693281
  have htrace : WordTrace (prefixWord ++ tailWord_693281) baseStart_693281 baseEnd_693281 := by
    simpa [prefixWord, tailWord_693281, baseEnd_693281] using wordTrace_append hprefix tailTrace_693281
  have hstable : (prefixWord ++ tailWord_693281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693281).length < 2 ^ (prefixWord ++ tailWord_693281).sum := by decide
  have hdescent : baseEnd_693281 < baseStart_693281 := by decide
  rcases family_descends (prefixWord ++ tailWord_693281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693351 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_693351 : Nat := 118140960795 + 693351 * 2 ^ 59
def prefixEnd_693351 : Nat := 4983230072969 + 3 ^ 40 * 693351 * 2
def baseEnd_693351 : Nat := 356022325275621994723843

theorem tailTrace_693351 : CollatzResearch.WordTrace tailWord_693351 prefixEnd_693351 356022325275621994723843 := by
  unfold tailWord_693351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25288588511115216768415907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16859059007410144512277271 25288588511115216768415907)
  ·
    refine ⟨37932882766672825152623861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25288588511115216768415907 37932882766672825152623861)
    ·
      refine ⟨3556207759375577358058487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37932882766672825152623861 3556207759375577358058487)
      ·
        refine ⟨5334311639063366037087731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556207759375577358058487 5334311639063366037087731)
        ·
          refine ⟨8001467458595049055631597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334311639063366037087731 8001467458595049055631597)
          ·
            refine ⟨3000550296973143395861849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8001467458595049055631597 3000550296973143395861849)
            ·
              refine ⟨2250412722729857546896387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000550296973143395861849 2250412722729857546896387)
              ·
                refine ⟨3375619084094786320344581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250412722729857546896387 3375619084094786320344581)
                ·
                  refine ⟨632928578267772435064609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3375619084094786320344581 632928578267772435064609)
                  ·
                    refine ⟨474696433700829326298457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632928578267772435064609 474696433700829326298457)
                    ·
                      refine ⟨356022325275621994723843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474696433700829326298457 356022325275621994723843)
                      ·
                        rfl

theorem cell23_693351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_693351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693351 prefixEnd_693351 := by exact prefixLift 693351
  have htrace : WordTrace (prefixWord ++ tailWord_693351) baseStart_693351 baseEnd_693351 := by
    simpa [prefixWord, tailWord_693351, baseEnd_693351] using wordTrace_append hprefix tailTrace_693351
  have hstable : (prefixWord ++ tailWord_693351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693351).length < 2 ^ (prefixWord ++ tailWord_693351).sum := by decide
  have hdescent : baseEnd_693351 < baseStart_693351 := by decide
  rcases family_descends (prefixWord ++ tailWord_693351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693367 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_693367 : Nat := 118140960795 + 693367 * 2 ^ 59
def prefixEnd_693367 : Nat := 4983230072969 + 3 ^ 40 * 693367 * 2
def baseEnd_693367 : Nat := 356030540966093932123769

theorem tailTrace_693367 : CollatzResearch.WordTrace tailWord_693367 prefixEnd_693367 356030540966093932123769 := by
  unfold tailWord_693367
  simp only [CollatzResearch.WordTrace]
  refine ⟨25289172079057251500998355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16859448052704834333998903 25289172079057251500998355)
  ·
    refine ⟨37933758118585877251497533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25289172079057251500998355 37933758118585877251497533)
    ·
      refine ⟨14225159294469703969311575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37933758118585877251497533 14225159294469703969311575)
      ·
        refine ⟨21337738941704555953967363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14225159294469703969311575 21337738941704555953967363)
        ·
          refine ⟨32006608412556833930951045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21337738941704555953967363 32006608412556833930951045)
          ·
            refine ⟨6001239077354406362053321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32006608412556833930951045 6001239077354406362053321)
            ·
              refine ⟨4500929308015804771539991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001239077354406362053321 4500929308015804771539991)
              ·
                refine ⟨6751393962023707157309987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500929308015804771539991 6751393962023707157309987)
                ·
                  refine ⟨10127090943035560735964981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751393962023707157309987 10127090943035560735964981)
                  ·
                    refine ⟨949414775909583818996717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10127090943035560735964981 949414775909583818996717)
                    ·
                      refine ⟨356030540966093932123769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 949414775909583818996717 356030540966093932123769)
                      ·
                        rfl

theorem cell23_693367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_693367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693367 prefixEnd_693367 := by exact prefixLift 693367
  have htrace : WordTrace (prefixWord ++ tailWord_693367) baseStart_693367 baseEnd_693367 := by
    simpa [prefixWord, tailWord_693367, baseEnd_693367] using wordTrace_append hprefix tailTrace_693367
  have hstable : (prefixWord ++ tailWord_693367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693367).length < 2 ^ (prefixWord ++ tailWord_693367).sum := by decide
  have hdescent : baseEnd_693367 < baseStart_693367 := by decide
  rcases family_descends (prefixWord ++ tailWord_693367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693368 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_693368 : Nat := 118140960795 + 693368 * 2 ^ 59
def prefixEnd_693368 : Nat := 4983230072969 + 3 ^ 40 * 693368 * 2
def baseEnd_693368 : Nat := 356031054446748428211265

theorem tailTrace_693368 : CollatzResearch.WordTrace tailWord_693368 prefixEnd_693368 356031054446748428211265 := by
  unfold tailWord_693368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644604276026814335892379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16859472368035752447856505 12644604276026814335892379)
  ·
    refine ⟨18966906414040221503838569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12644604276026814335892379 18966906414040221503838569)
    ·
      refine ⟨14225179810530166127878927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18966906414040221503838569 14225179810530166127878927)
      ·
        refine ⟨21337769715795249191818391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14225179810530166127878927 21337769715795249191818391)
        ·
          refine ⟨32006654573692873787727587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21337769715795249191818391 32006654573692873787727587)
          ·
            refine ⟨48009981860539310681591381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32006654573692873787727587 48009981860539310681591381)
            ·
              refine ⟨562616974928195047049899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 48009981860539310681591381 562616974928195047049899)
              ·
                refine ⟨843925462392292570574849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562616974928195047049899 843925462392292570574849)
                ·
                  refine ⟨632944096794219427931137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843925462392292570574849 632944096794219427931137)
                  ·
                    refine ⟨474708072595664570948353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632944096794219427931137 474708072595664570948353)
                    ·
                      refine ⟨356031054446748428211265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474708072595664570948353 356031054446748428211265)
                      ·
                        rfl

theorem cell23_693368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_693368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693368 prefixEnd_693368 := by exact prefixLift 693368
  have htrace : WordTrace (prefixWord ++ tailWord_693368) baseStart_693368 baseEnd_693368 := by
    simpa [prefixWord, tailWord_693368, baseEnd_693368] using wordTrace_append hprefix tailTrace_693368
  have hstable : (prefixWord ++ tailWord_693368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693368).length < 2 ^ (prefixWord ++ tailWord_693368).sum := by decide
  have hdescent : baseEnd_693368 < baseStart_693368 := by decide
  rcases family_descends (prefixWord ++ tailWord_693368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693404 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_693404 : Nat := 118140960795 + 693404 * 2 ^ 59
def prefixEnd_693404 : Nat := 4983230072969 + 3 ^ 40 * 693404 * 2
def baseEnd_693404 : Nat := 118683179916770095787033

theorem tailTrace_693404 : CollatzResearch.WordTrace tailWord_693404 prefixEnd_693404 118683179916770095787033 := by
  unfold tailWord_693404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645260789961603410047633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16860347719948804546730177 12645260789961603410047633)
  ·
    refine ⟨9483945592471202557535725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12645260789961603410047633 9483945592471202557535725)
    ·
      refine ⟨3556479597176700959075897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9483945592471202557535725 3556479597176700959075897)
      ·
        refine ⟨2667359697882525719306923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556479597176700959075897 2667359697882525719306923)
        ·
          refine ⟨4001039546823788578960385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667359697882525719306923 4001039546823788578960385)
          ·
            refine ⟨3000779660117841434220289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001039546823788578960385 3000779660117841434220289)
            ·
              refine ⟨2250584745088381075665217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000779660117841434220289 2250584745088381075665217)
              ·
                refine ⟨1687938558816285806748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250584745088381075665217 1687938558816285806748913)
                ·
                  refine ⟨1265953919112214355061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687938558816285806748913 1265953919112214355061685)
                  ·
                    refine ⟨118683179916770095787033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1265953919112214355061685 118683179916770095787033)
                    ·
                      rfl

theorem cell23_693404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_693404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693404 prefixEnd_693404 := by exact prefixLift 693404
  have htrace : WordTrace (prefixWord ++ tailWord_693404) baseStart_693404 baseEnd_693404 := by
    simpa [prefixWord, tailWord_693404, baseEnd_693404] using wordTrace_append hprefix tailTrace_693404
  have hstable : (prefixWord ++ tailWord_693404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693404).length < 2 ^ (prefixWord ++ tailWord_693404).sum := by decide
  have hdescent : baseEnd_693404 < baseStart_693404 := by decide
  rcases family_descends (prefixWord ++ tailWord_693404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693424 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2]
def baseStart_693424 : Nat := 118140960795 + 693424 * 2 ^ 59
def prefixEnd_693424 : Nat := 4983230072969 + 3 ^ 40 * 693424 * 2
def baseEnd_693424 : Nat := 356059809363400209111007

theorem tailTrace_693424 : CollatzResearch.WordTrace tailWord_693424 prefixEnd_693424 356059809363400209111007 := by
  unfold tailWord_693424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645625519925375117911663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16860834026567166823882217 12645625519925375117911663)
  ·
    refine ⟨18968438279888062676867495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12645625519925375117911663 18968438279888062676867495)
    ·
      refine ⟨28452657419832094015301243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18968438279888062676867495 28452657419832094015301243)
      ·
        refine ⟨42678986129748141022951865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28452657419832094015301243 42678986129748141022951865)
        ·
          refine ⟨32009239597311105767213899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42678986129748141022951865 32009239597311105767213899)
          ·
            refine ⟨48013859395966658650820849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32009239597311105767213899 48013859395966658650820849)
            ·
              refine ⟨36010394546974993988115637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48013859395966658650820849 36010394546974993988115637)
              ·
                refine ⟨3375974488778905686385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36010394546974993988115637 3375974488778905686385841)
                ·
                  refine ⟨2531980866584179264789381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375974488778905686385841 2531980866584179264789381)
                  ·
                    refine ⟨474746412484533612148009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531980866584179264789381 474746412484533612148009)
                    ·
                      refine ⟨356059809363400209111007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474746412484533612148009 356059809363400209111007)
                      ·
                        rfl

theorem cell23_693424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2].length) (baseStart_693424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693424 prefixEnd_693424 := by exact prefixLift 693424
  have htrace : WordTrace (prefixWord ++ tailWord_693424) baseStart_693424 baseEnd_693424 := by
    simpa [prefixWord, tailWord_693424, baseEnd_693424] using wordTrace_append hprefix tailTrace_693424
  have hstable : (prefixWord ++ tailWord_693424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693424).length < 2 ^ (prefixWord ++ tailWord_693424).sum := by decide
  have hdescent : baseEnd_693424 < baseStart_693424 := by decide
  rcases family_descends (prefixWord ++ tailWord_693424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693441 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_693441 : Nat := 118140960795 + 693441 * 2 ^ 59
def prefixEnd_693441 : Nat := 4983230072969 + 3 ^ 40 * 693441 * 2
def baseEnd_693441 : Nat := 356068538534526642598429

theorem tailTrace_693441 : CollatzResearch.WordTrace tailWord_693441 prefixEnd_693441 356068538534526642598429 := by
  unfold tailWord_693441
  simp only [CollatzResearch.WordTrace]
  refine ⟨25291871080789162139192177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16861247387192774759461451 25291871080789162139192177)
  ·
    refine ⟨18968903310591871604394133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25291871080789162139192177 18968903310591871604394133)
    ·
      refine ⟨889167342683993981455975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18968903310591871604394133 889167342683993981455975)
      ·
        refine ⟨1333751014025990972183963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889167342683993981455975 1333751014025990972183963)
        ·
          refine ⟨2000626521038986458275945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333751014025990972183963 2000626521038986458275945)
          ·
            refine ⟨1500469890779239843706959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000626521038986458275945 1500469890779239843706959)
            ·
              refine ⟨2250704836168859765560439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500469890779239843706959 2250704836168859765560439)
              ·
                refine ⟨3376057254253289648340659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250704836168859765560439 3376057254253289648340659)
                ·
                  refine ⟨5064085881379934472510989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376057254253289648340659 5064085881379934472510989)
                  ·
                    refine ⟨1899032205517475427191621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5064085881379934472510989 1899032205517475427191621)
                    ·
                      refine ⟨356068538534526642598429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1899032205517475427191621 356068538534526642598429)
                      ·
                        rfl

theorem cell23_693441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_693441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693441 prefixEnd_693441 := by exact prefixLift 693441
  have htrace : WordTrace (prefixWord ++ tailWord_693441) baseStart_693441 baseEnd_693441 := by
    simpa [prefixWord, tailWord_693441, baseEnd_693441] using wordTrace_append hprefix tailTrace_693441
  have hstable : (prefixWord ++ tailWord_693441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693441).length < 2 ^ (prefixWord ++ tailWord_693441).sum := by decide
  have hdescent : baseEnd_693441 < baseStart_693441 := by decide
  rcases family_descends (prefixWord ++ tailWord_693441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693464 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 8]
def baseStart_693464 : Nat := 118140960795 + 693464 * 2 ^ 59
def prefixEnd_693464 : Nat := 4983230072969 + 3 ^ 40 * 693464 * 2
def baseEnd_693464 : Nat := 39564483176620005845647

theorem tailTrace_693464 : CollatzResearch.WordTrace tailWord_693464 prefixEnd_693464 39564483176620005845647 := by
  unfold tailWord_693464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646354979852918533639723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16861806639803891378186297 12646354979852918533639723)
  ·
    refine ⟨18969532469779377800459585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12646354979852918533639723 18969532469779377800459585)
    ·
      refine ⟨14227149352334533350344689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18969532469779377800459585 14227149352334533350344689)
      ·
        refine ⟨10670362014250900012758517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14227149352334533350344689 10670362014250900012758517)
        ·
          refine ⟨1000346438836021876196111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10670362014250900012758517 1000346438836021876196111)
          ·
            refine ⟨1500519658254032814294167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000346438836021876196111 1500519658254032814294167)
            ·
              refine ⟨2250779487381049221441251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500519658254032814294167 2250779487381049221441251)
              ·
                refine ⟨3376169231071573832161877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250779487381049221441251 3376169231071573832161877)
                ·
                  refine ⟨39564483176620005845647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3376169231071573832161877 39564483176620005845647)
                  ·
                    rfl

theorem cell23_693464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_693464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693464 prefixEnd_693464 := by exact prefixLift 693464
  have htrace : WordTrace (prefixWord ++ tailWord_693464) baseStart_693464 baseEnd_693464 := by
    simpa [prefixWord, tailWord_693464, baseEnd_693464] using wordTrace_append hprefix tailTrace_693464
  have hstable : (prefixWord ++ tailWord_693464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693464).length < 2 ^ (prefixWord ++ tailWord_693464).sum := by decide
  have hdescent : baseEnd_693464 < baseStart_693464 := by decide
  rcases family_descends (prefixWord ++ tailWord_693464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693491 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 3]
def baseStart_693491 : Nat := 118140960795 + 693491 * 2 ^ 59
def prefixEnd_693491 : Nat := 4983230072969 + 3 ^ 40 * 693491 * 2
def baseEnd_693491 : Nat := 356094212567251446973199

theorem tailTrace_693491 : CollatzResearch.WordTrace tailWord_693491 prefixEnd_693491 356094212567251446973199 := by
  unfold tailWord_693491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293694730608020678512327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16862463153738680452341551 25293694730608020678512327)
  ·
    refine ⟨37940542095912031017768491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25293694730608020678512327 37940542095912031017768491)
    ·
      refine ⟨56910813143868046526652737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37940542095912031017768491 56910813143868046526652737)
      ·
        refine ⟨42683109857901034894989553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56910813143868046526652737 42683109857901034894989553)
        ·
          refine ⟨32012332393425776171242165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42683109857901034894989553 32012332393425776171242165)
          ·
            refine ⟨3001156161883666516053953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32012332393425776171242165 3001156161883666516053953)
            ·
              refine ⟨2250867121412749887040465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001156161883666516053953 2250867121412749887040465)
              ·
                refine ⟨1688150341059562415280349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250867121412749887040465 1688150341059562415280349)
                ·
                  refine ⟨633056377897335905730131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1688150341059562415280349 633056377897335905730131)
                  ·
                    refine ⟨949584566846003858595197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 633056377897335905730131 949584566846003858595197)
                    ·
                      refine ⟨356094212567251446973199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 949584566846003858595197 356094212567251446973199)
                      ·
                        rfl

theorem cell23_693491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_693491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693491 prefixEnd_693491 := by exact prefixLift 693491
  have htrace : WordTrace (prefixWord ++ tailWord_693491) baseStart_693491 baseEnd_693491 := by
    simpa [prefixWord, tailWord_693491, baseEnd_693491] using wordTrace_append hprefix tailTrace_693491
  have hstable : (prefixWord ++ tailWord_693491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693491).length < 2 ^ (prefixWord ++ tailWord_693491).sum := by decide
  have hdescent : baseEnd_693491 < baseStart_693491 := by decide
  rcases family_descends (prefixWord ++ tailWord_693491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693514 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_693514 : Nat := 118140960795 + 693514 * 2 ^ 59
def prefixEnd_693514 : Nat := 4983230072969 + 3 ^ 40 * 693514 * 2
def baseEnd_693514 : Nat := 356106022622304856985593

theorem tailTrace_693514 : CollatzResearch.WordTrace tailWord_693514 prefixEnd_693514 356106022622304856985593 := by
  unfold tailWord_693514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323633402381173901649899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16863022406349797071066397 6323633402381173901649899)
  ·
    refine ⟨9485450103571760852474849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323633402381173901649899 9485450103571760852474849)
    ·
      refine ⟨7114087577678820639356137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9485450103571760852474849 7114087577678820639356137)
      ·
        refine ⟨5335565683259115479517103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7114087577678820639356137 5335565683259115479517103)
        ·
          refine ⟨8003348524888673219275655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335565683259115479517103 8003348524888673219275655)
          ·
            refine ⟨12005022787333009828913483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003348524888673219275655 12005022787333009828913483)
            ·
              refine ⟨18007534180999514743370225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005022787333009828913483 18007534180999514743370225)
              ·
                refine ⟨13505650635749636057527669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18007534180999514743370225 13505650635749636057527669)
                ·
                  refine ⟨1266154747101528380393219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13505650635749636057527669 1266154747101528380393219)
                  ·
                    refine ⟨1899232120652292570589829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266154747101528380393219 1899232120652292570589829)
                    ·
                      refine ⟨356106022622304856985593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1899232120652292570589829 356106022622304856985593)
                      ·
                        rfl

theorem cell23_693514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_693514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693514 prefixEnd_693514 := by exact prefixLift 693514
  have htrace : WordTrace (prefixWord ++ tailWord_693514) baseStart_693514 baseEnd_693514 := by
    simpa [prefixWord, tailWord_693514, baseEnd_693514] using wordTrace_append hprefix tailTrace_693514
  have hstable : (prefixWord ++ tailWord_693514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693514).length < 2 ^ (prefixWord ++ tailWord_693514).sum := by decide
  have hdescent : baseEnd_693514 < baseStart_693514 := by decide
  rcases family_descends (prefixWord ++ tailWord_693514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693518 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_693518 : Nat := 118140960795 + 693518 * 2 ^ 59
def prefixEnd_693518 : Nat := 4983230072969 + 3 ^ 40 * 693518 * 2
def baseEnd_693518 : Nat := 356108076544922841335575

theorem tailTrace_693518 : CollatzResearch.WordTrace tailWord_693518 prefixEnd_693518 356108076544922841335575 := by
  unfold tailWord_693518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161834937688775536218151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16863119667673469526496805 3161834937688775536218151)
  ·
    refine ⟨4742752406533163304327227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3161834937688775536218151 4742752406533163304327227)
    ·
      refine ⟨7114128609799744956490841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4742752406533163304327227 7114128609799744956490841)
      ·
        refine ⟨5335596457349808717368131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7114128609799744956490841 5335596457349808717368131)
        ·
          refine ⟨8003394686024713076052197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335596457349808717368131 8003394686024713076052197)
          ·
            refine ⟨1500636503629633701759787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8003394686024713076052197 1500636503629633701759787)
            ·
              refine ⟨2250954755444450552639681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500636503629633701759787 2250954755444450552639681)
              ·
                refine ⟨1688216066583337914479761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250954755444450552639681 1688216066583337914479761)
                ·
                  refine ⟨1266162049937503435859821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688216066583337914479761 1266162049937503435859821)
                  ·
                    refine ⟨474810768726563788447433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266162049937503435859821 474810768726563788447433)
                    ·
                      refine ⟨356108076544922841335575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474810768726563788447433 356108076544922841335575)
                      ·
                        rfl

theorem cell23_693518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_693518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693518 prefixEnd_693518 := by exact prefixLift 693518
  have htrace : WordTrace (prefixWord ++ tailWord_693518) baseStart_693518 baseEnd_693518 := by
    simpa [prefixWord, tailWord_693518, baseEnd_693518] using wordTrace_append hprefix tailTrace_693518
  have hstable : (prefixWord ++ tailWord_693518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693518).length < 2 ^ (prefixWord ++ tailWord_693518).sum := by decide
  have hdescent : baseEnd_693518 < baseStart_693518 := by decide
  rcases family_descends (prefixWord ++ tailWord_693518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693547 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_693547 : Nat := 118140960795 + 693547 * 2 ^ 59
def prefixEnd_693547 : Nat := 4983230072969 + 3 ^ 40 * 693547 * 2
def baseEnd_693547 : Nat := 356122967483903227872941

theorem tailTrace_693547 : CollatzResearch.WordTrace tailWord_693547 prefixEnd_693547 356122967483903227872941 := by
  unfold tailWord_693547
  simp only [CollatzResearch.WordTrace]
  refine ⟨25295737218405142242550895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16863824812270094828367263 25295737218405142242550895)
  ·
    refine ⟨37943605827607713363826343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25295737218405142242550895 37943605827607713363826343)
    ·
      refine ⟨56915408741411570045739515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37943605827607713363826343 56915408741411570045739515)
      ·
        refine ⟨85373113112117355068609273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56915408741411570045739515 85373113112117355068609273)
        ·
          refine ⟨64029834834088016301456955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85373113112117355068609273 64029834834088016301456955)
          ·
            refine ⟨96044752251132024452185433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64029834834088016301456955 96044752251132024452185433)
            ·
              refine ⟨72033564188349018339139075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96044752251132024452185433 72033564188349018339139075)
              ·
                refine ⟨108050346282523527508708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72033564188349018339139075 108050346282523527508708613)
                ·
                  refine ⟨20259439927973161407882865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108050346282523527508708613 20259439927973161407882865)
                  ·
                    refine ⟨15194579945979871055912149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20259439927973161407882865 15194579945979871055912149)
                    ·
                      refine ⟨356122967483903227872941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15194579945979871055912149 356122967483903227872941)
                      ·
                        rfl

theorem cell23_693547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_693547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693547 prefixEnd_693547 := by exact prefixLift 693547
  have htrace : WordTrace (prefixWord ++ tailWord_693547) baseStart_693547 baseEnd_693547 := by
    simpa [prefixWord, tailWord_693547, baseEnd_693547] using wordTrace_append hprefix tailTrace_693547
  have hstable : (prefixWord ++ tailWord_693547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693547).length < 2 ^ (prefixWord ++ tailWord_693547).sum := by decide
  have hdescent : baseEnd_693547 < baseStart_693547 := by decide
  rcases family_descends (prefixWord ++ tailWord_693547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693554 : List Nat := [3, 2, 1, 1, 4, 1, 2, 9]
def baseStart_693554 : Nat := 118140960795 + 693554 * 2 ^ 59
def prefixEnd_693554 : Nat := 4983230072969 + 3 ^ 40 * 693554 * 2
def baseEnd_693554 : Nat := 13189872661054988906867

theorem tailTrace_693554 : CollatzResearch.WordTrace tailWord_693554 prefixEnd_693554 13189872661054988906867 := by
  unfold tailWord_693554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323998132344945609513929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16863995019586521625370477 6323998132344945609513929)
  ·
    refine ⟨4742998599258709207135447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6323998132344945609513929 4742998599258709207135447)
    ·
      refine ⟨7114497898888063810703171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4742998599258709207135447 7114497898888063810703171)
      ·
        refine ⟨10671746848332095716054757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114497898888063810703171 10671746848332095716054757)
        ·
          refine ⟨2000952534062267946760267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10671746848332095716054757 2000952534062267946760267)
          ·
            refine ⟨3001428801093401920140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000952534062267946760267 3001428801093401920140401)
            ·
              refine ⟨2251071600820051440105301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001428801093401920140401 2251071600820051440105301)
              ·
                refine ⟨13189872661054988906867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2251071600820051440105301 13189872661054988906867)
                ·
                  rfl

theorem cell23_693554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_693554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693554 prefixEnd_693554 := by exact prefixLift 693554
  have htrace : WordTrace (prefixWord ++ tailWord_693554) baseStart_693554 baseEnd_693554 := by
    simpa [prefixWord, tailWord_693554, baseEnd_693554] using wordTrace_append hprefix tailTrace_693554
  have hstable : (prefixWord ++ tailWord_693554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693554).length < 2 ^ (prefixWord ++ tailWord_693554).sum := by decide
  have hdescent : baseEnd_693554 < baseStart_693554 := by decide
  rcases family_descends (prefixWord ++ tailWord_693554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693568 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3]
def baseStart_693568 : Nat := 118140960795 + 693568 * 2 ^ 59
def prefixEnd_693568 : Nat := 4983230072969 + 3 ^ 40 * 693568 * 2
def baseEnd_693568 : Nat := 356133750577647645710345

theorem tailTrace_693568 : CollatzResearch.WordTrace tailWord_693568 prefixEnd_693568 356133750577647645710345 := by
  unfold tailWord_693568
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648251575664531414532679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16864335434219375219376905 12648251575664531414532679)
  ·
    refine ⟨18972377363496797121799019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12648251575664531414532679 18972377363496797121799019)
    ·
      refine ⟨28458566045245195682698529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18972377363496797121799019 28458566045245195682698529)
      ·
        refine ⟨21343924533933896762023897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28458566045245195682698529 21343924533933896762023897)
        ·
          refine ⟨16007943400450422571517923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21343924533933896762023897 16007943400450422571517923)
          ·
            refine ⟨24011915100675633857276885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16007943400450422571517923 24011915100675633857276885)
            ·
              refine ⟨562779260172085168529927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24011915100675633857276885 562779260172085168529927)
              ·
                refine ⟨844168890258127752794891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562779260172085168529927 844168890258127752794891)
                ·
                  refine ⟨1266253335387191629192337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844168890258127752794891 1266253335387191629192337)
                  ·
                    refine ⟨949690001540393721894253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266253335387191629192337 949690001540393721894253)
                    ·
                      refine ⟨356133750577647645710345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 949690001540393721894253 356133750577647645710345)
                      ·
                        rfl

theorem cell23_693568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_693568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693568 prefixEnd_693568 := by exact prefixLift 693568
  have htrace : WordTrace (prefixWord ++ tailWord_693568) baseStart_693568 baseEnd_693568 := by
    simpa [prefixWord, tailWord_693568, baseEnd_693568] using wordTrace_append hprefix tailTrace_693568
  have hstable : (prefixWord ++ tailWord_693568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693568).length < 2 ^ (prefixWord ++ tailWord_693568).sum := by decide
  have hdescent : baseEnd_693568 < baseStart_693568 := by decide
  rcases family_descends (prefixWord ++ tailWord_693568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693625 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 1, 3, 2]
def baseStart_693625 : Nat := 118140960795 + 693625 * 2 ^ 59
def prefixEnd_693625 : Nat := 4983230072969 + 3 ^ 40 * 693625 * 2
def baseEnd_693625 : Nat := 356163018974953922697583

theorem tailTrace_693625 : CollatzResearch.WordTrace tailWord_693625 prefixEnd_693625 356163018974953922697583 := by
  unfold tailWord_693625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25298582112122561563890329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16865721408081707709260219 25298582112122561563890329)
  ·
    refine ⟨18973936584091921172917747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25298582112122561563890329 18973936584091921172917747)
    ·
      refine ⟨28460904876137881759376621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18973936584091921172917747 28460904876137881759376621)
      ·
        refine ⟨10672839328551705659766233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28460904876137881759376621 10672839328551705659766233)
        ·
          refine ⟨8004629496413779244824675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10672839328551705659766233 8004629496413779244824675)
          ·
            refine ⟨12006944244620668867237013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004629496413779244824675 12006944244620668867237013)
            ·
              refine ⟨562825511466593853151735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12006944244620668867237013 562825511466593853151735)
              ·
                refine ⟨844238267199890779727603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562825511466593853151735 844238267199890779727603)
                ·
                  refine ⟨1266357400799836169591405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844238267199890779727603 1266357400799836169591405)
                  ·
                    refine ⟨474884025299938563596777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1266357400799836169591405 474884025299938563596777)
                    ·
                      refine ⟨356163018974953922697583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474884025299938563596777 356163018974953922697583)
                      ·
                        rfl

theorem cell23_693625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_693625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693625 prefixEnd_693625 := by exact prefixLift 693625
  have htrace : WordTrace (prefixWord ++ tailWord_693625) baseStart_693625 baseEnd_693625 := by
    simpa [prefixWord, tailWord_693625, baseEnd_693625] using wordTrace_append hprefix tailTrace_693625
  have hstable : (prefixWord ++ tailWord_693625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693625).length < 2 ^ (prefixWord ++ tailWord_693625).sum := by decide
  have hdescent : baseEnd_693625 < baseStart_693625 := by decide
  rcases family_descends (prefixWord ++ tailWord_693625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693661 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 7]
def baseStart_693661 : Nat := 118140960795 + 693661 * 2 ^ 59
def prefixEnd_693661 : Nat := 4983230072969 + 3 ^ 40 * 693661 * 2
def baseEnd_693661 : Nat := 39575722697612864649713

theorem tailTrace_693661 : CollatzResearch.WordTrace tailWord_693661 prefixEnd_693661 39575722697612864649713 := by
  unfold tailWord_693661
  simp only [CollatzResearch.WordTrace]
  refine ⟨25299895139992139712200837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16866596759994759808133891 25299895139992139712200837)
  ·
    refine ⟨4743730338748526196037657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25299895139992139712200837 4743730338748526196037657)
    ·
      refine ⟨3557797754061394647028243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4743730338748526196037657 3557797754061394647028243)
      ·
        refine ⟨5336696631092091970542365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557797754061394647028243 5336696631092091970542365)
        ·
          refine ⟨2001261236659534488953387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5336696631092091970542365 2001261236659534488953387)
          ·
            refine ⟨3001891854989301733430081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001261236659534488953387 3001891854989301733430081)
            ·
              refine ⟨2251418891241976300072561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001891854989301733430081 2251418891241976300072561)
              ·
                refine ⟨1688564168431482225054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251418891241976300072561 1688564168431482225054421)
                ·
                  refine ⟨39575722697612864649713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1688564168431482225054421 39575722697612864649713)
                  ·
                    rfl

theorem cell23_693661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_693661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693661 prefixEnd_693661 := by exact prefixLift 693661
  have htrace : WordTrace (prefixWord ++ tailWord_693661) baseStart_693661 baseEnd_693661 := by
    simpa [prefixWord, tailWord_693661, baseEnd_693661] using wordTrace_append hprefix tailTrace_693661
  have hstable : (prefixWord ++ tailWord_693661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693661).length < 2 ^ (prefixWord ++ tailWord_693661).sum := by decide
  have hdescent : baseEnd_693661 < baseStart_693661 := by decide
  rcases family_descends (prefixWord ++ tailWord_693661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693762 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_693762 : Nat := 118140960795 + 693762 * 2 ^ 59
def prefixEnd_693762 : Nat := 4983230072969 + 3 ^ 40 * 693762 * 2
def baseEnd_693762 : Nat := 356233365824619886684453

theorem tailTrace_693762 : CollatzResearch.WordTrace tailWord_693762 prefixEnd_693762 356233365824619886684453 := by
  unfold tailWord_693762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325894728156558490406885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16869052608417489307751693 6325894728156558490406885)
  ·
    refine ⟨1186105261529354716951291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6325894728156558490406885 1186105261529354716951291)
    ·
      refine ⟨1779157892294032075426937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186105261529354716951291 1779157892294032075426937)
      ·
        refine ⟨1334368419220524056570203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779157892294032075426937 1334368419220524056570203)
        ·
          refine ⟨2001552628830786084855305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334368419220524056570203 2001552628830786084855305)
          ·
            refine ⟨1501164471623089563641479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001552628830786084855305 1501164471623089563641479)
            ·
              refine ⟨2251746707434634345462219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501164471623089563641479 2251746707434634345462219)
              ·
                refine ⟨3377620061151951518193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251746707434634345462219 3377620061151951518193329)
                ·
                  refine ⟨2533215045863963638644997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3377620061151951518193329 2533215045863963638644997)
                  ·
                    refine ⟨474977821099493182245937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533215045863963638644997 474977821099493182245937)
                    ·
                      refine ⟨356233365824619886684453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 474977821099493182245937 356233365824619886684453)
                      ·
                        rfl

theorem cell23_693762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_693762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693762 prefixEnd_693762 := by exact prefixLift 693762
  have htrace : WordTrace (prefixWord ++ tailWord_693762) baseStart_693762 baseEnd_693762 := by
    simpa [prefixWord, tailWord_693762, baseEnd_693762] using wordTrace_append hprefix tailTrace_693762
  have hstable : (prefixWord ++ tailWord_693762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693762).length < 2 ^ (prefixWord ++ tailWord_693762).sum := by decide
  have hdescent : baseEnd_693762 < baseStart_693762 := by decide
  rcases family_descends (prefixWord ++ tailWord_693762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693841 : List Nat := [1, 2, 2, 1, 3, 2, 3, 9]
def baseStart_693841 : Nat := 118140960795 + 693841 * 2 ^ 59
def prefixEnd_693841 : Nat := 4983230072969 + 3 ^ 40 * 693841 * 2
def baseEnd_693841 : Nat := 13195330770234262133207

theorem tailTrace_693841 : CollatzResearch.WordTrace tailWord_693841 prefixEnd_693841 13195330770234262133207 := by
  unfold tailWord_693841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25306460279340030453753377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16870973519560020302502251 25306460279340030453753377)
  ·
    refine ⟨18979845209505022840315033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25306460279340030453753377 18979845209505022840315033)
    ·
      refine ⟨14234883907128767130236275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18979845209505022840315033 14234883907128767130236275)
      ·
        refine ⟨21352325860693150695354413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14234883907128767130236275 21352325860693150695354413)
        ·
          refine ⟨8007122197759931510757905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21352325860693150695354413 8007122197759931510757905)
          ·
            refine ⟨6005341648319948633068429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007122197759931510757905 6005341648319948633068429)
            ·
              refine ⟨2252003118119980737400661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6005341648319948633068429 2252003118119980737400661)
              ·
                refine ⟨13195330770234262133207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2252003118119980737400661 13195330770234262133207)
                ·
                  rfl

theorem cell23_693841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 9].length) (baseStart_693841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693841 prefixEnd_693841 := by exact prefixLift 693841
  have htrace : WordTrace (prefixWord ++ tailWord_693841) baseStart_693841 baseEnd_693841 := by
    simpa [prefixWord, tailWord_693841, baseEnd_693841] using wordTrace_append hprefix tailTrace_693841
  have hstable : (prefixWord ++ tailWord_693841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693841).length < 2 ^ (prefixWord ++ tailWord_693841).sum := by decide
  have hdescent : baseEnd_693841 < baseStart_693841 := by decide
  rcases family_descends (prefixWord ++ tailWord_693841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693871 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 7]
def baseStart_693871 : Nat := 118140960795 + 693871 * 2 ^ 59
def prefixEnd_693871 : Nat := 4983230072969 + 3 ^ 40 * 693871 * 2
def baseEnd_693871 : Nat := 118763111738653320073817

theorem tailTrace_693871 : CollatzResearch.WordTrace tailWord_693871 prefixEnd_693871 118763111738653320073817 := by
  unfold tailWord_693871
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307554469231345577345467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16871702979487563718230311 25307554469231345577345467)
  ·
    refine ⟨37961331703847018366018201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25307554469231345577345467 37961331703847018366018201)
    ·
      refine ⟨28470998777885263774513651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37961331703847018366018201 28470998777885263774513651)
      ·
        refine ⟨42706498166827895661770477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28470998777885263774513651 42706498166827895661770477)
        ·
          refine ⟨16014936812560460873163929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42706498166827895661770477 16014936812560460873163929)
          ·
            refine ⟨12011202609420345654872947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16014936812560460873163929 12011202609420345654872947)
            ·
              refine ⟨18016803914130518482309421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12011202609420345654872947 18016803914130518482309421)
              ·
                refine ⟨6756301467798944430866033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18016803914130518482309421 6756301467798944430866033)
                ·
                  refine ⟨5067226100849208323149525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756301467798944430866033 5067226100849208323149525)
                  ·
                    refine ⟨118763111738653320073817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5067226100849208323149525 118763111738653320073817)
                    ·
                      rfl

theorem cell23_693871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_693871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693871 prefixEnd_693871 := by exact prefixLift 693871
  have htrace : WordTrace (prefixWord ++ tailWord_693871) baseStart_693871 baseEnd_693871 := by
    simpa [prefixWord, tailWord_693871, baseEnd_693871] using wordTrace_append hprefix tailTrace_693871
  have hstable : (prefixWord ++ tailWord_693871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693871).length < 2 ^ (prefixWord ++ tailWord_693871).sum := by decide
  have hdescent : baseEnd_693871 < baseStart_693871 := by decide
  rcases family_descends (prefixWord ++ tailWord_693871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693891 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_693891 : Nat := 118140960795 + 693891 * 2 ^ 59
def prefixEnd_693891 : Nat := 4983230072969 + 3 ^ 40 * 693891 * 2
def baseEnd_693891 : Nat := 356299604829049881971359

theorem tailTrace_693891 : CollatzResearch.WordTrace tailWord_693891 prefixEnd_693891 356299604829049881971359 := by
  unfold tailWord_693891
  simp only [CollatzResearch.WordTrace]
  refine ⟨25308283929158888993073527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16872189286105925995382351 25308283929158888993073527)
  ·
    refine ⟨37962425893738333489610291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25308283929158888993073527 37962425893738333489610291)
    ·
      refine ⟨56943638840607500234415437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37962425893738333489610291 56943638840607500234415437)
      ·
        refine ⟨21353864565227812587905789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56943638840607500234415437 21353864565227812587905789)
        ·
          refine ⟨8007699211960429720464671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21353864565227812587905789 8007699211960429720464671)
          ·
            refine ⟨12011548817940644580697007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8007699211960429720464671 12011548817940644580697007)
            ·
              refine ⟨18017323226910966871045511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12011548817940644580697007 18017323226910966871045511)
              ·
                refine ⟨27025984840366450306568267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18017323226910966871045511 27025984840366450306568267)
                ·
                  refine ⟨40538977260549675459852401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27025984840366450306568267 40538977260549675459852401)
                  ·
                    refine ⟨30404232945412256594889301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40538977260549675459852401 30404232945412256594889301)
                    ·
                      refine ⟨356299604829049881971359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30404232945412256594889301 356299604829049881971359)
                      ·
                        rfl

theorem cell23_693891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_693891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693891 prefixEnd_693891 := by exact prefixLift 693891
  have htrace : WordTrace (prefixWord ++ tailWord_693891) baseStart_693891 baseEnd_693891 := by
    simpa [prefixWord, tailWord_693891, baseEnd_693891] using wordTrace_append hprefix tailTrace_693891
  have hstable : (prefixWord ++ tailWord_693891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693891).length < 2 ^ (prefixWord ++ tailWord_693891).sum := by decide
  have hdescent : baseEnd_693891 < baseStart_693891 := by decide
  rcases family_descends (prefixWord ++ tailWord_693891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693938 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_693938 : Nat := 118140960795 + 693938 * 2 ^ 59
def prefixEnd_693938 : Nat := 4983230072969 + 3 ^ 40 * 693938 * 2
def baseEnd_693938 : Nat := 356323738419811198083643

theorem tailTrace_693938 : CollatzResearch.WordTrace tailWord_693938 prefixEnd_693938 356323738419811198083643 := by
  unfold tailWord_693938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327499539997154005008617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16873332106659077346689645 6327499539997154005008617)
  ·
    refine ⟨4745624654997865503756463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6327499539997154005008617 4745624654997865503756463)
    ·
      refine ⟨7118436982496798255634695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4745624654997865503756463 7118436982496798255634695)
      ·
        refine ⟨10677655473745197383452043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118436982496798255634695 10677655473745197383452043)
        ·
          refine ⟨16016483210617796075178065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677655473745197383452043 16016483210617796075178065)
          ·
            refine ⟨12012362407963347056383549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16016483210617796075178065 12012362407963347056383549)
            ·
              refine ⟨4504635902986255146143831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12012362407963347056383549 4504635902986255146143831)
              ·
                refine ⟨6756953854479382719215747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504635902986255146143831 6756953854479382719215747)
                ·
                  refine ⟨10135430781719074078823621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756953854479382719215747 10135430781719074078823621)
                  ·
                    refine ⟨1900393271572326389779429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10135430781719074078823621 1900393271572326389779429)
                    ·
                      refine ⟨356323738419811198083643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1900393271572326389779429 356323738419811198083643)
                      ·
                        rfl

theorem cell23_693938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_693938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693938 prefixEnd_693938 := by exact prefixLift 693938
  have htrace : WordTrace (prefixWord ++ tailWord_693938) baseStart_693938 baseEnd_693938 := by
    simpa [prefixWord, tailWord_693938, baseEnd_693938] using wordTrace_append hprefix tailTrace_693938
  have hstable : (prefixWord ++ tailWord_693938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693938).length < 2 ^ (prefixWord ++ tailWord_693938).sum := by decide
  have hdescent : baseEnd_693938 < baseStart_693938 := by decide
  rcases family_descends (prefixWord ++ tailWord_693938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693948 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 9]
def baseStart_693948 : Nat := 118140960795 + 693948 * 2 ^ 59
def prefixEnd_693948 : Nat := 4983230072969 + 3 ^ 40 * 693948 * 2
def baseEnd_693948 : Nat := 39592097025150684328733

theorem tailTrace_693948 : CollatzResearch.WordTrace tailWord_693948 prefixEnd_693948 39592097025150684328733 := by
  unfold tailWord_693948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655181444976193863949249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16873575259968258485265665 12655181444976193863949249)
  ·
    refine ⟨9491386083732145397961937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12655181444976193863949249 9491386083732145397961937)
    ·
      refine ⟨7118539562799109048471453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9491386083732145397961937 7118539562799109048471453)
      ·
        refine ⟨2669452336049665893176795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7118539562799109048471453 2669452336049665893176795)
        ·
          refine ⟨4004178504074498839765193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669452336049665893176795 4004178504074498839765193)
          ·
            refine ⟨3003133878055874129823895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004178504074498839765193 3003133878055874129823895)
            ·
              refine ⟨4504700817083811194735843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003133878055874129823895 4504700817083811194735843)
              ·
                refine ⟨6757051225625716792103765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504700817083811194735843 6757051225625716792103765)
                ·
                  refine ⟨39592097025150684328733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6757051225625716792103765 39592097025150684328733)
                  ·
                    rfl

theorem cell23_693948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_693948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693948 prefixEnd_693948 := by exact prefixLift 693948
  have htrace : WordTrace (prefixWord ++ tailWord_693948) baseStart_693948 baseEnd_693948 := by
    simpa [prefixWord, tailWord_693948, baseEnd_693948] using wordTrace_append hprefix tailTrace_693948
  have hstable : (prefixWord ++ tailWord_693948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693948).length < 2 ^ (prefixWord ++ tailWord_693948).sum := by decide
  have hdescent : baseEnd_693948 < baseStart_693948 := by decide
  rcases family_descends (prefixWord ++ tailWord_693948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693988 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_693988 : Nat := 118140960795 + 693988 * 2 ^ 59
def prefixEnd_693988 : Nat := 4983230072969 + 3 ^ 40 * 693988 * 2
def baseEnd_693988 : Nat := 356349412452536002458413

theorem tailTrace_693988 : CollatzResearch.WordTrace tailWord_693988 prefixEnd_693988 356349412452536002458413 := by
  unfold tailWord_693988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655910904903737279677309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16874547873204983039569745 12655910904903737279677309)
  ·
    refine ⟨4745966589338901479878991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12655910904903737279677309 4745966589338901479878991)
    ·
      refine ⟨7118949884008352219818487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4745966589338901479878991 7118949884008352219818487)
      ·
        refine ⟨10678424826012528329727731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118949884008352219818487 10678424826012528329727731)
        ·
          refine ⟨16017637239018792494591597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10678424826012528329727731 16017637239018792494591597)
          ·
            refine ⟨6006613964632047185471849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16017637239018792494591597 6006613964632047185471849)
            ·
              refine ⟨4504960473474035389103887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6006613964632047185471849 4504960473474035389103887)
              ·
                refine ⟨6757440710211053083655831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504960473474035389103887 6757440710211053083655831)
                ·
                  refine ⟨10136161065316579625483747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6757440710211053083655831 10136161065316579625483747)
                  ·
                    refine ⟨15204241597974869438225621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10136161065316579625483747 15204241597974869438225621)
                    ·
                      refine ⟨356349412452536002458413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15204241597974869438225621 356349412452536002458413)
                      ·
                        rfl

theorem cell23_693988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_693988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_693988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_693988 prefixEnd_693988 := by exact prefixLift 693988
  have htrace : WordTrace (prefixWord ++ tailWord_693988) baseStart_693988 baseEnd_693988 := by
    simpa [prefixWord, tailWord_693988, baseEnd_693988] using wordTrace_append hprefix tailTrace_693988
  have hstable : (prefixWord ++ tailWord_693988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693988).length < 2 ^ (prefixWord ++ tailWord_693988).sum := by decide
  have hdescent : baseEnd_693988 < baseStart_693988 := by decide
  rcases family_descends (prefixWord ++ tailWord_693988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694015 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 6, 2]
def baseStart_694015 : Nat := 118140960795 + 694015 * 2 ^ 59
def prefixEnd_694015 : Nat := 4983230072969 + 3 ^ 40 * 694015 * 2
def baseEnd_694015 : Nat := 356363276430207396820789

theorem tailTrace_694015 : CollatzResearch.WordTrace tailWord_694015 prefixEnd_694015 356363276430207396820789 := by
  unfold tailWord_694015
  simp only [CollatzResearch.WordTrace]
  refine ⟨25312806580709658170587499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16875204387139772113724999 25312806580709658170587499)
  ·
    refine ⟨37969209871064487255881249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25312806580709658170587499 37969209871064487255881249)
    ·
      refine ⟨28476907403298365441910937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37969209871064487255881249 28476907403298365441910937)
      ·
        refine ⟨21357680552473774081433203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28476907403298365441910937 21357680552473774081433203)
        ·
          refine ⟨32036520828710661122149805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21357680552473774081433203 32036520828710661122149805)
          ·
            refine ⟨12013695310766497920806177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32036520828710661122149805 12013695310766497920806177)
            ·
              refine ⟨9010271483074873440604633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12013695310766497920806177 9010271483074873440604633)
              ·
                refine ⟨6757703612306155080453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9010271483074873440604633 6757703612306155080453475)
                ·
                  refine ⟨10136555418459232620680213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6757703612306155080453475 10136555418459232620680213)
                  ·
                    refine ⟨475151035240276529094385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10136555418459232620680213 475151035240276529094385)
                    ·
                      refine ⟨356363276430207396820789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475151035240276529094385 356363276430207396820789)
                      ·
                        rfl

theorem cell23_694015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_694015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694015 prefixEnd_694015 := by exact prefixLift 694015
  have htrace : WordTrace (prefixWord ++ tailWord_694015) baseStart_694015 baseEnd_694015 := by
    simpa [prefixWord, tailWord_694015, baseEnd_694015] using wordTrace_append hprefix tailTrace_694015
  have hstable : (prefixWord ++ tailWord_694015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694015).length < 2 ^ (prefixWord ++ tailWord_694015).sum := by decide
  have hdescent : baseEnd_694015 < baseStart_694015 := by decide
  rcases family_descends (prefixWord ++ tailWord_694015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694028 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_694028 : Nat := 118140960795 + 694028 * 2 ^ 59
def prefixEnd_694028 : Nat := 4983230072969 + 3 ^ 40 * 694028 * 2
def baseEnd_694028 : Nat := 356369951678715845958229

theorem tailTrace_694028 : CollatzResearch.WordTrace tailWord_694028 prefixEnd_694028 356369951678715845958229 := by
  unfold tailWord_694028
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656640364831280695405369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16875520486441707593873825 12656640364831280695405369)
  ·
    refine ⟨9492480273623460521554027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12656640364831280695405369 9492480273623460521554027)
    ·
      refine ⟨14238720410435190782331041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492480273623460521554027 14238720410435190782331041)
      ·
        refine ⟨10679040307826393086748281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14238720410435190782331041 10679040307826393086748281)
        ·
          refine ⟨8009280230869794815061211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10679040307826393086748281 8009280230869794815061211)
          ·
            refine ⟨12013920346304692222591817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8009280230869794815061211 12013920346304692222591817)
            ·
              refine ⟨9010440259728519166943863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12013920346304692222591817 9010440259728519166943863)
              ·
                refine ⟨13515660389592778750415795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9010440259728519166943863 13515660389592778750415795)
                ·
                  refine ⟨20273490584389168125623693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13515660389592778750415795 20273490584389168125623693)
                  ·
                    refine ⟨7602558969145938047108885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20273490584389168125623693 7602558969145938047108885)
                    ·
                      refine ⟨356369951678715845958229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7602558969145938047108885 356369951678715845958229)
                      ·
                        rfl

theorem cell23_694028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_694028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694028 prefixEnd_694028 := by exact prefixLift 694028
  have htrace : WordTrace (prefixWord ++ tailWord_694028) baseStart_694028 baseEnd_694028 := by
    simpa [prefixWord, tailWord_694028, baseEnd_694028] using wordTrace_append hprefix tailTrace_694028
  have hstable : (prefixWord ++ tailWord_694028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694028).length < 2 ^ (prefixWord ++ tailWord_694028).sum := by decide
  have hdescent : baseEnd_694028 < baseStart_694028 := by decide
  rcases family_descends (prefixWord ++ tailWord_694028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694042 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_694042 : Nat := 118140960795 + 694042 * 2 ^ 59
def prefixEnd_694042 : Nat := 4983230072969 + 3 ^ 40 * 694042 * 2
def baseEnd_694042 : Nat := 118792380135959597061055

theorem tailTrace_694042 : CollatzResearch.WordTrace tailWord_694042 prefixEnd_694042 118792380135959597061055 := by
  unfold tailWord_694042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328447837902960445455095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16875860901074561187880253 6328447837902960445455095)
  ·
    refine ⟨9492671756854440668182643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328447837902960445455095 9492671756854440668182643)
    ·
      refine ⟨14239007635281661002273965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492671756854440668182643 14239007635281661002273965)
      ·
        refine ⟨5339627863230622875852737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14239007635281661002273965 5339627863230622875852737)
        ·
          refine ⟨4004720897422967156889553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5339627863230622875852737 4004720897422967156889553)
          ·
            refine ⟨3003540673067225367667165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004720897422967156889553 3003540673067225367667165)
            ·
              refine ⟨1126327752400209512875187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3003540673067225367667165 1126327752400209512875187)
              ·
                refine ⟨1689491628600314269312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126327752400209512875187 1689491628600314269312781)
                ·
                  refine ⟨633559360725117850992293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1689491628600314269312781 633559360725117850992293)
                  ·
                    refine ⟨118792380135959597061055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 633559360725117850992293 118792380135959597061055)
                    ·
                      rfl

theorem cell23_694042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_694042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694042 prefixEnd_694042 := by exact prefixLift 694042
  have htrace : WordTrace (prefixWord ++ tailWord_694042) baseStart_694042 baseEnd_694042 := by
    simpa [prefixWord, tailWord_694042, baseEnd_694042] using wordTrace_append hprefix tailTrace_694042
  have hstable : (prefixWord ++ tailWord_694042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694042).length < 2 ^ (prefixWord ++ tailWord_694042).sum := by decide
  have hdescent : baseEnd_694042 < baseStart_694042 := by decide
  rcases family_descends (prefixWord ++ tailWord_694042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694069 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_694069 : Nat := 118140960795 + 694069 * 2 ^ 59
def prefixEnd_694069 : Nat := 4983230072969 + 3 ^ 40 * 694069 * 2
def baseEnd_694069 : Nat := 356391004385550185545541

theorem tailTrace_694069 : CollatzResearch.WordTrace tailWord_694069 prefixEnd_694069 356391004385550185545541 := by
  unfold tailWord_694069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314776122514025393053261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16876517415009350262035507 25314776122514025393053261)
  ·
    refine ⟨9493041045942759522394973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25314776122514025393053261 9493041045942759522394973)
    ·
      refine ⟨3559890392228534820898115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9493041045942759522394973 3559890392228534820898115)
      ·
        refine ⟨5339835588342802231347173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3559890392228534820898115 5339835588342802231347173)
        ·
          refine ⟨1001219172814275418377595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5339835588342802231347173 1001219172814275418377595)
          ·
            refine ⟨1501828759221413127566393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001219172814275418377595 1501828759221413127566393)
            ·
              refine ⟨1126371569416059845674795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501828759221413127566393 1126371569416059845674795)
              ·
                refine ⟨1689557354124089768512193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126371569416059845674795 1689557354124089768512193)
                ·
                  refine ⟨1267168015593067326384145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689557354124089768512193 1267168015593067326384145)
                  ·
                    refine ⟨950376011694800494788109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1267168015593067326384145 950376011694800494788109)
                    ·
                      refine ⟨356391004385550185545541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 950376011694800494788109 356391004385550185545541)
                      ·
                        rfl

theorem cell23_694069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_694069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694069 prefixEnd_694069 := by exact prefixLift 694069
  have htrace : WordTrace (prefixWord ++ tailWord_694069) baseStart_694069 baseEnd_694069 := by
    simpa [prefixWord, tailWord_694069, baseEnd_694069] using wordTrace_append hprefix tailTrace_694069
  have hstable : (prefixWord ++ tailWord_694069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694069).length < 2 ^ (prefixWord ++ tailWord_694069).sum := by decide
  have hdescent : baseEnd_694069 < baseStart_694069 := by decide
  rcases family_descends (prefixWord ++ tailWord_694069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694086 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_694086 : Nat := 118140960795 + 694086 * 2 ^ 59
def prefixEnd_694086 : Nat := 4983230072969 + 3 ^ 40 * 694086 * 2
def baseEnd_694086 : Nat := 356399733556676619032963

theorem tailTrace_694086 : CollatzResearch.WordTrace tailWord_694086 prefixEnd_694086 356399733556676619032963 := by
  unfold tailWord_694086
  simp only [CollatzResearch.WordTrace]
  refine ⟨791106130107888665513191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16876930775634958197614741 791106130107888665513191)
  ·
    refine ⟨1186659195161832998269787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791106130107888665513191 1186659195161832998269787)
    ·
      refine ⟨1779988792742749497404681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186659195161832998269787 1779988792742749497404681)
      ·
        refine ⟨1334991594557062123053511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779988792742749497404681 1334991594557062123053511)
        ·
          refine ⟨2002487391835593184580267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334991594557062123053511 2002487391835593184580267)
          ·
            refine ⟨3003731087753389776870401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002487391835593184580267 3003731087753389776870401)
            ·
              refine ⟨2252798315815042332652801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003731087753389776870401 2252798315815042332652801)
              ·
                refine ⟨1689598736861281749489601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252798315815042332652801 1689598736861281749489601)
                ·
                  refine ⟨1267199052645961312117201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689598736861281749489601 1267199052645961312117201)
                  ·
                    refine ⟨950399289484470984087901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1267199052645961312117201 950399289484470984087901)
                    ·
                      refine ⟨356399733556676619032963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 950399289484470984087901 356399733556676619032963)
                      ·
                        rfl

theorem cell23_694086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_694086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694086 prefixEnd_694086 := by exact prefixLift 694086
  have htrace : WordTrace (prefixWord ++ tailWord_694086) baseStart_694086 baseEnd_694086 := by
    simpa [prefixWord, tailWord_694086, baseEnd_694086] using wordTrace_append hprefix tailTrace_694086
  have hstable : (prefixWord ++ tailWord_694086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694086).length < 2 ^ (prefixWord ++ tailWord_694086).sum := by decide
  have hdescent : baseEnd_694086 < baseStart_694086 := by decide
  rcases family_descends (prefixWord ++ tailWord_694086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694093 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_694093 : Nat := 118140960795 + 694093 * 2 ^ 59
def prefixEnd_694093 : Nat := 4983230072969 + 3 ^ 40 * 694093 * 2
def baseEnd_694093 : Nat := 118801109307086030548477

theorem tailTrace_694093 : CollatzResearch.WordTrace tailWord_694093 prefixEnd_694093 118801109307086030548477 := by
  unfold tailWord_694093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25315651474427077491926933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16877100982951384994617955 25315651474427077491926933)
  ·
    refine ⟨1186671162863769257434075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25315651474427077491926933 1186671162863769257434075)
    ·
      refine ⟨1780006744295653886151113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186671162863769257434075 1780006744295653886151113)
      ·
        refine ⟨1335005058221740414613335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780006744295653886151113 1335005058221740414613335)
        ·
          refine ⟨2002507587332610621920003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335005058221740414613335 2002507587332610621920003)
          ·
            refine ⟨3003761380998915932880005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002507587332610621920003 3003761380998915932880005)
            ·
              refine ⟨563205258937296737415001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3003761380998915932880005 563205258937296737415001)
              ·
                refine ⟨422403944202972553061251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563205258937296737415001 422403944202972553061251)
                ·
                  refine ⟨633605916304458829591877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422403944202972553061251 633605916304458829591877)
                  ·
                    refine ⟨118801109307086030548477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 633605916304458829591877 118801109307086030548477)
                    ·
                      rfl

theorem cell23_694093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_694093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694093 prefixEnd_694093 := by exact prefixLift 694093
  have htrace : WordTrace (prefixWord ++ tailWord_694093) baseStart_694093 baseEnd_694093 := by
    simpa [prefixWord, tailWord_694093, baseEnd_694093] using wordTrace_append hprefix tailTrace_694093
  have hstable : (prefixWord ++ tailWord_694093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694093).length < 2 ^ (prefixWord ++ tailWord_694093).sum := by decide
  have hdescent : baseEnd_694093 < baseStart_694093 := by decide
  rcases family_descends (prefixWord ++ tailWord_694093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694105 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_694105 : Nat := 118140960795 + 694105 * 2 ^ 59
def prefixEnd_694105 : Nat := 4983230072969 + 3 ^ 40 * 694105 * 2
def baseEnd_694105 : Nat := 356409489689112044695375

theorem tailTrace_694105 : CollatzResearch.WordTrace tailWord_694105 prefixEnd_694105 356409489689112044695375 := by
  unfold tailWord_694105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316089150383603541363769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16877392766922402360909179 25316089150383603541363769)
  ·
    refine ⟨18987066862787702656022827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25316089150383603541363769 18987066862787702656022827)
    ·
      refine ⟨28480600294181553984034241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18987066862787702656022827 28480600294181553984034241)
      ·
        refine ⟨21360450220636165488025681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28480600294181553984034241 21360450220636165488025681)
        ·
          refine ⟨16020337665477124116019261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21360450220636165488025681 16020337665477124116019261)
          ·
            refine ⟨6007626624553921543507223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16020337665477124116019261 6007626624553921543507223)
            ·
              refine ⟨9011439936830882315260835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007626624553921543507223 9011439936830882315260835)
              ·
                refine ⟨13517159905246323472891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011439936830882315260835 13517159905246323472891253)
                ·
                  refine ⟨1267233741116842825583555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13517159905246323472891253 1267233741116842825583555)
                  ·
                    refine ⟨1900850611675264238375333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1267233741116842825583555 1900850611675264238375333)
                    ·
                      refine ⟨356409489689112044695375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1900850611675264238375333 356409489689112044695375)
                      ·
                        rfl

theorem cell23_694105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_694105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694105 prefixEnd_694105 := by exact prefixLift 694105
  have htrace : WordTrace (prefixWord ++ tailWord_694105) baseStart_694105 baseEnd_694105 := by
    simpa [prefixWord, tailWord_694105, baseEnd_694105] using wordTrace_append hprefix tailTrace_694105
  have hstable : (prefixWord ++ tailWord_694105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694105).length < 2 ^ (prefixWord ++ tailWord_694105).sum := by decide
  have hdescent : baseEnd_694105 < baseStart_694105 := by decide
  rcases family_descends (prefixWord ++ tailWord_694105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694126 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_694126 : Nat := 118140960795 + 694126 * 2 ^ 59
def prefixEnd_694126 : Nat := 4983230072969 + 3 ^ 40 * 694126 * 2
def baseEnd_694126 : Nat := 356420272782856462532779

theorem tailTrace_694126 : CollatzResearch.WordTrace tailWord_694126 prefixEnd_694126 356420272782856462532779 := by
  unfold tailWord_694126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164606885413440515984779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16877903388871682751918821 3164606885413440515984779)
  ·
    refine ⟨4746910328120160773977169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3164606885413440515984779 4746910328120160773977169)
    ·
      refine ⟨3560182746090120580482877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4746910328120160773977169 3560182746090120580482877)
      ·
        refine ⟨1335068529783795217681079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3560182746090120580482877 1335068529783795217681079)
        ·
          refine ⟨2002602794675692826521619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335068529783795217681079 2002602794675692826521619)
          ·
            refine ⟨3003904192013539239782429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002602794675692826521619 3003904192013539239782429)
            ·
              refine ⟨1126464072005077214918411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3003904192013539239782429 1126464072005077214918411)
              ·
                refine ⟨1689696108007615822377617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126464072005077214918411 1689696108007615822377617)
                ·
                  refine ⟨1267272081005711866783213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689696108007615822377617 1267272081005711866783213)
                  ·
                    refine ⟨475227030377141950043705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267272081005711866783213 475227030377141950043705)
                    ·
                      refine ⟨356420272782856462532779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475227030377141950043705 356420272782856462532779)
                      ·
                        rfl

theorem cell23_694126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_694126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694126 prefixEnd_694126 := by exact prefixLift 694126
  have htrace : WordTrace (prefixWord ++ tailWord_694126) baseStart_694126 baseEnd_694126 := by
    simpa [prefixWord, tailWord_694126, baseEnd_694126] using wordTrace_append hprefix tailTrace_694126
  have hstable : (prefixWord ++ tailWord_694126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694126).length < 2 ^ (prefixWord ++ tailWord_694126).sum := by decide
  have hdescent : baseEnd_694126 < baseStart_694126 := by decide
  rcases family_descends (prefixWord ++ tailWord_694126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694196 : List Nat := [2, 5, 2, 1, 3, 1, 9]
def baseStart_694196 : Nat := 118140960795 + 694196 * 2 ^ 59
def prefixEnd_694196 : Nat := 4983230072969 + 3 ^ 40 * 694196 * 2
def baseEnd_694196 : Nat := 4400694029983594921697

theorem tailTrace_694196 : CollatzResearch.WordTrace tailWord_694196 prefixEnd_694196 4400694029983594921697 := by
  unfold tailWord_694196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12659704096526963041463221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16879605462035950721950961 12659704096526963041463221)
  ·
    refine ⟨1186847259049402785137177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12659704096526963041463221 1186847259049402785137177)
    ·
      refine ⟨890135444287052088852883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1186847259049402785137177 890135444287052088852883)
      ·
        refine ⟨1335203166430578133279325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890135444287052088852883 1335203166430578133279325)
        ·
          refine ⟨500701187411466799979747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1335203166430578133279325 500701187411466799979747)
          ·
            refine ⟨751051781117200199969621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500701187411466799979747 751051781117200199969621)
            ·
              refine ⟨4400694029983594921697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 751051781117200199969621 4400694029983594921697)
              ·
                rfl

theorem cell23_694196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 9].length) (baseStart_694196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694196 prefixEnd_694196 := by exact prefixLift 694196
  have htrace : WordTrace (prefixWord ++ tailWord_694196) baseStart_694196 baseEnd_694196 := by
    simpa [prefixWord, tailWord_694196, baseEnd_694196] using wordTrace_append hprefix tailTrace_694196
  have hstable : (prefixWord ++ tailWord_694196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694196).length < 2 ^ (prefixWord ++ tailWord_694196).sum := by decide
  have hdescent : baseEnd_694196 < baseStart_694196 := by decide
  rcases family_descends (prefixWord ++ tailWord_694196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694215 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_694215 : Nat := 118140960795 + 694215 * 2 ^ 59
def prefixEnd_694215 : Nat := 4983230072969 + 3 ^ 40 * 694215 * 2
def baseEnd_694215 : Nat := 356465972561106614319869

theorem tailTrace_694215 : CollatzResearch.WordTrace tailWord_694215 prefixEnd_694215 356465972561106614319869 := by
  unfold tailWord_694215
  simp only [CollatzResearch.WordTrace]
  refine ⟨25320101179985092327868099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16880067453323394885245399 25320101179985092327868099)
  ·
    refine ⟨37980151769977638491802149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25320101179985092327868099 37980151769977638491802149)
    ·
      refine ⟨7121278456870807217212903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37980151769977638491802149 7121278456870807217212903)
      ·
        refine ⟨10681917685306210825819355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7121278456870807217212903 10681917685306210825819355)
        ·
          refine ⟨16022876527959316238729033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681917685306210825819355 16022876527959316238729033)
          ·
            refine ⟨12017157395969487179046775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16022876527959316238729033 12017157395969487179046775)
            ·
              refine ⟨18025736093954230768570163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12017157395969487179046775 18025736093954230768570163)
              ·
                refine ⟨27038604140931346152855245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18025736093954230768570163 27038604140931346152855245)
                ·
                  refine ⟨10139476552849254807320717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27038604140931346152855245 10139476552849254807320717)
                  ·
                    refine ⟨3802303707318470552745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10139476552849254807320717 3802303707318470552745269)
                    ·
                      refine ⟨356465972561106614319869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3802303707318470552745269 356465972561106614319869)
                      ·
                        rfl

theorem cell23_694215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_694215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694215 prefixEnd_694215 := by exact prefixLift 694215
  have htrace : WordTrace (prefixWord ++ tailWord_694215) baseStart_694215 baseEnd_694215 := by
    simpa [prefixWord, tailWord_694215, baseEnd_694215] using wordTrace_append hprefix tailTrace_694215
  have hstable : (prefixWord ++ tailWord_694215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694215).length < 2 ^ (prefixWord ++ tailWord_694215).sum := by decide
  have hdescent : baseEnd_694215 < baseStart_694215 := by decide
  rcases family_descends (prefixWord ++ tailWord_694215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694233 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 1, 3, 2]
def baseStart_694233 : Nat := 118140960795 + 694233 * 2 ^ 59
def prefixEnd_694233 : Nat := 4983230072969 + 3 ^ 40 * 694233 * 2
def baseEnd_694233 : Nat := 356475215212887543894787

theorem tailTrace_694233 : CollatzResearch.WordTrace tailWord_694233 prefixEnd_694233 356475215212887543894787 := by
  unfold tailWord_694233
  simp only [CollatzResearch.WordTrace]
  refine ⟨25320757693919881402023353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16880505129279920934682235 25320757693919881402023353)
  ·
    refine ⟨18990568270439911051517515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25320757693919881402023353 18990568270439911051517515)
    ·
      refine ⟨28485852405659866577276273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18990568270439911051517515 28485852405659866577276273)
      ·
        refine ⟨21364389304244899932957205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28485852405659866577276273 21364389304244899932957205)
        ·
          refine ⟨1001455748636479684357369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21364389304244899932957205 1001455748636479684357369)
          ·
            refine ⟨751091811477359763268027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001455748636479684357369 751091811477359763268027)
            ·
              refine ⟨1126637717216039644902041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751091811477359763268027 1126637717216039644902041)
              ·
                refine ⟨844978287912029733676531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126637717216039644902041 844978287912029733676531)
                ·
                  refine ⟨1267467431868044600514797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844978287912029733676531 1267467431868044600514797)
                  ·
                    refine ⟨475300286950516725193049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1267467431868044600514797 475300286950516725193049)
                    ·
                      refine ⟨356475215212887543894787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475300286950516725193049 356475215212887543894787)
                      ·
                        rfl

theorem cell23_694233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_694233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694233 prefixEnd_694233 := by exact prefixLift 694233
  have htrace : WordTrace (prefixWord ++ tailWord_694233) baseStart_694233 baseEnd_694233 := by
    simpa [prefixWord, tailWord_694233, baseEnd_694233] using wordTrace_append hprefix tailTrace_694233
  have hstable : (prefixWord ++ tailWord_694233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694233).length < 2 ^ (prefixWord ++ tailWord_694233).sum := by decide
  have hdescent : baseEnd_694233 < baseStart_694233 := by decide
  rcases family_descends (prefixWord ++ tailWord_694233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694276 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_694276 : Nat := 118140960795 + 694276 * 2 ^ 59
def prefixEnd_694276 : Nat := 4983230072969 + 3 ^ 40 * 694276 * 2
def baseEnd_694276 : Nat := 356497294881030875657089

theorem tailTrace_694276 : CollatzResearch.WordTrace tailWord_694276 prefixEnd_694276 356497294881030875657089 := by
  unfold tailWord_694276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661163016382049872919341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16881550688509399830559121 12661163016382049872919341)
  ·
    refine ⟨4747936131143268702344753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12661163016382049872919341 4747936131143268702344753)
    ·
      refine ⟨3560952098357451526758565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4747936131143268702344753 3560952098357451526758565)
      ·
        refine ⟨667678518442022161267231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3560952098357451526758565 667678518442022161267231)
        ·
          refine ⟨1001517777663033241900847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667678518442022161267231 1001517777663033241900847)
          ·
            refine ⟨1502276666494549862851271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001517777663033241900847 1502276666494549862851271)
            ·
              refine ⟨2253414999741824794276907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502276666494549862851271 2253414999741824794276907)
              ·
                refine ⟨3380122499612737191415361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253414999741824794276907 3380122499612737191415361)
                ·
                  refine ⟨2535091874709552893561521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380122499612737191415361 2535091874709552893561521)
                  ·
                    refine ⟨1901318906032164670171141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535091874709552893561521 1901318906032164670171141)
                    ·
                      refine ⟨356497294881030875657089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1901318906032164670171141 356497294881030875657089)
                      ·
                        rfl

theorem cell23_694276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_694276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694276 prefixEnd_694276 := by exact prefixLift 694276
  have htrace : WordTrace (prefixWord ++ tailWord_694276) baseStart_694276 baseEnd_694276 := by
    simpa [prefixWord, tailWord_694276, baseEnd_694276] using wordTrace_append hprefix tailTrace_694276
  have hstable : (prefixWord ++ tailWord_694276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694276).length < 2 ^ (prefixWord ++ tailWord_694276).sum := by decide
  have hdescent : baseEnd_694276 < baseStart_694276 := by decide
  rcases family_descends (prefixWord ++ tailWord_694276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694279 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_694279 : Nat := 118140960795 + 694279 * 2 ^ 59
def prefixEnd_694279 : Nat := 4983230072969 + 3 ^ 40 * 694279 * 2
def baseEnd_694279 : Nat := 356498835322994363919575

theorem tailTrace_694279 : CollatzResearch.WordTrace tailWord_694279 prefixEnd_694279 356498835322994363919575 := by
  unfold tailWord_694279
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322435451753231258197891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16881623634502154172131927 25322435451753231258197891)
  ·
    refine ⟨37983653177629846887296837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25322435451753231258197891 37983653177629846887296837)
    ·
      refine ⟨7121934970805596291368157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37983653177629846887296837 7121934970805596291368157)
      ·
        refine ⟨2670725614052098609263059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7121934970805596291368157 2670725614052098609263059)
        ·
          refine ⟨4006088421078147913894589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670725614052098609263059 4006088421078147913894589)
          ·
            refine ⟨1502283157904305467710471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006088421078147913894589 1502283157904305467710471)
            ·
              refine ⟨2253424736856458201565707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502283157904305467710471 2253424736856458201565707)
              ·
                refine ⟨3380137105284687302348561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253424736856458201565707 3380137105284687302348561)
                ·
                  refine ⟨2535102828963515476761421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380137105284687302348561 2535102828963515476761421)
                  ·
                    refine ⟨950663560861318303785533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535102828963515476761421 950663560861318303785533)
                    ·
                      refine ⟨356498835322994363919575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 950663560861318303785533 356498835322994363919575)
                      ·
                        rfl

theorem cell23_694279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_694279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694279 prefixEnd_694279 := by exact prefixLift 694279
  have htrace : WordTrace (prefixWord ++ tailWord_694279) baseStart_694279 baseEnd_694279 := by
    simpa [prefixWord, tailWord_694279, baseEnd_694279] using wordTrace_append hprefix tailTrace_694279
  have hstable : (prefixWord ++ tailWord_694279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694279).length < 2 ^ (prefixWord ++ tailWord_694279).sum := by decide
  have hdescent : baseEnd_694279 < baseStart_694279 := by decide
  rcases family_descends (prefixWord ++ tailWord_694279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694332 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_694332 : Nat := 118140960795 + 694332 * 2 ^ 59
def prefixEnd_694332 : Nat := 4983230072969 + 3 ^ 40 * 694332 * 2
def baseEnd_694332 : Nat := 356526049797682656556831

theorem tailTrace_694332 : CollatzResearch.WordTrace tailWord_694332 prefixEnd_694332 356526049797682656556831 := by
  unfold tailWord_694332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662184260280610654938625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16882912347040814206584833 12662184260280610654938625)
  ·
    refine ⟨9496638195210457991203969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12662184260280610654938625 9496638195210457991203969)
    ·
      refine ⟨7122478646407843493402977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9496638195210457991203969 7122478646407843493402977)
      ·
        refine ⟨5341858984805882620052233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7122478646407843493402977 5341858984805882620052233)
        ·
          refine ⟨4006394238604411965039175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341858984805882620052233 4006394238604411965039175)
          ·
            refine ⟨6009591357906617947558763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006394238604411965039175 6009591357906617947558763)
            ·
              refine ⟨9014387036859926921338145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009591357906617947558763 9014387036859926921338145)
              ·
                refine ⟨6760790277644945191003609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014387036859926921338145 6760790277644945191003609)
                ·
                  refine ⟨5070592708233708893252707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6760790277644945191003609 5070592708233708893252707)
                  ·
                    refine ⟨7605889062350563339879061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070592708233708893252707 7605889062350563339879061)
                    ·
                      refine ⟨356526049797682656556831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7605889062350563339879061 356526049797682656556831)
                      ·
                        rfl

theorem cell23_694332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_694332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694332 prefixEnd_694332 := by exact prefixLift 694332
  have htrace : WordTrace (prefixWord ++ tailWord_694332) baseStart_694332 baseEnd_694332 := by
    simpa [prefixWord, tailWord_694332, baseEnd_694332] using wordTrace_append hprefix tailTrace_694332
  have hstable : (prefixWord ++ tailWord_694332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694332).length < 2 ^ (prefixWord ++ tailWord_694332).sum := by decide
  have hdescent : baseEnd_694332 < baseStart_694332 := by decide
  rcases family_descends (prefixWord ++ tailWord_694332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694349 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_694349 : Nat := 118140960795 + 694349 * 2 ^ 59
def prefixEnd_694349 : Nat := 4983230072969 + 3 ^ 40 * 694349 * 2
def baseEnd_694349 : Nat := 356534778968809090044253

theorem tailTrace_694349 : CollatzResearch.WordTrace tailWord_694349 prefixEnd_694349 356534778968809090044253 := by
  unfold tailWord_694349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25324988561499633213246101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16883325707666422142164067 25324988561499633213246101)
  ·
    refine ⟨1187108838820295306870911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25324988561499633213246101 1187108838820295306870911)
    ·
      refine ⟨1780663258230442960306367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187108838820295306870911 1780663258230442960306367)
      ·
        refine ⟨2670994887345664440459551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780663258230442960306367 2670994887345664440459551)
        ·
          refine ⟨4006492331018496660689327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670994887345664440459551 4006492331018496660689327)
          ·
            refine ⟨6009738496527744991033991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006492331018496660689327 6009738496527744991033991)
            ·
              refine ⟨9014607744791617486550987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009738496527744991033991 9014607744791617486550987)
              ·
                refine ⟨13521911617187426229826481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014607744791617486550987 13521911617187426229826481)
                ·
                  refine ⟨10141433712890569672369861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13521911617187426229826481 10141433712890569672369861)
                  ·
                    refine ⟨1901518821166981813569349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10141433712890569672369861 1901518821166981813569349)
                    ·
                      refine ⟨356534778968809090044253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1901518821166981813569349 356534778968809090044253)
                      ·
                        rfl

theorem cell23_694349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_694349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694349 prefixEnd_694349 := by exact prefixLift 694349
  have htrace : WordTrace (prefixWord ++ tailWord_694349) baseStart_694349 baseEnd_694349 := by
    simpa [prefixWord, tailWord_694349, baseEnd_694349] using wordTrace_append hprefix tailTrace_694349
  have hstable : (prefixWord ++ tailWord_694349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694349).length < 2 ^ (prefixWord ++ tailWord_694349).sum := by decide
  have hdescent : baseEnd_694349 < baseStart_694349 := by decide
  rcases family_descends (prefixWord ++ tailWord_694349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694392 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_694392 : Nat := 118140960795 + 694392 * 2 ^ 59
def prefixEnd_694392 : Nat := 4983230072969 + 3 ^ 40 * 694392 * 2
def baseEnd_694392 : Nat := 356556858636952421806555

theorem tailTrace_694392 : CollatzResearch.WordTrace tailWord_694392 prefixEnd_694392 356556858636952421806555 := by
  unfold tailWord_694392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663278450171925778530715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16884371266895901038040953 12663278450171925778530715)
  ·
    refine ⟨18994917675257888667796073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12663278450171925778530715 18994917675257888667796073)
    ·
      refine ⟨14246188256443416500847055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18994917675257888667796073 14246188256443416500847055)
      ·
        refine ⟨21369282384665124751270583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14246188256443416500847055 21369282384665124751270583)
        ·
          refine ⟨32053923576997687126905875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21369282384665124751270583 32053923576997687126905875)
          ·
            refine ⟨48080885365496530690358813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32053923576997687126905875 48080885365496530690358813)
            ·
              refine ⟨18030332012061199008884555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48080885365496530690358813 18030332012061199008884555)
              ·
                refine ⟨27045498018091798513326833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18030332012061199008884555 27045498018091798513326833)
                ·
                  refine ⟨20284123513568848884995125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27045498018091798513326833 20284123513568848884995125)
                  ·
                    refine ⟨1901636579397079582968293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20284123513568848884995125 1901636579397079582968293)
                    ·
                      refine ⟨356556858636952421806555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1901636579397079582968293 356556858636952421806555)
                      ·
                        rfl

theorem cell23_694392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_694392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694392 prefixEnd_694392 := by exact prefixLift 694392
  have htrace : WordTrace (prefixWord ++ tailWord_694392) baseStart_694392 baseEnd_694392 := by
    simpa [prefixWord, tailWord_694392, baseEnd_694392] using wordTrace_append hprefix tailTrace_694392
  have hstable : (prefixWord ++ tailWord_694392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694392).length < 2 ^ (prefixWord ++ tailWord_694392).sum := by decide
  have hdescent : baseEnd_694392 < baseStart_694392 := by decide
  rcases family_descends (prefixWord ++ tailWord_694392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694409 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_694409 : Nat := 118140960795 + 694409 * 2 ^ 59
def prefixEnd_694409 : Nat := 4983230072969 + 3 ^ 40 * 694409 * 2
def baseEnd_694409 : Nat := 356565587808078855293977

theorem tailTrace_694409 : CollatzResearch.WordTrace tailWord_694409 prefixEnd_694409 356565587808078855293977 := by
  unfold tailWord_694409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25327176941282263460430281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16884784627521508973620187 25327176941282263460430281)
  ·
    refine ⟨18995382705961697595322711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25327176941282263460430281 18995382705961697595322711)
    ·
      refine ⟨28493074058942546392984067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18995382705961697595322711 28493074058942546392984067)
      ·
        refine ⟨42739611088413819589476101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28493074058942546392984067 42739611088413819589476101)
        ·
          refine ⟨8013677079077591173026769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42739611088413819589476101 8013677079077591173026769)
          ·
            refine ⟨6010257809308193379770077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8013677079077591173026769 6010257809308193379770077)
            ·
              refine ⟨2253846678490572517413779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6010257809308193379770077 2253846678490572517413779)
              ·
                refine ⟨3380770017735858776120669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253846678490572517413779 3380770017735858776120669)
                ·
                  refine ⟨1267788756650947041045251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3380770017735858776120669 1267788756650947041045251)
                  ·
                    refine ⟨1901683134976420561567877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1267788756650947041045251 1901683134976420561567877)
                    ·
                      refine ⟨356565587808078855293977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1901683134976420561567877 356565587808078855293977)
                      ·
                        rfl

theorem cell23_694409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_694409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694409 prefixEnd_694409 := by exact prefixLift 694409
  have htrace : WordTrace (prefixWord ++ tailWord_694409) baseStart_694409 baseEnd_694409 := by
    simpa [prefixWord, tailWord_694409, baseEnd_694409] using wordTrace_append hprefix tailTrace_694409
  have hstable : (prefixWord ++ tailWord_694409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694409).length < 2 ^ (prefixWord ++ tailWord_694409).sum := by decide
  have hdescent : baseEnd_694409 < baseStart_694409 := by decide
  rcases family_descends (prefixWord ++ tailWord_694409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694412 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_694412 : Nat := 118140960795 + 694412 * 2 ^ 59
def prefixEnd_694412 : Nat := 4983230072969 + 3 ^ 40 * 694412 * 2
def baseEnd_694412 : Nat := 356567128250042343556463

theorem tailTrace_694412 : CollatzResearch.WordTrace tailWord_694412 prefixEnd_694412 356567128250042343556463 := by
  unfold tailWord_694412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663643180135697486394745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16884857573514263315192993 12663643180135697486394745)
  ·
    refine ⟨9497732385101773114796059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12663643180135697486394745 9497732385101773114796059)
    ·
      refine ⟨14246598577652659672194089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9497732385101773114796059 14246598577652659672194089)
      ·
        refine ⟨10684948933239494754145567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14246598577652659672194089 10684948933239494754145567)
        ·
          refine ⟨16027423399859242131218351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10684948933239494754145567 16027423399859242131218351)
          ·
            refine ⟨24041135099788863196827527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16027423399859242131218351 24041135099788863196827527)
            ·
              refine ⟨36061702649683294795241291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24041135099788863196827527 36061702649683294795241291)
              ·
                refine ⟨54092553974524942192861937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36061702649683294795241291 54092553974524942192861937)
                ·
                  refine ⟨40569415480893706644646453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54092553974524942192861937 40569415480893706644646453)
                  ·
                    refine ⟨3803382701333784997935605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40569415480893706644646453 3803382701333784997935605)
                    ·
                      refine ⟨356567128250042343556463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3803382701333784997935605 356567128250042343556463)
                      ·
                        rfl

theorem cell23_694412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_694412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694412 prefixEnd_694412 := by exact prefixLift 694412
  have htrace : WordTrace (prefixWord ++ tailWord_694412) baseStart_694412 baseEnd_694412 := by
    simpa [prefixWord, tailWord_694412, baseEnd_694412] using wordTrace_append hprefix tailTrace_694412
  have hstable : (prefixWord ++ tailWord_694412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694412).length < 2 ^ (prefixWord ++ tailWord_694412).sum := by decide
  have hdescent : baseEnd_694412 < baseStart_694412 := by decide
  rcases family_descends (prefixWord ++ tailWord_694412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694423 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 1, 5]
def baseStart_694423 : Nat := 118140960795 + 694423 * 2 ^ 59
def prefixEnd_694423 : Nat := 4983230072969 + 3 ^ 40 * 694423 * 2
def baseEnd_694423 : Nat := 118857592179080600172971

theorem tailTrace_694423 : CollatzResearch.WordTrace tailWord_694423 prefixEnd_694423 118857592179080600172971 := by
  unfold tailWord_694423
  simp only [CollatzResearch.WordTrace]
  refine ⟨25327687563231543851439923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16885125042154362567626615 25327687563231543851439923)
  ·
    refine ⟨37991531344847315777159885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25327687563231543851439923 37991531344847315777159885)
    ·
      refine ⟨14246824254317743416434957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37991531344847315777159885 14246824254317743416434957)
      ·
        refine ⟨5342559095369153781163109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14246824254317743416434957 5342559095369153781163109)
        ·
          refine ⟨1001729830381716333968083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5342559095369153781163109 1001729830381716333968083)
          ·
            refine ⟨1502594745572574500952125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001729830381716333968083 1502594745572574500952125)
            ·
              refine ⟨563473029589715437857047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1502594745572574500952125 563473029589715437857047)
              ·
                refine ⟨845209544384573156785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563473029589715437857047 845209544384573156785571)
                ·
                  refine ⟨1267814316576859735178357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845209544384573156785571 1267814316576859735178357)
                  ·
                    refine ⟨118857592179080600172971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1267814316576859735178357 118857592179080600172971)
                    ·
                      rfl

theorem cell23_694423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_694423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694423 prefixEnd_694423 := by exact prefixLift 694423
  have htrace : WordTrace (prefixWord ++ tailWord_694423) baseStart_694423 baseEnd_694423 := by
    simpa [prefixWord, tailWord_694423, baseEnd_694423] using wordTrace_append hprefix tailTrace_694423
  have hstable : (prefixWord ++ tailWord_694423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694423).length < 2 ^ (prefixWord ++ tailWord_694423).sum := by decide
  have hdescent : baseEnd_694423 < baseStart_694423 := by decide
  rcases family_descends (prefixWord ++ tailWord_694423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694432 : List Nat := [2, 1, 1, 4, 2, 13]
def baseStart_694432 : Nat := 118140960795 + 694432 * 2 ^ 59
def prefixEnd_694432 : Nat := 4983230072969 + 3 ^ 40 * 694432 * 2
def baseEnd_694432 : Nat := 1467396699025235659697

theorem tailTrace_694432 : CollatzResearch.WordTrace tailWord_694432 prefixEnd_694432 1467396699025235659697 := by
  unfold tailWord_694432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664007910099469194258775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16885343880132625592345033 12664007910099469194258775)
  ·
    refine ⟨18996011865149203791388163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12664007910099469194258775 18996011865149203791388163)
    ·
      refine ⟨28494017797723805687082245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18996011865149203791388163 28494017797723805687082245)
      ·
        refine ⟨5342628337073213566327921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28494017797723805687082245 5342628337073213566327921)
        ·
          refine ⟨4006971252804910174745941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342628337073213566327921 4006971252804910174745941)
          ·
            refine ⟨1467396699025235659697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4006971252804910174745941 1467396699025235659697)
            ·
              rfl

theorem cell23_694432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 13].length) (baseStart_694432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694432 prefixEnd_694432 := by exact prefixLift 694432
  have htrace : WordTrace (prefixWord ++ tailWord_694432) baseStart_694432 baseEnd_694432 := by
    simpa [prefixWord, tailWord_694432, baseEnd_694432] using wordTrace_append hprefix tailTrace_694432
  have hstable : (prefixWord ++ tailWord_694432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694432).length < 2 ^ (prefixWord ++ tailWord_694432).sum := by decide
  have hdescent : baseEnd_694432 < baseStart_694432 := by decide
  rcases family_descends (prefixWord ++ tailWord_694432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694453 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_694453 : Nat := 118140960795 + 694453 * 2 ^ 59
def prefixEnd_694453 : Nat := 4983230072969 + 3 ^ 40 * 694453 * 2
def baseEnd_694453 : Nat := 118862726985625561047925

theorem tailTrace_694453 : CollatzResearch.WordTrace tailWord_694453 prefixEnd_694453 118862726985625561047925 := by
  unfold tailWord_694453
  simp only [CollatzResearch.WordTrace]
  refine ⟨25328781753122858975032013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16885854502081905983354675 25328781753122858975032013)
  ·
    refine ⟨9498293157421072115637005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25328781753122858975032013 9498293157421072115637005)
    ·
      refine ⟨3561859934032902043363877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9498293157421072115637005 3561859934032902043363877)
      ·
        refine ⟨667848737631169133130727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3561859934032902043363877 667848737631169133130727)
        ·
          refine ⟨1001773106446753699696091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667848737631169133130727 1001773106446753699696091)
          ·
            refine ⟨1502659659670130549544137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001773106446753699696091 1502659659670130549544137)
            ·
              refine ⟨1126994744752597912158103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502659659670130549544137 1126994744752597912158103)
              ·
                refine ⟨1690492117128896868237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126994744752597912158103 1690492117128896868237155)
                ·
                  refine ⟨2535738175693345302355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690492117128896868237155 2535738175693345302355733)
                  ·
                    refine ⟨118862726985625561047925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2535738175693345302355733 118862726985625561047925)
                    ·
                      rfl

theorem cell23_694453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_694453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694453 prefixEnd_694453 := by exact prefixLift 694453
  have htrace : WordTrace (prefixWord ++ tailWord_694453) baseStart_694453 baseEnd_694453 := by
    simpa [prefixWord, tailWord_694453, baseEnd_694453] using wordTrace_append hprefix tailTrace_694453
  have hstable : (prefixWord ++ tailWord_694453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694453).length < 2 ^ (prefixWord ++ tailWord_694453).sum := by decide
  have hdescent : baseEnd_694453 < baseStart_694453 := by decide
  rcases family_descends (prefixWord ++ tailWord_694453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694460 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_694460 : Nat := 118140960795 + 694460 * 2 ^ 59
def prefixEnd_694460 : Nat := 4983230072969 + 3 ^ 40 * 694460 * 2
def baseEnd_694460 : Nat := 356591775321458155756243

theorem tailTrace_694460 : CollatzResearch.WordTrace tailWord_694460 prefixEnd_694460 356591775321458155756243 := by
  unfold tailWord_694460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664518532048749585268417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16886024709398332780357889 12664518532048749585268417)
  ·
    refine ⟨9498388899036562188951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12664518532048749585268417 9498388899036562188951313)
    ·
      refine ⟨7123791674277421641713485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9498388899036562188951313 7123791674277421641713485)
      ·
        refine ⟨2671421877854033115642557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7123791674277421641713485 2671421877854033115642557)
        ·
          refine ⟨1001783204195262418365959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2671421877854033115642557 1001783204195262418365959)
          ·
            refine ⟨1502674806292893627548939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001783204195262418365959 1502674806292893627548939)
            ·
              refine ⟨2254012209439340441323409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502674806292893627548939 2254012209439340441323409)
              ·
                refine ⟨1690509157079505330992557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254012209439340441323409 1690509157079505330992557)
                ·
                  refine ⟨633940933904814499122209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1690509157079505330992557 633940933904814499122209)
                  ·
                    refine ⟨475455700428610874341657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 633940933904814499122209 475455700428610874341657)
                    ·
                      refine ⟨356591775321458155756243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475455700428610874341657 356591775321458155756243)
                      ·
                        rfl

theorem cell23_694460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_694460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694460 prefixEnd_694460 := by exact prefixLift 694460
  have htrace : WordTrace (prefixWord ++ tailWord_694460) baseStart_694460 baseEnd_694460 := by
    simpa [prefixWord, tailWord_694460, baseEnd_694460] using wordTrace_append hprefix tailTrace_694460
  have hstable : (prefixWord ++ tailWord_694460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694460).length < 2 ^ (prefixWord ++ tailWord_694460).sum := by decide
  have hdescent : baseEnd_694460 < baseStart_694460 := by decide
  rcases family_descends (prefixWord ++ tailWord_694460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694536 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_694536 : Nat := 118140960795 + 694536 * 2 ^ 59
def prefixEnd_694536 : Nat := 4983230072969 + 3 ^ 40 * 694536 * 2
def baseEnd_694536 : Nat := 356630799851199858405893

theorem tailTrace_694536 : CollatzResearch.WordTrace tailWord_694536 prefixEnd_694536 356630799851199858405893 := by
  unfold tailWord_694536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665904505911082075151731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16887872674548109433535641 12665904505911082075151731)
  ·
    refine ⟨18998856758866623112727597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12665904505911082075151731 18998856758866623112727597)
    ·
      refine ⟨7124571284574983667272849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18998856758866623112727597 7124571284574983667272849)
      ·
        refine ⟨5343428463431237750454637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7124571284574983667272849 5343428463431237750454637)
        ·
          refine ⟨2003785673786714156420489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5343428463431237750454637 2003785673786714156420489)
          ·
            refine ⟨1502839255340035617315367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003785673786714156420489 1502839255340035617315367)
            ·
              refine ⟨2254258883010053425973051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502839255340035617315367 2254258883010053425973051)
              ·
                refine ⟨3381388324515080138959577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254258883010053425973051 3381388324515080138959577)
                ·
                  refine ⟨2536041243386310104219683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3381388324515080138959577 2536041243386310104219683)
                  ·
                    refine ⟨3804061865079465156329525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536041243386310104219683 3804061865079465156329525)
                    ·
                      refine ⟨356630799851199858405893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3804061865079465156329525 356630799851199858405893)
                      ·
                        rfl

theorem cell23_694536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_694536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694536 prefixEnd_694536 := by exact prefixLift 694536
  have htrace : WordTrace (prefixWord ++ tailWord_694536) baseStart_694536 baseEnd_694536 := by
    simpa [prefixWord, tailWord_694536, baseEnd_694536] using wordTrace_append hprefix tailTrace_694536
  have hstable : (prefixWord ++ tailWord_694536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694536).length < 2 ^ (prefixWord ++ tailWord_694536).sum := by decide
  have hdescent : baseEnd_694536 < baseStart_694536 := by decide
  rcases family_descends (prefixWord ++ tailWord_694536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694576 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2]
def baseStart_694576 : Nat := 118140960795 + 694576 * 2 ^ 59
def prefixEnd_694576 : Nat := 4983230072969 + 3 ^ 40 * 694576 * 2
def baseEnd_694576 : Nat := 356651339077379701905709

theorem tailTrace_694576 : CollatzResearch.WordTrace tailWord_694576 prefixEnd_694576 356651339077379701905709 := by
  unfold tailWord_694576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12666633965838625490879791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16888845287784833987839721 12666633965838625490879791)
  ·
    refine ⟨18999950948757938236319687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12666633965838625490879791 18999950948757938236319687)
    ·
      refine ⟨28499926423136907354479531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18999950948757938236319687 28499926423136907354479531)
      ·
        refine ⟨42749889634705361031719297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28499926423136907354479531 42749889634705361031719297)
        ·
          refine ⟨32062417226029020773789473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42749889634705361031719297 32062417226029020773789473)
          ·
            refine ⟨24046812919521765580342105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32062417226029020773789473 24046812919521765580342105)
            ·
              refine ⟨18035109689641324185256579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24046812919521765580342105 18035109689641324185256579)
              ·
                refine ⟨27052664534461986277884869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18035109689641324185256579 27052664534461986277884869)
                ·
                  refine ⟨5072374600211622427103413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27052664534461986277884869 5072374600211622427103413)
                  ·
                    refine ⟨475535118769839602540945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5072374600211622427103413 475535118769839602540945)
                    ·
                      refine ⟨356651339077379701905709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475535118769839602540945 356651339077379701905709)
                      ·
                        rfl

theorem cell23_694576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2].length) (baseStart_694576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694576 prefixEnd_694576 := by exact prefixLift 694576
  have htrace : WordTrace (prefixWord ++ tailWord_694576) baseStart_694576 baseEnd_694576 := by
    simpa [prefixWord, tailWord_694576, baseEnd_694576] using wordTrace_append hprefix tailTrace_694576
  have hstable : (prefixWord ++ tailWord_694576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694576).length < 2 ^ (prefixWord ++ tailWord_694576).sum := by decide
  have hdescent : baseEnd_694576 < baseStart_694576 := by decide
  rcases family_descends (prefixWord ++ tailWord_694576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694579 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_694579 : Nat := 118140960795 + 694579 * 2 ^ 59
def prefixEnd_694579 : Nat := 4983230072969 + 3 ^ 40 * 694579 * 2
def baseEnd_694579 : Nat := 356652879519343190168195

theorem tailTrace_694579 : CollatzResearch.WordTrace tailWord_694579 prefixEnd_694579 356652879519343190168195 := by
  unfold tailWord_694579
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333377350666382494118791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16888918233777588329412527 25333377350666382494118791)
  ·
    refine ⟨38000066025999573741178187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333377350666382494118791 38000066025999573741178187)
    ·
      refine ⟨57000099038999360611767281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38000066025999573741178187 57000099038999360611767281)
      ·
        refine ⟨42750074279249520458825461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57000099038999360611767281 42750074279249520458825461)
        ·
          refine ⟨4007819463679642543014887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42750074279249520458825461 4007819463679642543014887)
          ·
            refine ⟨6011729195519463814522331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007819463679642543014887 6011729195519463814522331)
            ·
              refine ⟨9017593793279195721783497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011729195519463814522331 9017593793279195721783497)
              ·
                refine ⟨6763195344959396791337623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017593793279195721783497 6763195344959396791337623)
                ·
                  refine ⟨10144793017439095187006435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763195344959396791337623 10144793017439095187006435)
                  ·
                    refine ⟨15217189526158642780509653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10144793017439095187006435 15217189526158642780509653)
                    ·
                      refine ⟨356652879519343190168195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15217189526158642780509653 356652879519343190168195)
                      ·
                        rfl

theorem cell23_694579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_694579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694579 prefixEnd_694579 := by exact prefixLift 694579
  have htrace : WordTrace (prefixWord ++ tailWord_694579) baseStart_694579 baseEnd_694579 := by
    simpa [prefixWord, tailWord_694579, baseEnd_694579] using wordTrace_append hprefix tailTrace_694579
  have hstable : (prefixWord ++ tailWord_694579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694579).length < 2 ^ (prefixWord ++ tailWord_694579).sum := by decide
  have hdescent : baseEnd_694579 < baseStart_694579 := by decide
  rcases family_descends (prefixWord ++ tailWord_694579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694586 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_694586 : Nat := 118140960795 + 694586 * 2 ^ 59
def prefixEnd_694586 : Nat := 4983230072969 + 3 ^ 40 * 694586 * 2
def baseEnd_694586 : Nat := 118885491294641554260221

theorem tailTrace_694586 : CollatzResearch.WordTrace tailWord_694586 prefixEnd_694586 118885491294641554260221 := by
  unfold tailWord_694586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333408165410255672405903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16889088441094015126415741 6333408165410255672405903)
  ·
    refine ⟨9500112248115383508608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333408165410255672405903 9500112248115383508608855)
    ·
      refine ⟨14250168372173075262913283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9500112248115383508608855 14250168372173075262913283)
      ·
        refine ⟨21375252558259612894369925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14250168372173075262913283 21375252558259612894369925)
        ·
          refine ⟨4007859854673677417694361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21375252558259612894369925 4007859854673677417694361)
          ·
            refine ⟨3005894891005258063270771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007859854673677417694361 3005894891005258063270771)
            ·
              refine ⟨4508842336507887094906157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005894891005258063270771 4508842336507887094906157)
              ·
                refine ⟨1690815876190457660589809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508842336507887094906157 1690815876190457660589809)
                ·
                  refine ⟨1268111907142843245442357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690815876190457660589809 1268111907142843245442357)
                  ·
                    refine ⟨118885491294641554260221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268111907142843245442357 118885491294641554260221)
                    ·
                      rfl

theorem cell23_694586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_694586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694586 prefixEnd_694586 := by exact prefixLift 694586
  have htrace : WordTrace (prefixWord ++ tailWord_694586) baseStart_694586 baseEnd_694586 := by
    simpa [prefixWord, tailWord_694586, baseEnd_694586] using wordTrace_append hprefix tailTrace_694586
  have hstable : (prefixWord ++ tailWord_694586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694586).length < 2 ^ (prefixWord ++ tailWord_694586).sum := by decide
  have hdescent : baseEnd_694586 < baseStart_694586 := by decide
  rcases family_descends (prefixWord ++ tailWord_694586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694606 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_694606 : Nat := 118140960795 + 694606 * 2 ^ 59
def prefixEnd_694606 : Nat := 4983230072969 + 3 ^ 40 * 694606 * 2
def baseEnd_694606 : Nat := 356666743497014584530571

theorem tailTrace_694606 : CollatzResearch.WordTrace tailWord_694606 prefixEnd_694606 356666743497014584530571 := by
  unfold tailWord_694606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166795265196070763168959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16889574747712377403567781 3166795265196070763168959)
  ·
    refine ⟨4750192897794106144753439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3166795265196070763168959 4750192897794106144753439)
    ·
      refine ⟨7125289346691159217130159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750192897794106144753439 7125289346691159217130159)
      ·
        refine ⟨10687934020036738825695239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7125289346691159217130159 10687934020036738825695239)
        ·
          refine ⟨16031901030055108238542859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10687934020036738825695239 16031901030055108238542859)
          ·
            refine ⟨24047851545082662357814289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16031901030055108238542859 24047851545082662357814289)
            ·
              refine ⟨18035888658811996768360717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24047851545082662357814289 18035888658811996768360717)
              ·
                refine ⟨6763458247054498788135269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18035888658811996768360717 6763458247054498788135269)
                ·
                  refine ⟨1268148421322718522775363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6763458247054498788135269 1268148421322718522775363)
                  ·
                    refine ⟨1902222631984077784163045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1268148421322718522775363 1902222631984077784163045)
                    ·
                      refine ⟨356666743497014584530571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1902222631984077784163045 356666743497014584530571)
                      ·
                        rfl

theorem cell23_694606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_694606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694606 prefixEnd_694606 := by exact prefixLift 694606
  have htrace : WordTrace (prefixWord ++ tailWord_694606) baseStart_694606 baseEnd_694606 := by
    simpa [prefixWord, tailWord_694606, baseEnd_694606] using wordTrace_append hprefix tailTrace_694606
  have hstable : (prefixWord ++ tailWord_694606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694606).length < 2 ^ (prefixWord ++ tailWord_694606).sum := by decide
  have hdescent : baseEnd_694606 < baseStart_694606 := by decide
  rcases family_descends (prefixWord ++ tailWord_694606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694680 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 6]
def baseStart_694680 : Nat := 118140960795 + 694680 * 2 ^ 59
def prefixEnd_694680 : Nat := 4983230072969 + 3 ^ 40 * 694680 * 2
def baseEnd_694680 : Nat := 39633860118383032778359

theorem tailTrace_694680 : CollatzResearch.WordTrace tailWord_694680 prefixEnd_694680 39633860118383032778359 := by
  unfold tailWord_694680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668530561650238371772747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16891374082200317829030329 12668530561650238371772747)
  ·
    refine ⟨19002795842475357557659121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12668530561650238371772747 19002795842475357557659121)
    ·
      refine ⟨14252096881856518168244341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19002795842475357557659121 14252096881856518168244341)
      ·
        refine ⟨1336134082674048578272907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14252096881856518168244341 1336134082674048578272907)
        ·
          refine ⟨2004201124011072867409361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336134082674048578272907 2004201124011072867409361)
          ·
            refine ⟨1503150843008304650557021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004201124011072867409361 1503150843008304650557021)
            ·
              refine ⟨563681566128114243958883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503150843008304650557021 563681566128114243958883)
              ·
                refine ⟨845522349192171365938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563681566128114243958883 845522349192171365938325)
                ·
                  refine ⟨39633860118383032778359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 845522349192171365938325 39633860118383032778359)
                  ·
                    rfl

theorem cell23_694680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_694680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694680 prefixEnd_694680 := by exact prefixLift 694680
  have htrace : WordTrace (prefixWord ++ tailWord_694680) baseStart_694680 baseEnd_694680 := by
    simpa [prefixWord, tailWord_694680, baseEnd_694680] using wordTrace_append hprefix tailTrace_694680
  have hstable : (prefixWord ++ tailWord_694680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694680).length < 2 ^ (prefixWord ++ tailWord_694680).sum := by decide
  have hdescent : baseEnd_694680 < baseStart_694680 := by decide
  rcases family_descends (prefixWord ++ tailWord_694680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694690 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_694690 : Nat := 118140960795 + 694690 * 2 ^ 59
def prefixEnd_694690 : Nat := 4983230072969 + 3 ^ 40 * 694690 * 2
def baseEnd_694690 : Nat := 356709875871992255880185

theorem tailTrace_694690 : CollatzResearch.WordTrace tailWord_694690 prefixEnd_694690 356709875871992255880185 := by
  unfold tailWord_694690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334356463316062112852381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16891617235509498967606349 6334356463316062112852381)
  ·
    refine ⟨2375383673743523292319643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6334356463316062112852381 2375383673743523292319643)
    ·
      refine ⟨3563075510615284938479465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375383673743523292319643 3563075510615284938479465)
      ·
        refine ⟨2672306632961463703859599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3563075510615284938479465 2672306632961463703859599)
        ·
          refine ⟨4008459949442195555789399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672306632961463703859599 4008459949442195555789399)
          ·
            refine ⟨6012689924163293333684099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008459949442195555789399 6012689924163293333684099)
            ·
              refine ⟨9019034886244940000526149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012689924163293333684099 9019034886244940000526149)
              ·
                refine ⟨1691069041170926250098653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9019034886244940000526149 1691069041170926250098653)
                ·
                  refine ⟨634150890439097343786995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691069041170926250098653 634150890439097343786995)
                  ·
                    refine ⟨951226335658646015680493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634150890439097343786995 951226335658646015680493)
                    ·
                      refine ⟨356709875871992255880185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951226335658646015680493 356709875871992255880185)
                      ·
                        rfl

theorem cell23_694690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_694690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694690 prefixEnd_694690 := by exact prefixLift 694690
  have htrace : WordTrace (prefixWord ++ tailWord_694690) baseStart_694690 baseEnd_694690 := by
    simpa [prefixWord, tailWord_694690, baseEnd_694690] using wordTrace_append hprefix tailTrace_694690
  have hstable : (prefixWord ++ tailWord_694690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694690).length < 2 ^ (prefixWord ++ tailWord_694690).sum := by decide
  have hdescent : baseEnd_694690 < baseStart_694690 := by decide
  rcases family_descends (prefixWord ++ tailWord_694690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694693 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_694693 : Nat := 118140960795 + 694693 * 2 ^ 59
def prefixEnd_694693 : Nat := 4983230072969 + 3 ^ 40 * 694693 * 2
def baseEnd_694693 : Nat := 118903805437985248047557

theorem tailTrace_694693 : CollatzResearch.WordTrace tailWord_694693 prefixEnd_694693 118903805437985248047557 := by
  unfold tailWord_694693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337535272253379963768733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16891690181502253309179155 25337535272253379963768733)
  ·
    refine ⟨9501575727095017486413275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25337535272253379963768733 9501575727095017486413275)
    ·
      refine ⟨14252363590642526229619913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9501575727095017486413275 14252363590642526229619913)
      ·
        refine ⟨10689272692981894672214935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14252363590642526229619913 10689272692981894672214935)
        ·
          refine ⟨16033909039472842008322403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689272692981894672214935 16033909039472842008322403)
          ·
            refine ⟨24050863559209263012483605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16033909039472842008322403 24050863559209263012483605)
            ·
              refine ⟨1127384229337934203710169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24050863559209263012483605 1127384229337934203710169)
              ·
                refine ⟨845538172003450652782627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127384229337934203710169 845538172003450652782627)
                ·
                  refine ⟨1268307258005175979173941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845538172003450652782627 1268307258005175979173941)
                  ·
                    refine ⟨118903805437985248047557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268307258005175979173941 118903805437985248047557)
                    ·
                      rfl

theorem cell23_694693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_694693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694693 prefixEnd_694693 := by exact prefixLift 694693
  have htrace : WordTrace (prefixWord ++ tailWord_694693) baseStart_694693 baseEnd_694693 := by
    simpa [prefixWord, tailWord_694693, baseEnd_694693] using wordTrace_append hprefix tailTrace_694693
  have hstable : (prefixWord ++ tailWord_694693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694693).length < 2 ^ (prefixWord ++ tailWord_694693).sum := by decide
  have hdescent : baseEnd_694693 < baseStart_694693 := by decide
  rcases family_descends (prefixWord ++ tailWord_694693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694701 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_694701 : Nat := 118140960795 + 694701 * 2 ^ 59
def prefixEnd_694701 : Nat := 4983230072969 + 3 ^ 40 * 694701 * 2
def baseEnd_694701 : Nat := 118905174719730570947545

theorem tailTrace_694701 : CollatzResearch.WordTrace tailWord_694701 prefixEnd_694701 118905174719730570947545 := by
  unfold tailWord_694701
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337827056224397330059957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16891884704149598220039971 25337827056224397330059957)
  ·
    refine ⟨2375421286521037249693121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25337827056224397330059957 2375421286521037249693121)
    ·
      refine ⟨1781565964890777937269841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375421286521037249693121 1781565964890777937269841)
      ·
        refine ⟨1336174473668083452952381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781565964890777937269841 1336174473668083452952381)
        ·
          refine ⟨501065427625531294857143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1336174473668083452952381 501065427625531294857143)
          ·
            refine ⟨751598141438296942285715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501065427625531294857143 751598141438296942285715)
            ·
              refine ⟨1127397212157445413428573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751598141438296942285715 1127397212157445413428573)
              ·
                refine ⟨422773954559042030035715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127397212157445413428573 422773954559042030035715)
                ·
                  refine ⟨634160931838563045053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422773954559042030035715 634160931838563045053573)
                  ·
                    refine ⟨118905174719730570947545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634160931838563045053573 118905174719730570947545)
                    ·
                      rfl

theorem cell23_694701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_694701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694701 prefixEnd_694701 := by exact prefixLift 694701
  have htrace : WordTrace (prefixWord ++ tailWord_694701) baseStart_694701 baseEnd_694701 := by
    simpa [prefixWord, tailWord_694701, baseEnd_694701] using wordTrace_append hprefix tailTrace_694701
  have hstable : (prefixWord ++ tailWord_694701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694701).length < 2 ^ (prefixWord ++ tailWord_694701).sum := by decide
  have hdescent : baseEnd_694701 < baseStart_694701 := by decide
  rcases family_descends (prefixWord ++ tailWord_694701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694706 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_694706 : Nat := 118140960795 + 694706 * 2 ^ 59
def prefixEnd_694706 : Nat := 4983230072969 + 3 ^ 40 * 694706 * 2
def baseEnd_694706 : Nat := 118906030520821397760037

theorem tailTrace_694706 : CollatzResearch.WordTrace tailWord_694706 prefixEnd_694706 118906030520821397760037 := by
  unfold tailWord_694706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334502355301570795997993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16892006280804188789327981 6334502355301570795997993)
  ·
    refine ⟨4750876766476178096998495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6334502355301570795997993 4750876766476178096998495)
    ·
      refine ⟨7126315149714267145497743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750876766476178096998495 7126315149714267145497743)
      ·
        refine ⟨10689472724571400718246615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7126315149714267145497743 10689472724571400718246615)
        ·
          refine ⟨16034209086857101077369923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689472724571400718246615 16034209086857101077369923)
          ·
            refine ⟨24051313630285651616054885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16034209086857101077369923 24051313630285651616054885)
            ·
              refine ⟨4509621305678559678010291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24051313630285651616054885 4509621305678559678010291)
              ·
                refine ⟨6764431958517839517015437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509621305678559678010291 6764431958517839517015437)
                ·
                  refine ⟨2536661984444189818880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6764431958517839517015437 2536661984444189818880789)
                  ·
                    refine ⟨118906030520821397760037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2536661984444189818880789 118906030520821397760037)
                    ·
                      rfl

theorem cell23_694706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_694706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694706 prefixEnd_694706 := by exact prefixLift 694706
  have htrace : WordTrace (prefixWord ++ tailWord_694706) baseStart_694706 baseEnd_694706 := by
    simpa [prefixWord, tailWord_694706, baseEnd_694706] using wordTrace_append hprefix tailTrace_694706
  have hstable : (prefixWord ++ tailWord_694706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694706).length < 2 ^ (prefixWord ++ tailWord_694706).sum := by decide
  have hdescent : baseEnd_694706 < baseStart_694706 := by decide
  rcases family_descends (prefixWord ++ tailWord_694706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694723 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 2, 4]
def baseStart_694723 : Nat := 118140960795 + 694723 * 2 ^ 59
def prefixEnd_694723 : Nat := 4983230072969 + 3 ^ 40 * 694723 * 2
def baseEnd_694723 : Nat := 118908940244530208922511

theorem tailTrace_694723 : CollatzResearch.WordTrace tailWord_694723 prefixEnd_694723 118908940244530208922511 := by
  unfold tailWord_694723
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338629462144695087360823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892419641429796724907215 25338629462144695087360823)
  ·
    refine ⟨38007944193217042631041235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25338629462144695087360823 38007944193217042631041235)
    ·
      refine ⟨57011916289825563946561853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38007944193217042631041235 57011916289825563946561853)
      ·
        refine ⟨21379468608684586479960695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57011916289825563946561853 21379468608684586479960695)
        ·
          refine ⟨32069202913026879719941043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21379468608684586479960695 32069202913026879719941043)
          ·
            refine ⟨48103804369540319579911565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32069202913026879719941043 48103804369540319579911565)
            ·
              refine ⟨18038926638577619842466837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48103804369540319579911565 18038926638577619842466837)
              ·
                refine ⟨845574686183325930115633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18038926638577619842466837 845574686183325930115633)
                ·
                  refine ⟨634181014637494447586725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 845574686183325930115633 634181014637494447586725)
                  ·
                    refine ⟨118908940244530208922511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634181014637494447586725 118908940244530208922511)
                    ·
                      rfl

theorem cell23_694723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 4].length) (baseStart_694723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694723 prefixEnd_694723 := by exact prefixLift 694723
  have htrace : WordTrace (prefixWord ++ tailWord_694723) baseStart_694723 baseEnd_694723 := by
    simpa [prefixWord, tailWord_694723, baseEnd_694723] using wordTrace_append hprefix tailTrace_694723
  have hstable : (prefixWord ++ tailWord_694723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694723).length < 2 ^ (prefixWord ++ tailWord_694723).sum := by decide
  have hdescent : baseEnd_694723 < baseStart_694723 := by decide
  rcases family_descends (prefixWord ++ tailWord_694723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694724 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_694724 : Nat := 118140960795 + 694724 * 2 ^ 59
def prefixEnd_694724 : Nat := 4983230072969 + 3 ^ 40 * 694724 * 2
def baseEnd_694724 : Nat := 356727334214245122855029

theorem tailTrace_694724 : CollatzResearch.WordTrace tailWord_694724 prefixEnd_694724 356727334214245122855029 := by
  unfold tailWord_694724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669332967570536129073613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16892443956760714838764817 12669332967570536129073613)
  ·
    refine ⟨4750999862838951048402605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12669332967570536129073613 4750999862838951048402605)
    ·
      refine ⟨1781624948564606643150977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4750999862838951048402605 1781624948564606643150977)
      ·
        refine ⟨1336218711423454982363233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781624948564606643150977 1336218711423454982363233)
        ·
          refine ⟨1002164033567591236772425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336218711423454982363233 1002164033567591236772425)
          ·
            refine ⟨751623025175693427579319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002164033567591236772425 751623025175693427579319)
            ·
              refine ⟨1127434537763540141368979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751623025175693427579319 1127434537763540141368979)
              ·
                refine ⟨1691151806645310212053469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127434537763540141368979 1691151806645310212053469)
                ·
                  refine ⟨634181927491991329520051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691151806645310212053469 634181927491991329520051)
                  ·
                    refine ⟨951272891237986994280077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634181927491991329520051 951272891237986994280077)
                    ·
                      refine ⟨356727334214245122855029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951272891237986994280077 356727334214245122855029)
                      ·
                        rfl

theorem cell23_694724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_694724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694724 prefixEnd_694724 := by exact prefixLift 694724
  have htrace : WordTrace (prefixWord ++ tailWord_694724) baseStart_694724 baseEnd_694724 := by
    simpa [prefixWord, tailWord_694724, baseEnd_694724] using wordTrace_append hprefix tailTrace_694724
  have hstable : (prefixWord ++ tailWord_694724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694724).length < 2 ^ (prefixWord ++ tailWord_694724).sum := by decide
  have hdescent : baseEnd_694724 < baseStart_694724 := by decide
  rcases family_descends (prefixWord ++ tailWord_694724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694763 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3]
def baseStart_694763 : Nat := 118140960795 + 694763 * 2 ^ 59
def prefixEnd_694763 : Nat := 4983230072969 + 3 ^ 40 * 694763 * 2
def baseEnd_694763 : Nat := 356747359959770470267349

theorem tailTrace_694763 : CollatzResearch.WordTrace tailWord_694763 prefixEnd_694763 356747359959770470267349 := by
  unfold tailWord_694763
  simp only [CollatzResearch.WordTrace]
  refine ⟨25340088381999781918816943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16893392254666521279211295 25340088381999781918816943)
  ·
    refine ⟨38010132572999672878225415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25340088381999781918816943 38010132572999672878225415)
    ·
      refine ⟨57015198859499509317338123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38010132572999672878225415 57015198859499509317338123)
      ·
        refine ⟨85522798289249263976007185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57015198859499509317338123 85522798289249263976007185)
        ·
          refine ⟨64142098716936947982005389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85522798289249263976007185 64142098716936947982005389)
          ·
            refine ⟨24053287018851355493252021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64142098716936947982005389 24053287018851355493252021)
            ·
              refine ⟨2254995658017314577492377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24053287018851355493252021 2254995658017314577492377)
              ·
                refine ⟨1691246743512985933119283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254995658017314577492377 1691246743512985933119283)
                ·
                  refine ⟨2536870115269478899678925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691246743512985933119283 2536870115269478899678925)
                  ·
                    refine ⟨951326293226054587379597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536870115269478899678925 951326293226054587379597)
                    ·
                      refine ⟨356747359959770470267349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951326293226054587379597 356747359959770470267349)
                      ·
                        rfl

theorem cell23_694763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].length) (baseStart_694763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694763 prefixEnd_694763 := by exact prefixLift 694763
  have htrace : WordTrace (prefixWord ++ tailWord_694763) baseStart_694763 baseEnd_694763 := by
    simpa [prefixWord, tailWord_694763, baseEnd_694763] using wordTrace_append hprefix tailTrace_694763
  have hstable : (prefixWord ++ tailWord_694763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694763).length < 2 ^ (prefixWord ++ tailWord_694763).sum := by decide
  have hdescent : baseEnd_694763 < baseStart_694763 := by decide
  rcases family_descends (prefixWord ++ tailWord_694763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694824 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_694824 : Nat := 118140960795 + 694824 * 2 ^ 59
def prefixEnd_694824 : Nat := 4983230072969 + 3 ^ 40 * 694824 * 2
def baseEnd_694824 : Nat := 356778682279694731604569

theorem tailTrace_694824 : CollatzResearch.WordTrace tailWord_694824 prefixEnd_694824 356778682279694731604569 := by
  unfold tailWord_694824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671156617389394668393763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16894875489852526224525017 12671156617389394668393763)
  ·
    refine ⟨19006734926084092002590645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671156617389394668393763 19006734926084092002590645)
    ·
      refine ⟨1781881399320383625242873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19006734926084092002590645 1781881399320383625242873)
      ·
        refine ⟨1336411049490287718932155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781881399320383625242873 1336411049490287718932155)
        ·
          refine ⟨2004616574235431578398233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336411049490287718932155 2004616574235431578398233)
          ·
            refine ⟨1503462430676573683798675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004616574235431578398233 1503462430676573683798675)
            ·
              refine ⟨2255193646014860525698013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503462430676573683798675 2255193646014860525698013)
              ·
                refine ⟨845697617255572697136755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255193646014860525698013 845697617255572697136755)
                ·
                  refine ⟨1268546425883359045705133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845697617255572697136755 1268546425883359045705133)
                  ·
                    refine ⟨475704909706259642139425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268546425883359045705133 475704909706259642139425)
                    ·
                      refine ⟨356778682279694731604569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475704909706259642139425 356778682279694731604569)
                      ·
                        rfl

theorem cell23_694824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_694824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694824 prefixEnd_694824 := by exact prefixLift 694824
  have htrace : WordTrace (prefixWord ++ tailWord_694824) baseStart_694824 baseEnd_694824 := by
    simpa [prefixWord, tailWord_694824, baseEnd_694824] using wordTrace_append hprefix tailTrace_694824
  have hstable : (prefixWord ++ tailWord_694824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694824).length < 2 ^ (prefixWord ++ tailWord_694824).sum := by decide
  have hdescent : baseEnd_694824 < baseStart_694824 := by decide
  rcases family_descends (prefixWord ++ tailWord_694824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694833 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_694833 : Nat := 118140960795 + 694833 * 2 ^ 59
def prefixEnd_694833 : Nat := 4983230072969 + 3 ^ 40 * 694833 * 2
def baseEnd_694833 : Nat := 356783303605585196392027

theorem tailTrace_694833 : CollatzResearch.WordTrace tailWord_694833 prefixEnd_694833 356783303605585196392027 := by
  unfold tailWord_694833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342641491746183873865153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16895094327830789249243435 25342641491746183873865153)
  ·
    refine ⟨19006981118809637905398865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25342641491746183873865153 19006981118809637905398865)
    ·
      refine ⟨14255235839107228429049149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19006981118809637905398865 14255235839107228429049149)
      ·
        refine ⟨5345713439665210660893431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14255235839107228429049149 5345713439665210660893431)
        ·
          refine ⟨8018570159497815991340147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345713439665210660893431 8018570159497815991340147)
          ·
            refine ⟨12027855239246723987010221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8018570159497815991340147 12027855239246723987010221)
            ·
              refine ⟨4510445714717521495128833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12027855239246723987010221 4510445714717521495128833)
              ·
                refine ⟨3382834286038141121346625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510445714717521495128833 3382834286038141121346625)
                ·
                  refine ⟨2537125714528605841009969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382834286038141121346625 2537125714528605841009969)
                  ·
                    refine ⟨1902844285896454380757477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537125714528605841009969 1902844285896454380757477)
                    ·
                      refine ⟨356783303605585196392027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1902844285896454380757477 356783303605585196392027)
                      ·
                        rfl

theorem cell23_694833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_694833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694833 prefixEnd_694833 := by exact prefixLift 694833
  have htrace : WordTrace (prefixWord ++ tailWord_694833) baseStart_694833 baseEnd_694833 := by
    simpa [prefixWord, tailWord_694833, baseEnd_694833] using wordTrace_append hprefix tailTrace_694833
  have hstable : (prefixWord ++ tailWord_694833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694833).length < 2 ^ (prefixWord ++ tailWord_694833).sum := by decide
  have hdescent : baseEnd_694833 < baseStart_694833 := by decide
  rcases family_descends (prefixWord ++ tailWord_694833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694837 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_694837 : Nat := 118140960795 + 694837 * 2 ^ 59
def prefixEnd_694837 : Nat := 4983230072969 + 3 ^ 40 * 694837 * 2
def baseEnd_694837 : Nat := 356785357528203180742009

theorem tailTrace_694837 : CollatzResearch.WordTrace tailWord_694837 prefixEnd_694837 356785357528203180742009 := by
  unfold tailWord_694837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342787383731692557010765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16895191589154461704673843 25342787383731692557010765)
  ·
    refine ⟨9503545268899384708879037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25342787383731692557010765 9503545268899384708879037)
    ·
      refine ⟨3563829475837269265829639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9503545268899384708879037 3563829475837269265829639)
      ·
        refine ⟨5345744213755903898744459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563829475837269265829639 5345744213755903898744459)
        ·
          refine ⟨8018616320633855848116689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345744213755903898744459 8018616320633855848116689)
          ·
            refine ⟨6013962240475391886087517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8018616320633855848116689 6013962240475391886087517)
            ·
              refine ⟨2255235840178271957282819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013962240475391886087517 2255235840178271957282819)
              ·
                refine ⟨3382853760267407935924229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255235840178271957282819 3382853760267407935924229)
                ·
                  refine ⟨634285080050138987985793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3382853760267407935924229 634285080050138987985793)
                  ·
                    refine ⟨475713810037604240989345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634285080050138987985793 475713810037604240989345)
                    ·
                      refine ⟨356785357528203180742009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475713810037604240989345 356785357528203180742009)
                      ·
                        rfl

theorem cell23_694837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_694837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694837 prefixEnd_694837 := by exact prefixLift 694837
  have htrace : WordTrace (prefixWord ++ tailWord_694837) baseStart_694837 baseEnd_694837 := by
    simpa [prefixWord, tailWord_694837, baseEnd_694837] using wordTrace_append hprefix tailTrace_694837
  have hstable : (prefixWord ++ tailWord_694837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694837).length < 2 ^ (prefixWord ++ tailWord_694837).sum := by decide
  have hdescent : baseEnd_694837 < baseStart_694837 := by decide
  rcases family_descends (prefixWord ++ tailWord_694837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694883 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_694883 : Nat := 118140960795 + 694883 * 2 ^ 59
def prefixEnd_694883 : Nat := 4983230072969 + 3 ^ 40 * 694883 * 2
def baseEnd_694883 : Nat := 356808977638310000766797

theorem tailTrace_694883 : CollatzResearch.WordTrace tailWord_694883 prefixEnd_694883 356808977638310000766797 := by
  unfold tailWord_694883
  simp only [CollatzResearch.WordTrace]
  refine ⟨25344465141565042413185303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16896310094376694942123535 25344465141565042413185303)
  ·
    refine ⟨38016697712347563619777955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25344465141565042413185303 38016697712347563619777955)
    ·
      refine ⟨57025046568521345429666933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38016697712347563619777955 57025046568521345429666933)
      ·
        refine ⟨5346098115798876134031275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57025046568521345429666933 5346098115798876134031275)
        ·
          refine ⟨8019147173698314201046913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346098115798876134031275 8019147173698314201046913)
          ·
            refine ⟨6014360380273735650785185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8019147173698314201046913 6014360380273735650785185)
            ·
              refine ⟨4510770285205301738088889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014360380273735650785185 4510770285205301738088889)
              ·
                refine ⟨3383077713903976303566667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510770285205301738088889 3383077713903976303566667)
                ·
                  refine ⟨5074616570855964455350001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383077713903976303566667 5074616570855964455350001)
                  ·
                    refine ⟨3805962428141973341512501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074616570855964455350001 3805962428141973341512501)
                    ·
                      refine ⟨356808977638310000766797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3805962428141973341512501 356808977638310000766797)
                      ·
                        rfl

theorem cell23_694883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_694883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694883 prefixEnd_694883 := by exact prefixLift 694883
  have htrace : WordTrace (prefixWord ++ tailWord_694883) baseStart_694883 baseEnd_694883 := by
    simpa [prefixWord, tailWord_694883, baseEnd_694883] using wordTrace_append hprefix tailTrace_694883
  have hstable : (prefixWord ++ tailWord_694883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694883).length < 2 ^ (prefixWord ++ tailWord_694883).sum := by decide
  have hdescent : baseEnd_694883 < baseStart_694883 := by decide
  rcases family_descends (prefixWord ++ tailWord_694883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694890 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_694890 : Nat := 118140960795 + 694890 * 2 ^ 59
def prefixEnd_694890 : Nat := 4983230072969 + 3 ^ 40 * 694890 * 2
def baseEnd_694890 : Nat := 118937524000963824459755

theorem tailTrace_694890 : CollatzResearch.WordTrace tailWord_694890 prefixEnd_694890 118937524000963824459755 := by
  unfold tailWord_694890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336180113134920652172531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16896480301693121739126749 6336180113134920652172531)
  ·
    refine ⟨9504270169702380978258797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6336180113134920652172531 9504270169702380978258797)
    ·
      refine ⟨3564101313638392866847049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9504270169702380978258797 3564101313638392866847049)
      ·
        refine ⟨2673075985228794650135287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564101313638392866847049 2673075985228794650135287)
        ·
          refine ⟨4009613977843191975202931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673075985228794650135287 4009613977843191975202931)
          ·
            refine ⟨6014420966764787962804397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009613977843191975202931 6014420966764787962804397)
            ·
              refine ⟨2255407862536795486051649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6014420966764787962804397 2255407862536795486051649)
              ·
                refine ⟨1691555896902596614538737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255407862536795486051649 1691555896902596614538737)
                ·
                  refine ⟨1268666922676947460904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691555896902596614538737 1268666922676947460904053)
                  ·
                    refine ⟨118937524000963824459755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268666922676947460904053 118937524000963824459755)
                    ·
                      rfl

theorem cell23_694890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_694890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694890 prefixEnd_694890 := by exact prefixLift 694890
  have htrace : WordTrace (prefixWord ++ tailWord_694890) baseStart_694890 baseEnd_694890 := by
    simpa [prefixWord, tailWord_694890, baseEnd_694890] using wordTrace_append hprefix tailTrace_694890
  have hstable : (prefixWord ++ tailWord_694890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694890).length < 2 ^ (prefixWord ++ tailWord_694890).sum := by decide
  have hdescent : baseEnd_694890 < baseStart_694890 := by decide
  rcases family_descends (prefixWord ++ tailWord_694890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694894 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_694894 : Nat := 118140960795 + 694894 * 2 ^ 59
def prefixEnd_694894 : Nat := 4983230072969 + 3 ^ 40 * 694894 * 2
def baseEnd_694894 : Nat := 39646069547278828636583

theorem tailTrace_694894 : CollatzResearch.WordTrace tailWord_694894 prefixEnd_694894 39646069547278828636583 := by
  unfold tailWord_694894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168108293065648911479467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16896577563016794194557157 3168108293065648911479467)
  ·
    refine ⟨4752162439598473367219201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3168108293065648911479467 4752162439598473367219201)
    ·
      refine ⟨3564121829698855025414401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4752162439598473367219201 3564121829698855025414401)
      ·
        refine ⟨2673091372274141269060801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564121829698855025414401 2673091372274141269060801)
        ·
          refine ⟨2004818529205605951795601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673091372274141269060801 2004818529205605951795601)
          ·
            refine ⟨1503613896904204463846701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004818529205605951795601 1503613896904204463846701)
            ·
              refine ⟨563855211339076673942513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503613896904204463846701 563855211339076673942513)
              ·
                refine ⟨422891408504307505456885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563855211339076673942513 422891408504307505456885)
                ·
                  refine ⟨39646069547278828636583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 422891408504307505456885 39646069547278828636583)
                  ·
                    rfl

theorem cell23_694894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_694894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694894 prefixEnd_694894 := by exact prefixLift 694894
  have htrace : WordTrace (prefixWord ++ tailWord_694894) baseStart_694894 baseEnd_694894 := by
    simpa [prefixWord, tailWord_694894, baseEnd_694894] using wordTrace_append hprefix tailTrace_694894
  have hstable : (prefixWord ++ tailWord_694894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694894).length < 2 ^ (prefixWord ++ tailWord_694894).sum := by decide
  have hdescent : baseEnd_694894 < baseStart_694894 := by decide
  rcases family_descends (prefixWord ++ tailWord_694894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694937 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 1, 4]
def baseStart_694937 : Nat := 118140960795 + 694937 * 2 ^ 59
def prefixEnd_694937 : Nat := 4983230072969 + 3 ^ 40 * 694937 * 2
def baseEnd_694937 : Nat := 118945568531217596497183

theorem tailTrace_694937 : CollatzResearch.WordTrace tailWord_694937 prefixEnd_694937 118945568531217596497183 := by
  unfold tailWord_694937
  simp only [CollatzResearch.WordTrace]
  refine ⟨25346434683369409635651065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16897623122246273090434043 25346434683369409635651065)
  ·
    refine ⟨19009826012527057226738299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25346434683369409635651065 19009826012527057226738299)
    ·
      refine ⟨28514739018790585840107449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19009826012527057226738299 28514739018790585840107449)
      ·
        refine ⟨21386054264092939380080587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28514739018790585840107449 21386054264092939380080587)
        ·
          refine ⟨32079081396139409070120881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21386054264092939380080587 32079081396139409070120881)
          ·
            refine ⟨24059311047104556802590661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32079081396139409070120881 24059311047104556802590661)
            ·
              refine ⟨4511120821332104400485749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24059311047104556802590661 4511120821332104400485749)
              ·
                refine ⟨422917576999884787545539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4511120821332104400485749 422917576999884787545539)
                ·
                  refine ⟨634376365499827181318309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422917576999884787545539 634376365499827181318309)
                  ·
                    refine ⟨118945568531217596497183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634376365499827181318309 118945568531217596497183)
                    ·
                      rfl

theorem cell23_694937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_694937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_694937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_694937 prefixEnd_694937 := by exact prefixLift 694937
  have htrace : WordTrace (prefixWord ++ tailWord_694937) baseStart_694937 baseEnd_694937 := by
    simpa [prefixWord, tailWord_694937, baseEnd_694937] using wordTrace_append hprefix tailTrace_694937
  have hstable : (prefixWord ++ tailWord_694937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694937).length < 2 ^ (prefixWord ++ tailWord_694937).sum := by decide
  have hdescent : baseEnd_694937 < baseStart_694937 := by decide
  rcases family_descends (prefixWord ++ tailWord_694937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695011 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 1, 1, 3]
def baseStart_695011 : Nat := 118140960795 + 695011 * 2 ^ 59
def prefixEnd_695011 : Nat := 4983230072969 + 3 ^ 40 * 695011 * 2
def baseEnd_695011 : Nat := 356874703162085499966209

theorem tailTrace_695011 : CollatzResearch.WordTrace tailWord_695011 prefixEnd_695011 356874703162085499966209 := by
  unfold tailWord_695011
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349133685101320273844887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16899422456734213515896591 25349133685101320273844887)
  ·
    refine ⟨38023700527651980410767331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25349133685101320273844887 38023700527651980410767331)
    ·
      refine ⟨57035550791477970616150997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38023700527651980410767331 57035550791477970616150997)
      ·
        refine ⟨1336770721675264936316039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57035550791477970616150997 1336770721675264936316039)
        ·
          refine ⟨2005156082512897404474059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336770721675264936316039 2005156082512897404474059)
          ·
            refine ⟨3007734123769346106711089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005156082512897404474059 3007734123769346106711089)
            ·
              refine ⟨2255800592827009580033317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007734123769346106711089 2255800592827009580033317)
              ·
                refine ⟨422962611155064296256247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2255800592827009580033317 422962611155064296256247)
                ·
                  refine ⟨634443916732596444384371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422962611155064296256247 634443916732596444384371)
                  ·
                    refine ⟨951665875098894666576557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634443916732596444384371 951665875098894666576557)
                    ·
                      refine ⟨356874703162085499966209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951665875098894666576557 356874703162085499966209)
                      ·
                        rfl

theorem cell23_695011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_695011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695011 prefixEnd_695011 := by exact prefixLift 695011
  have htrace : WordTrace (prefixWord ++ tailWord_695011) baseStart_695011 baseEnd_695011 := by
    simpa [prefixWord, tailWord_695011, baseEnd_695011] using wordTrace_append hprefix tailTrace_695011
  have hstable : (prefixWord ++ tailWord_695011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695011).length < 2 ^ (prefixWord ++ tailWord_695011).sum := by decide
  have hdescent : baseEnd_695011 < baseStart_695011 := by decide
  rcases family_descends (prefixWord ++ tailWord_695011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695034 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_695034 : Nat := 118140960795 + 695034 * 2 ^ 59
def prefixEnd_695034 : Nat := 4983230072969 + 3 ^ 40 * 695034 * 2
def baseEnd_695034 : Nat := 356886513217138909978603

theorem tailTrace_695034 : CollatzResearch.WordTrace tailWord_695034 prefixEnd_695034 356886513217138909978603 := by
  unfold tailWord_695034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337493141004498800483039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16899981709345330134621437 6337493141004498800483039)
  ·
    refine ⟨9506239711506748200724559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337493141004498800483039 9506239711506748200724559)
    ·
      refine ⟨14259359567260122301086839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9506239711506748200724559 14259359567260122301086839)
      ·
        refine ⟨21389039350890183451630259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14259359567260122301086839 21389039350890183451630259)
        ·
          refine ⟨32083559026335275177445389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21389039350890183451630259 32083559026335275177445389)
          ·
            refine ⟨12031334634875728191542021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32083559026335275177445389 12031334634875728191542021)
            ·
              refine ⟨2255875244039199035914129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12031334634875728191542021 2255875244039199035914129)
              ·
                refine ⟨1691906433029399276935597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255875244039199035914129 1691906433029399276935597)
                ·
                  refine ⟨634464912386024728850849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691906433029399276935597 634464912386024728850849)
                  ·
                    refine ⟨475848684289518546638137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634464912386024728850849 475848684289518546638137)
                    ·
                      refine ⟨356886513217138909978603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475848684289518546638137 356886513217138909978603)
                      ·
                        rfl

theorem cell23_695034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_695034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695034 prefixEnd_695034 := by exact prefixLift 695034
  have htrace : WordTrace (prefixWord ++ tailWord_695034) baseStart_695034 baseEnd_695034 := by
    simpa [prefixWord, tailWord_695034, baseEnd_695034] using wordTrace_append hprefix tailTrace_695034
  have hstable : (prefixWord ++ tailWord_695034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695034).length < 2 ^ (prefixWord ++ tailWord_695034).sum := by decide
  have hdescent : baseEnd_695034 < baseStart_695034 := by decide
  rcases family_descends (prefixWord ++ tailWord_695034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695084 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_695084 : Nat := 118140960795 + 695084 * 2 ^ 59
def prefixEnd_695084 : Nat := 4983230072969 + 3 ^ 40 * 695084 * 2
def baseEnd_695084 : Nat := 356912187249863714353373

theorem tailTrace_695084 : CollatzResearch.WordTrace tailWord_695084 prefixEnd_695084 356912187249863714353373 := by
  unfold tailWord_695084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675898106918426870626153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16901197475891235827501537 12675898106918426870626153)
  ·
    refine ⟨9506923580188820152969615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12675898106918426870626153 9506923580188820152969615)
    ·
      refine ⟨14260385370283230229454423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9506923580188820152969615 14260385370283230229454423)
      ·
        refine ⟨21390578055424845344181635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14260385370283230229454423 21390578055424845344181635)
        ·
          refine ⟨32085867083137268016272453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21390578055424845344181635 32085867083137268016272453)
          ·
            refine ⟨6016100078088237753051085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32085867083137268016272453 6016100078088237753051085)
            ·
              refine ⟨2256037529283089157394157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6016100078088237753051085 2256037529283089157394157)
              ·
                refine ⟨846014073481158434022809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256037529283089157394157 846014073481158434022809)
                ·
                  refine ⟨634510555110868825517107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846014073481158434022809 634510555110868825517107)
                  ·
                    refine ⟨951765832666303238275661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634510555110868825517107 951765832666303238275661)
                    ·
                      refine ⟨356912187249863714353373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951765832666303238275661 356912187249863714353373)
                      ·
                        rfl

theorem cell23_695084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_695084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695084 prefixEnd_695084 := by exact prefixLift 695084
  have htrace : WordTrace (prefixWord ++ tailWord_695084) baseStart_695084 baseEnd_695084 := by
    simpa [prefixWord, tailWord_695084, baseEnd_695084] using wordTrace_append hprefix tailTrace_695084
  have hstable : (prefixWord ++ tailWord_695084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695084).length < 2 ^ (prefixWord ++ tailWord_695084).sum := by decide
  have hdescent : baseEnd_695084 < baseStart_695084 := by decide
  rcases family_descends (prefixWord ++ tailWord_695084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695085 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_695085 : Nat := 118140960795 + 695085 * 2 ^ 59
def prefixEnd_695085 : Nat := 4983230072969 + 3 ^ 40 * 695085 * 2
def baseEnd_695085 : Nat := 356912700730518210440869

theorem tailTrace_695085 : CollatzResearch.WordTrace tailWord_695085 prefixEnd_695085 356912700730518210440869 := by
  unfold tailWord_695085
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351832686833230912038709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16901221791222153941359139 25351832686833230912038709)
  ·
    refine ⟨2376734314390615398003629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25351832686833230912038709 2376734314390615398003629)
    ·
      refine ⟨891275367896480774251361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2376734314390615398003629 891275367896480774251361)
      ·
        refine ⟨668456525922360580688521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891275367896480774251361 668456525922360580688521)
        ·
          refine ⟨501342394441770435516391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668456525922360580688521 501342394441770435516391)
          ·
            refine ⟨752013591662655653274587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501342394441770435516391 752013591662655653274587)
            ·
              refine ⟨1128020387493983479911881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752013591662655653274587 1128020387493983479911881)
              ·
                refine ⟨846015290620487609933911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128020387493983479911881 846015290620487609933911)
                ·
                  refine ⟨1269022935930731414900867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846015290620487609933911 1269022935930731414900867)
                  ·
                    refine ⟨1903534403896097122351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269022935930731414900867 1903534403896097122351301)
                    ·
                      refine ⟨356912700730518210440869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1903534403896097122351301 356912700730518210440869)
                      ·
                        rfl

theorem cell23_695085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_695085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695085 prefixEnd_695085 := by exact prefixLift 695085
  have htrace : WordTrace (prefixWord ++ tailWord_695085) baseStart_695085 baseEnd_695085 := by
    simpa [prefixWord, tailWord_695085, baseEnd_695085] using wordTrace_append hprefix tailTrace_695085
  have hstable : (prefixWord ++ tailWord_695085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695085).length < 2 ^ (prefixWord ++ tailWord_695085).sum := by decide
  have hdescent : baseEnd_695085 < baseStart_695085 := by decide
  rcases family_descends (prefixWord ++ tailWord_695085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695100 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_695100 : Nat := 118140960795 + 695100 * 2 ^ 59
def prefixEnd_695100 : Nat := 4983230072969 + 3 ^ 40 * 695100 * 2
def baseEnd_695100 : Nat := 118973467646778550584433

theorem tailTrace_695100 : CollatzResearch.WordTrace tailWord_695100 prefixEnd_695100 118973467646778550584433 := by
  unfold tailWord_695100
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676189890889444236917377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16901586521185925649223169 12676189890889444236917377)
  ·
    refine ⟨9507142418167083177688033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12676189890889444236917377 9507142418167083177688033)
    ·
      refine ⟨7130356813625312383266025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9507142418167083177688033 7130356813625312383266025)
      ·
        refine ⟨5347767610218984287449519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7130356813625312383266025 5347767610218984287449519)
        ·
          refine ⟨8021651415328476431174279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347767610218984287449519 8021651415328476431174279)
          ·
            refine ⟨12032477122992714646761419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021651415328476431174279 12032477122992714646761419)
            ·
              refine ⟨18048715684489071970142129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032477122992714646761419 18048715684489071970142129)
              ·
                refine ⟨13536536763366803977606597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18048715684489071970142129 13536536763366803977606597)
                ·
                  refine ⟨2538100643131275745801237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13536536763366803977606597 2538100643131275745801237)
                  ·
                    refine ⟨118973467646778550584433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2538100643131275745801237 118973467646778550584433)
                    ·
                      rfl

theorem cell23_695100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_695100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695100 prefixEnd_695100 := by exact prefixLift 695100
  have htrace : WordTrace (prefixWord ++ tailWord_695100) baseStart_695100 baseEnd_695100 := by
    simpa [prefixWord, tailWord_695100, baseEnd_695100] using wordTrace_append hprefix tailTrace_695100
  have hstable : (prefixWord ++ tailWord_695100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695100).length < 2 ^ (prefixWord ++ tailWord_695100).sum := by decide
  have hdescent : baseEnd_695100 < baseStart_695100 := by decide
  rcases family_descends (prefixWord ++ tailWord_695100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695127 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_695127 : Nat := 118140960795 + 695127 * 2 ^ 59
def prefixEnd_695127 : Nat := 4983230072969 + 3 ^ 40 * 695127 * 2
def baseEnd_695127 : Nat := 356934266918007046115675

theorem tailTrace_695127 : CollatzResearch.WordTrace tailWord_695127 prefixEnd_695127 356934266918007046115675 := by
  unfold tailWord_695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353364552681072085067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16902243035120714723378423 25353364552681072085067635)
  ·
    refine ⟨38030046829021608127601453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25353364552681072085067635 38030046829021608127601453)
    ·
      refine ⟨14261267560883103047850545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38030046829021608127601453 14261267560883103047850545)
      ·
        refine ⟨10695950670662327285887909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14261267560883103047850545 10695950670662327285887909)
        ·
          refine ⟨2005490750749186366103983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10695950670662327285887909 2005490750749186366103983)
          ·
            refine ⟨3008236126123779549155975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005490750749186366103983 3008236126123779549155975)
            ·
              refine ⟨4512354189185669323733963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008236126123779549155975 4512354189185669323733963)
              ·
                refine ⟨6768531283778503985600945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512354189185669323733963 6768531283778503985600945)
                ·
                  refine ⟨5076398462833877989200709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768531283778503985600945 5076398462833877989200709)
                  ·
                    refine ⟨951824711781352122975133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076398462833877989200709 951824711781352122975133)
                    ·
                      refine ⟨356934266918007046115675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 951824711781352122975133 356934266918007046115675)
                      ·
                        rfl

theorem cell23_695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_695127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695127 prefixEnd_695127 := by exact prefixLift 695127
  have htrace : WordTrace (prefixWord ++ tailWord_695127) baseStart_695127 baseEnd_695127 := by
    simpa [prefixWord, tailWord_695127, baseEnd_695127] using wordTrace_append hprefix tailTrace_695127
  have hstable : (prefixWord ++ tailWord_695127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695127).length < 2 ^ (prefixWord ++ tailWord_695127).sum := by decide
  have hdescent : baseEnd_695127 < baseStart_695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695141 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_695141 : Nat := 118140960795 + 695141 * 2 ^ 59
def prefixEnd_695141 : Nat := 4983230072969 + 3 ^ 40 * 695141 * 2
def baseEnd_695141 : Nat := 356941455647169991340611

theorem tailTrace_695141 : CollatzResearch.WordTrace tailWord_695141 prefixEnd_695141 356941455647169991340611 := by
  unfold tailWord_695141
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353875174630352476077277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16902583449753568317384851 25353875174630352476077277)
  ·
    refine ⟨9507703190486382178528979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25353875174630352476077277 9507703190486382178528979)
    ·
      refine ⟨14261554785729573267793469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9507703190486382178528979 14261554785729573267793469)
      ·
        refine ⟨5348083044648589975422551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14261554785729573267793469 5348083044648589975422551)
        ·
          refine ⟨8022124566972884963133827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348083044648589975422551 8022124566972884963133827)
          ·
            refine ⟨12033186850459327444700741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8022124566972884963133827 12033186850459327444700741)
            ·
              refine ⟨2256222534461123895881389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12033186850459327444700741 2256222534461123895881389)
              ·
                refine ⟨846083450422921460955521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256222534461123895881389 846083450422921460955521)
                ·
                  refine ⟨634562587817191095716641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846083450422921460955521 634562587817191095716641)
                  ·
                    refine ⟨475921940862893321787481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634562587817191095716641 475921940862893321787481)
                    ·
                      refine ⟨356941455647169991340611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 475921940862893321787481 356941455647169991340611)
                      ·
                        rfl

theorem cell23_695141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_695141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695141 prefixEnd_695141 := by exact prefixLift 695141
  have htrace : WordTrace (prefixWord ++ tailWord_695141) baseStart_695141 baseEnd_695141 := by
    simpa [prefixWord, tailWord_695141, baseEnd_695141] using wordTrace_append hprefix tailTrace_695141
  have hstable : (prefixWord ++ tailWord_695141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695141).length < 2 ^ (prefixWord ++ tailWord_695141).sum := by decide
  have hdescent : baseEnd_695141 < baseStart_695141 := by decide
  rcases family_descends (prefixWord ++ tailWord_695141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695197 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_695197 : Nat := 118140960795 + 695197 * 2 ^ 59
def prefixEnd_695197 : Nat := 4983230072969 + 3 ^ 40 * 695197 * 2
def baseEnd_695197 : Nat := 356970210563821772240353

theorem tailTrace_695197 : CollatzResearch.WordTrace tailWord_695197 prefixEnd_695197 356970210563821772240353 := by
  unfold tailWord_695197
  simp only [CollatzResearch.WordTrace]
  refine ⟨25355917662427474040115845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16903945108284982693410563 25355917662427474040115845)
  ·
    refine ⟨4754234561705151382521721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25355917662427474040115845 4754234561705151382521721)
    ·
      refine ⟨3565675921278863536891291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4754234561705151382521721 3565675921278863536891291)
      ·
        refine ⟨5348513881918295305336937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565675921278863536891291 5348513881918295305336937)
        ·
          refine ⟨4011385411438721479002703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348513881918295305336937 4011385411438721479002703)
          ·
            refine ⟨6017078117158082218504055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011385411438721479002703 6017078117158082218504055)
            ·
              refine ⟨9025617175737123327756083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017078117158082218504055 9025617175737123327756083)
              ·
                refine ⟨13538425763605684991634125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025617175737123327756083 13538425763605684991634125)
                ·
                  refine ⟨5076909661352131871862797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13538425763605684991634125 5076909661352131871862797)
                  ·
                    refine ⟨1903841123007049451948549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5076909661352131871862797 1903841123007049451948549)
                    ·
                      refine ⟨356970210563821772240353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1903841123007049451948549 356970210563821772240353)
                      ·
                        rfl

theorem cell23_695197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_695197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695197 prefixEnd_695197 := by exact prefixLift 695197
  have htrace : WordTrace (prefixWord ++ tailWord_695197) baseStart_695197 baseEnd_695197 := by
    simpa [prefixWord, tailWord_695197, baseEnd_695197] using wordTrace_append hprefix tailTrace_695197
  have hstable : (prefixWord ++ tailWord_695197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695197).length < 2 ^ (prefixWord ++ tailWord_695197).sum := by decide
  have hdescent : baseEnd_695197 < baseStart_695197 := by decide
  rcases family_descends (prefixWord ++ tailWord_695197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695304 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_695304 : Nat := 118140960795 + 695304 * 2 ^ 59
def prefixEnd_695304 : Nat := 4983230072969 + 3 ^ 40 * 695304 * 2
def baseEnd_695304 : Nat := 357025152993852853602361

theorem tailTrace_695304 : CollatzResearch.WordTrace tailWord_695304 prefixEnd_695304 357025152993852853602361 := by
  unfold tailWord_695304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679910136519915657130483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16906546848693220876173977 12679910136519915657130483)
  ·
    refine ⟨19019865204779873485695725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679910136519915657130483 19019865204779873485695725)
    ·
      refine ⟨7132449451792452557135897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19019865204779873485695725 7132449451792452557135897)
      ·
        refine ⟨5349337088844339417851923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132449451792452557135897 5349337088844339417851923)
        ·
          refine ⟨8024005633266509126777885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5349337088844339417851923 8024005633266509126777885)
          ·
            refine ⟨3009002112474940922541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8024005633266509126777885 3009002112474940922541707)
            ·
              refine ⟨4513503168712411383812561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009002112474940922541707 4513503168712411383812561)
              ·
                refine ⟨3385127376534308537859421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513503168712411383812561 3385127376534308537859421)
                ·
                  refine ⟨1269422766200365701697283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3385127376534308537859421 1269422766200365701697283)
                  ·
                    refine ⟨1904134149300548552545925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269422766200365701697283 1904134149300548552545925)
                    ·
                      refine ⟨357025152993852853602361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1904134149300548552545925 357025152993852853602361)
                      ·
                        rfl

theorem cell23_695304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_695304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695304 prefixEnd_695304 := by exact prefixLift 695304
  have htrace : WordTrace (prefixWord ++ tailWord_695304) baseStart_695304 baseEnd_695304 := by
    simpa [prefixWord, tailWord_695304, baseEnd_695304] using wordTrace_append hprefix tailTrace_695304
  have hstable : (prefixWord ++ tailWord_695304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695304).length < 2 ^ (prefixWord ++ tailWord_695304).sum := by decide
  have hdescent : baseEnd_695304 < baseStart_695304 := by decide
  rcases family_descends (prefixWord ++ tailWord_695304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695321 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 5, 2, 2]
def baseStart_695321 : Nat := 118140960795 + 695321 * 2 ^ 59
def prefixEnd_695321 : Nat := 4983230072969 + 3 ^ 40 * 695321 * 2
def baseEnd_695321 : Nat := 357033882164979287089783

theorem tailTrace_695321 : CollatzResearch.WordTrace tailWord_695321 prefixEnd_695321 357033882164979287089783 := by
  unfold tailWord_695321
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360440313978243217629817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16906960209318828811753211 25360440313978243217629817)
  ·
    refine ⟨19020330235483682413222363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25360440313978243217629817 19020330235483682413222363)
    ·
      refine ⟨28530495353225523619833545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19020330235483682413222363 28530495353225523619833545)
      ·
        refine ⟨21397871514919142714875159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28530495353225523619833545 21397871514919142714875159)
        ·
          refine ⟨32096807272378714072312739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21397871514919142714875159 32096807272378714072312739)
          ·
            refine ⟨48145210908568071108469109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32096807272378714072312739 48145210908568071108469109)
            ·
              refine ⟨4513613522678256666418979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48145210908568071108469109 4513613522678256666418979)
              ·
                refine ⟨6770420284017384999628469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513613522678256666418979 6770420284017384999628469)
                ·
                  refine ⟨634726901626629843715169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6770420284017384999628469 634726901626629843715169)
                  ·
                    refine ⟨476045176219972382786377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634726901626629843715169 476045176219972382786377)
                    ·
                      refine ⟨357033882164979287089783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476045176219972382786377 357033882164979287089783)
                      ·
                        rfl

theorem cell23_695321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_695321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695321 prefixEnd_695321 := by exact prefixLift 695321
  have htrace : WordTrace (prefixWord ++ tailWord_695321) baseStart_695321 baseEnd_695321 := by
    simpa [prefixWord, tailWord_695321, baseEnd_695321] using wordTrace_append hprefix tailTrace_695321
  have hstable : (prefixWord ++ tailWord_695321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695321).length < 2 ^ (prefixWord ++ tailWord_695321).sum := by decide
  have hdescent : baseEnd_695321 < baseStart_695321 := by decide
  rcases family_descends (prefixWord ++ tailWord_695321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695325 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_695325 : Nat := 118140960795 + 695325 * 2 ^ 59
def prefixEnd_695325 : Nat := 4983230072969 + 3 ^ 40 * 695325 * 2
def baseEnd_695325 : Nat := 357035936087597271439765

theorem tailTrace_695325 : CollatzResearch.WordTrace tailWord_695325 prefixEnd_695325 357035936087597271439765 := by
  unfold tailWord_695325
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360586205963751900775429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16907057470642501267183619 25360586205963751900775429)
  ·
    refine ⟨4755109913618203481395393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25360586205963751900775429 4755109913618203481395393)
    ·
      refine ⟨3566332435213652611046545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4755109913618203481395393 3566332435213652611046545)
      ·
        refine ⟨2674749326410239458284909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3566332435213652611046545 2674749326410239458284909)
        ·
          refine ⟨1003030997403839796856841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2674749326410239458284909 1003030997403839796856841)
          ·
            refine ⟨752273248052879847642631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003030997403839796856841 752273248052879847642631)
            ·
              refine ⟨1128409872079319771463947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752273248052879847642631 1128409872079319771463947)
              ·
                refine ⟨1692614808118979657195921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128409872079319771463947 1692614808118979657195921)
                ·
                  refine ⟨1269461106089234742896941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692614808118979657195921 1269461106089234742896941)
                  ·
                    refine ⟨476047914783463028586353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269461106089234742896941 476047914783463028586353)
                    ·
                      refine ⟨357035936087597271439765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476047914783463028586353 357035936087597271439765)
                      ·
                        rfl

theorem cell23_695325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_695325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695325 prefixEnd_695325 := by exact prefixLift 695325
  have htrace : WordTrace (prefixWord ++ tailWord_695325) baseStart_695325 baseEnd_695325 := by
    simpa [prefixWord, tailWord_695325, baseEnd_695325] using wordTrace_append hprefix tailTrace_695325
  have hstable : (prefixWord ++ tailWord_695325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695325).length < 2 ^ (prefixWord ++ tailWord_695325).sum := by decide
  have hdescent : baseEnd_695325 < baseStart_695325 := by decide
  rcases family_descends (prefixWord ++ tailWord_695325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695335 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 1, 5]
def baseStart_695335 : Nat := 118140960795 + 695335 * 2 ^ 59
def prefixEnd_695335 : Nat := 4983230072969 + 3 ^ 40 * 695335 * 2
def baseEnd_695335 : Nat := 119013690298047410771573

theorem tailTrace_695335 : CollatzResearch.WordTrace tailWord_695335 prefixEnd_695335 119013690298047410771573 := by
  unfold tailWord_695335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360950935927523608639459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16907300623951682405759639 25360950935927523608639459)
  ·
    refine ⟨38041426403891285412959189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25360950935927523608639459 38041426403891285412959189)
    ·
      refine ⟨891595931341202001866231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38041426403891285412959189 891595931341202001866231)
      ·
        refine ⟨1337393897011803002799347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891595931341202001866231 1337393897011803002799347)
        ·
          refine ⟨2006090845517704504199021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337393897011803002799347 2006090845517704504199021)
          ·
            refine ⟨752284067069139189074633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2006090845517704504199021 752284067069139189074633)
            ·
              refine ⟨564213050301854391805975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752284067069139189074633 564213050301854391805975)
              ·
                refine ⟨846319575452781587708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564213050301854391805975 846319575452781587708963)
                ·
                  refine ⟨1269479363179172381563445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846319575452781587708963 1269479363179172381563445)
                  ·
                    refine ⟨119013690298047410771573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1269479363179172381563445 119013690298047410771573)
                    ·
                      rfl

theorem cell23_695335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_695335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695335 prefixEnd_695335 := by exact prefixLift 695335
  have htrace : WordTrace (prefixWord ++ tailWord_695335) baseStart_695335 baseEnd_695335 := by
    simpa [prefixWord, tailWord_695335, baseEnd_695335] using wordTrace_append hprefix tailTrace_695335
  have hstable : (prefixWord ++ tailWord_695335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695335).length < 2 ^ (prefixWord ++ tailWord_695335).sum := by decide
  have hdescent : baseEnd_695335 < baseStart_695335 := by decide
  rcases family_descends (prefixWord ++ tailWord_695335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695338 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_695338 : Nat := 118140960795 + 695338 * 2 ^ 59
def prefixEnd_695338 : Nat := 4983230072969 + 3 ^ 40 * 695338 * 2
def baseEnd_695338 : Nat := 357042611336105720577205

theorem tailTrace_695338 : CollatzResearch.WordTrace tailWord_695338 prefixEnd_695338 357042611336105720577205 := by
  unfold tailWord_695338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340265088729163780249667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16907373569944436747332445 6340265088729163780249667)
  ·
    refine ⟨9510397633093745670374501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340265088729163780249667 9510397633093745670374501)
    ·
      refine ⟨1783199556205077313195219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9510397633093745670374501 1783199556205077313195219)
      ·
        refine ⟨2674799334307615969792829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783199556205077313195219 2674799334307615969792829)
        ·
          refine ⟨1003049750365355988672311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2674799334307615969792829 1003049750365355988672311)
          ·
            refine ⟨1504574625548033983008467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003049750365355988672311 1504574625548033983008467)
            ·
              refine ⟨2256861938322050974512701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504574625548033983008467 2256861938322050974512701)
              ·
                refine ⟨846323226870769115442263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256861938322050974512701 846323226870769115442263)
                ·
                  refine ⟨1269484840306153673163395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846323226870769115442263 1269484840306153673163395)
                  ·
                    refine ⟨1904227260459230509745093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269484840306153673163395 1904227260459230509745093)
                    ·
                      refine ⟨357042611336105720577205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1904227260459230509745093 357042611336105720577205)
                      ·
                        rfl

theorem cell23_695338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_695338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695338 prefixEnd_695338 := by exact prefixLift 695338
  have htrace : WordTrace (prefixWord ++ tailWord_695338) baseStart_695338 baseEnd_695338 := by
    simpa [prefixWord, tailWord_695338, baseEnd_695338] using wordTrace_append hprefix tailTrace_695338
  have hstable : (prefixWord ++ tailWord_695338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695338).length < 2 ^ (prefixWord ++ tailWord_695338).sum := by decide
  have hdescent : baseEnd_695338 < baseStart_695338 := by decide
  rcases family_descends (prefixWord ++ tailWord_695338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_695347 : Nat := 118140960795 + 695347 * 2 ^ 59
def prefixEnd_695347 : Nat := 4983230072969 + 3 ^ 40 * 695347 * 2
def baseEnd_695347 : Nat := 357047232661996185364663

theorem tailTrace_695347 : CollatzResearch.WordTrace tailWord_695347 prefixEnd_695347 357047232661996185364663 := by
  unfold tailWord_695347
  simp only [CollatzResearch.WordTrace]
  refine ⟨25361388611884049658076295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16907592407922699772050863 25361388611884049658076295)
  ·
    refine ⟨38042082917826074487114443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25361388611884049658076295 38042082917826074487114443)
    ·
      refine ⟨57063124376739111730671665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38042082917826074487114443 57063124376739111730671665)
      ·
        refine ⟨42797343282554333798003749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57063124376739111730671665 42797343282554333798003749)
        ·
          refine ⟨8024501865478937587125703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42797343282554333798003749 8024501865478937587125703)
          ·
            refine ⟨12036752798218406380688555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024501865478937587125703 12036752798218406380688555)
            ·
              refine ⟨18055129197327609571032833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036752798218406380688555 18055129197327609571032833)
              ·
                refine ⟨13541346897995707178274625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18055129197327609571032833 13541346897995707178274625)
                ·
                  refine ⟨10156010173496780383705969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13541346897995707178274625 10156010173496780383705969)
                  ·
                    refine ⟨7617007630122585287779477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10156010173496780383705969 7617007630122585287779477)
                    ·
                      refine ⟨357047232661996185364663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7617007630122585287779477 357047232661996185364663)
                      ·
                        rfl

theorem cell23_695347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_695347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695347 prefixEnd_695347 := by exact prefixLift 695347
  have htrace : WordTrace (prefixWord ++ tailWord_695347) baseStart_695347 baseEnd_695347 := by
    simpa [prefixWord, tailWord_695347, baseEnd_695347] using wordTrace_append hprefix tailTrace_695347
  have hstable : (prefixWord ++ tailWord_695347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695347).length < 2 ^ (prefixWord ++ tailWord_695347).sum := by decide
  have hdescent : baseEnd_695347 < baseStart_695347 := by decide
  rcases family_descends (prefixWord ++ tailWord_695347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695348 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_695348 : Nat := 118140960795 + 695348 * 2 ^ 59
def prefixEnd_695348 : Nat := 4983230072969 + 3 ^ 40 * 695348 * 2
def baseEnd_695348 : Nat := 119015915380883560484053

theorem tailTrace_695348 : CollatzResearch.WordTrace tailWord_695348 prefixEnd_695348 119015915380883560484053 := by
  unfold tailWord_695348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680712542440213414431349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16907616723253617885908465 12680712542440213414431349)
  ·
    refine ⟨1188816800853770007602939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12680712542440213414431349 1188816800853770007602939)
    ·
      refine ⟨1783225201280655011404409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188816800853770007602939 1783225201280655011404409)
      ·
        refine ⟨1337418900960491258553307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783225201280655011404409 1337418900960491258553307)
        ·
          refine ⟨2006128351440736887829961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337418900960491258553307 2006128351440736887829961)
          ·
            refine ⟨1504596263580552665872471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006128351440736887829961 1504596263580552665872471)
            ·
              refine ⟨2256894395370828998808707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504596263580552665872471 2256894395370828998808707)
              ·
                refine ⟨3385341593056243498213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256894395370828998808707 3385341593056243498213061)
                ·
                  refine ⟨634751548698045655914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3385341593056243498213061 634751548698045655914949)
                  ·
                    refine ⟨119015915380883560484053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634751548698045655914949 119015915380883560484053)
                    ·
                      rfl

theorem cell23_695348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_695348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695348 prefixEnd_695348 := by exact prefixLift 695348
  have htrace : WordTrace (prefixWord ++ tailWord_695348) baseStart_695348 baseEnd_695348 := by
    simpa [prefixWord, tailWord_695348, baseEnd_695348] using wordTrace_append hprefix tailTrace_695348
  have hstable : (prefixWord ++ tailWord_695348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695348).length < 2 ^ (prefixWord ++ tailWord_695348).sum := by decide
  have hdescent : baseEnd_695348 < baseStart_695348 := by decide
  rcases family_descends (prefixWord ++ tailWord_695348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695354 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_695354 : Nat := 118140960795 + 695354 * 2 ^ 59
def prefixEnd_695354 : Nat := 4983230072969 + 3 ^ 40 * 695354 * 2
def baseEnd_695354 : Nat := 357050827026577657977131

theorem tailTrace_695354 : CollatzResearch.WordTrace tailWord_695354 prefixEnd_695354 357050827026577657977131 := by
  unfold tailWord_695354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340410980714672463395279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16907762615239126569054077 6340410980714672463395279)
  ·
    refine ⟨9510616471072008695092919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340410980714672463395279 9510616471072008695092919)
    ·
      refine ⟨14265924706608013042639379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510616471072008695092919 14265924706608013042639379)
      ·
        refine ⟨21398887059912019563959069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14265924706608013042639379 21398887059912019563959069)
        ·
          refine ⟨8024582647467007336484651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21398887059912019563959069 8024582647467007336484651)
          ·
            refine ⟨12036873971200511004726977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024582647467007336484651 12036873971200511004726977)
            ·
              refine ⟨9027655478400383253545233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12036873971200511004726977 9027655478400383253545233)
              ·
                refine ⟨6770741608800287440158925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9027655478400383253545233 6770741608800287440158925)
                ·
                  refine ⟨2539028103300107790059597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6770741608800287440158925 2539028103300107790059597)
                  ·
                    refine ⟨952135538737540421272349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539028103300107790059597 952135538737540421272349)
                    ·
                      refine ⟨357050827026577657977131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 952135538737540421272349 357050827026577657977131)
                      ·
                        rfl

theorem cell23_695354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_695354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695354 prefixEnd_695354 := by exact prefixLift 695354
  have htrace : WordTrace (prefixWord ++ tailWord_695354) baseStart_695354 baseEnd_695354 := by
    simpa [prefixWord, tailWord_695354, baseEnd_695354] using wordTrace_append hprefix tailTrace_695354
  have hstable : (prefixWord ++ tailWord_695354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695354).length < 2 ^ (prefixWord ++ tailWord_695354).sum := by decide
  have hdescent : baseEnd_695354 < baseStart_695354 := by decide
  rcases family_descends (prefixWord ++ tailWord_695354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695424 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_695424 : Nat := 118140960795 + 695424 * 2 ^ 59
def prefixEnd_695424 : Nat := 4983230072969 + 3 ^ 40 * 695424 * 2
def baseEnd_695424 : Nat := 357086770672392384101809

theorem tailTrace_695424 : CollatzResearch.WordTrace tailWord_695424 prefixEnd_695424 357086770672392384101809 := by
  unfold tailWord_695424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682098516302545904314663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16909464688403394539086217 12682098516302545904314663)
  ·
    refine ⟨19023147774453818856471995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12682098516302545904314663 19023147774453818856471995)
    ·
      refine ⟨28534721661680728284707993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19023147774453818856471995 28534721661680728284707993)
      ·
        refine ⟨21401041246260546213530995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28534721661680728284707993 21401041246260546213530995)
        ·
          refine ⟨32101561869390819320296493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21401041246260546213530995 32101561869390819320296493)
          ·
            refine ⟨12038085701021557245111185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32101561869390819320296493 12038085701021557245111185)
            ·
              refine ⟨9028564275766167933833389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12038085701021557245111185 9028564275766167933833389)
              ·
                refine ⟨3385711603412312975187521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9028564275766167933833389 3385711603412312975187521)
                ·
                  refine ⟨2539283702559234731390641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385711603412312975187521 2539283702559234731390641)
                  ·
                    refine ⟨1904462776919426048542981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539283702559234731390641 1904462776919426048542981)
                    ·
                      refine ⟨357086770672392384101809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1904462776919426048542981 357086770672392384101809)
                      ·
                        rfl

theorem cell23_695424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_695424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695424 prefixEnd_695424 := by exact prefixLift 695424
  have htrace : WordTrace (prefixWord ++ tailWord_695424) baseStart_695424 baseEnd_695424 := by
    simpa [prefixWord, tailWord_695424, baseEnd_695424] using wordTrace_append hprefix tailTrace_695424
  have hstable : (prefixWord ++ tailWord_695424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695424).length < 2 ^ (prefixWord ++ tailWord_695424).sum := by decide
  have hdescent : baseEnd_695424 < baseStart_695424 := by decide
  rcases family_descends (prefixWord ++ tailWord_695424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695432 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_695432 : Nat := 118140960795 + 695432 * 2 ^ 59
def prefixEnd_695432 : Nat := 4983230072969 + 3 ^ 40 * 695432 * 2
def baseEnd_695432 : Nat := 357090878517628352801773

theorem tailTrace_695432 : CollatzResearch.WordTrace tailWord_695432 prefixEnd_695432 357090878517628352801773 := by
  unfold tailWord_695432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682244408288054587460275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16909659211050739449947033 12682244408288054587460275)
  ·
    refine ⟨19023366612432081881190413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12682244408288054587460275 19023366612432081881190413)
    ·
      refine ⟨7133762479662030705446405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19023366612432081881190413 7133762479662030705446405)
      ·
        refine ⟨1337580464936630757271201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7133762479662030705446405 1337580464936630757271201)
        ·
          refine ⟨1003185348702473067953401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337580464936630757271201 1003185348702473067953401)
          ·
            refine ⟨752389011526854800965051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003185348702473067953401 752389011526854800965051)
            ·
              refine ⟨1128583517290282201447577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752389011526854800965051 1128583517290282201447577)
              ·
                refine ⟨846437637967711651085683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128583517290282201447577 846437637967711651085683)
                ·
                  refine ⟨1269656456951567476628525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846437637967711651085683 1269656456951567476628525)
                  ·
                    refine ⟨476121171356837803735697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269656456951567476628525 476121171356837803735697)
                    ·
                      refine ⟨357090878517628352801773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476121171356837803735697 357090878517628352801773)
                      ·
                        rfl

theorem cell23_695432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_695432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695432 prefixEnd_695432 := by exact prefixLift 695432
  have htrace : WordTrace (prefixWord ++ tailWord_695432) baseStart_695432 baseEnd_695432 := by
    simpa [prefixWord, tailWord_695432, baseEnd_695432] using wordTrace_append hprefix tailTrace_695432
  have hstable : (prefixWord ++ tailWord_695432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695432).length < 2 ^ (prefixWord ++ tailWord_695432).sum := by decide
  have hdescent : baseEnd_695432 < baseStart_695432 := by decide
  rcases family_descends (prefixWord ++ tailWord_695432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695434 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_695434 : Nat := 118140960795 + 695434 * 2 ^ 59
def prefixEnd_695434 : Nat := 4983230072969 + 3 ^ 40 * 695434 * 2
def baseEnd_695434 : Nat := 39676878386548593886307

theorem tailTrace_695434 : CollatzResearch.WordTrace tailWord_695434 prefixEnd_695434 39676878386548593886307 := by
  unfold tailWord_695434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341140440642215879123339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16909707841712575677662237 6341140440642215879123339)
  ·
    refine ⟨9511710660963323818685009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341140440642215879123339 9511710660963323818685009)
    ·
      refine ⟨7133782995722492864013757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9511710660963323818685009 7133782995722492864013757)
      ·
        refine ⟨2675168623395934824005159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7133782995722492864013757 2675168623395934824005159)
        ·
          refine ⟨4012752935093902236007739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675168623395934824005159 4012752935093902236007739)
          ·
            refine ⟨6019129402640853354011609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012752935093902236007739 6019129402640853354011609)
            ·
              refine ⟨4514347051980640015508707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6019129402640853354011609 4514347051980640015508707)
              ·
                refine ⟨6771520577970960023263061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514347051980640015508707 6771520577970960023263061)
                ·
                  refine ⟨39676878386548593886307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6771520577970960023263061 39676878386548593886307)
                  ·
                    rfl

theorem cell23_695434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_695434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695434 prefixEnd_695434 := by exact prefixLift 695434
  have htrace : WordTrace (prefixWord ++ tailWord_695434) baseStart_695434 baseEnd_695434 := by
    simpa [prefixWord, tailWord_695434, baseEnd_695434] using wordTrace_append hprefix tailTrace_695434
  have hstable : (prefixWord ++ tailWord_695434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695434).length < 2 ^ (prefixWord ++ tailWord_695434).sum := by decide
  have hdescent : baseEnd_695434 < baseStart_695434 := by decide
  rcases family_descends (prefixWord ++ tailWord_695434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695471 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 5, 2]
def baseStart_695471 : Nat := 118140960795 + 695471 * 2 ^ 59
def prefixEnd_695471 : Nat := 4983230072969 + 3 ^ 40 * 695471 * 2
def baseEnd_695471 : Nat := 357110904263153700214093

theorem tailTrace_695471 : CollatzResearch.WordTrace tailWord_695471 prefixEnd_695471 357110904263153700214093 := by
  unfold tailWord_695471
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365911263434818835590267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16910607508956545890393511 25365911263434818835590267)
  ·
    refine ⟨38048866895152228253385401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25365911263434818835590267 38048866895152228253385401)
    ·
      refine ⟨28536650171364171190039051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38048866895152228253385401 28536650171364171190039051)
      ·
        refine ⟨42804975257046256785058577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28536650171364171190039051 42804975257046256785058577)
        ·
          refine ⟨32103731442784692588793933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42804975257046256785058577 32103731442784692588793933)
          ·
            refine ⟨12038899291044259720797725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32103731442784692588793933 12038899291044259720797725)
            ·
              refine ⟨4514587234141597395299147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12038899291044259720797725 4514587234141597395299147)
              ·
                refine ⟨6771880851212396092948721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514587234141597395299147 6771880851212396092948721)
                ·
                  refine ⟨5078910638409297069711541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6771880851212396092948721 5078910638409297069711541)
                  ·
                    refine ⟨476147872350871600285457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5078910638409297069711541 476147872350871600285457)
                    ·
                      refine ⟨357110904263153700214093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476147872350871600285457 357110904263153700214093)
                      ·
                        rfl

theorem cell23_695471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5, 2].length) (baseStart_695471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695471 prefixEnd_695471 := by exact prefixLift 695471
  have htrace : WordTrace (prefixWord ++ tailWord_695471) baseStart_695471 baseEnd_695471 := by
    simpa [prefixWord, tailWord_695471, baseEnd_695471] using wordTrace_append hprefix tailTrace_695471
  have hstable : (prefixWord ++ tailWord_695471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695471).length < 2 ^ (prefixWord ++ tailWord_695471).sum := by decide
  have hdescent : baseEnd_695471 < baseStart_695471 := by decide
  rcases family_descends (prefixWord ++ tailWord_695471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695498 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_695498 : Nat := 118140960795 + 695498 * 2 ^ 59
def prefixEnd_695498 : Nat := 4983230072969 + 3 ^ 40 * 695498 * 2
def baseEnd_695498 : Nat := 119041589413608364858823

theorem tailTrace_695498 : CollatzResearch.WordTrace tailWord_695498 prefixEnd_695498 119041589413608364858823 := by
  unfold tailWord_695498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341724008584250611705787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16911264022891334964548765 6341724008584250611705787)
  ·
    refine ⟨9512586012876375917558681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341724008584250611705787 9512586012876375917558681)
    ·
      refine ⟨7134439509657281938169011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9512586012876375917558681 7134439509657281938169011)
      ·
        refine ⟨10701659264485922907253517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7134439509657281938169011 10701659264485922907253517)
        ·
          refine ⟨4013122224182221090220069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10701659264485922907253517 4013122224182221090220069)
          ·
            refine ⟨752460417034166454416263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4013122224182221090220069 752460417034166454416263)
            ·
              refine ⟨1128690625551249681624395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752460417034166454416263 1128690625551249681624395)
              ·
                refine ⟨1693035938326874522436593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128690625551249681624395 1693035938326874522436593)
                ·
                  refine ⟨1269776953745155891827445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693035938326874522436593 1269776953745155891827445)
                  ·
                    refine ⟨119041589413608364858823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1269776953745155891827445 119041589413608364858823)
                    ·
                      rfl

theorem cell23_695498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_695498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695498 prefixEnd_695498 := by exact prefixLift 695498
  have htrace : WordTrace (prefixWord ++ tailWord_695498) baseStart_695498 baseEnd_695498 := by
    simpa [prefixWord, tailWord_695498, baseEnd_695498] using wordTrace_append hprefix tailTrace_695498
  have hstable : (prefixWord ++ tailWord_695498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695498).length < 2 ^ (prefixWord ++ tailWord_695498).sum := by decide
  have hdescent : baseEnd_695498 < baseStart_695498 := by decide
  rcases family_descends (prefixWord ++ tailWord_695498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695528 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_695528 : Nat := 118140960795 + 695528 * 2 ^ 59
def prefixEnd_695528 : Nat := 4983230072969 + 3 ^ 40 * 695528 * 2
def baseEnd_695528 : Nat := 119046724220153325733777

theorem tailTrace_695528 : CollatzResearch.WordTrace tailWord_695528 prefixEnd_695528 119046724220153325733777 := by
  unfold tailWord_695528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683995112114158785207619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16911993482818878380276825 12683995112114158785207619)
  ·
    refine ⟨19025992668171238177811429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12683995112114158785207619 19025992668171238177811429)
    ·
      refine ⟨3567373625282107158339643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19025992668171238177811429 3567373625282107158339643)
      ·
        refine ⟨5351060437923160737509465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567373625282107158339643 5351060437923160737509465)
        ·
          refine ⟨4013295328442370553132099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5351060437923160737509465 4013295328442370553132099)
          ·
            refine ⟨6019942992663555829698149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013295328442370553132099 6019942992663555829698149)
            ·
              refine ⟨1128739311124416718068403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6019942992663555829698149 1128739311124416718068403)
              ·
                refine ⟨1693108966686625077102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128739311124416718068403 1693108966686625077102605)
                ·
                  refine ⟨634915862507484403913477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1693108966686625077102605 634915862507484403913477)
                  ·
                    refine ⟨119046724220153325733777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634915862507484403913477 119046724220153325733777)
                    ·
                      rfl

theorem cell23_695528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_695528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695528 prefixEnd_695528 := by exact prefixLift 695528
  have htrace : WordTrace (prefixWord ++ tailWord_695528) baseStart_695528 baseEnd_695528 := by
    simpa [prefixWord, tailWord_695528, baseEnd_695528] using wordTrace_append hprefix tailTrace_695528
  have hstable : (prefixWord ++ tailWord_695528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695528).length < 2 ^ (prefixWord ++ tailWord_695528).sum := by decide
  have hdescent : baseEnd_695528 < baseStart_695528 := by decide
  rcases family_descends (prefixWord ++ tailWord_695528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695605 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_695605 : Nat := 118140960795 + 695605 * 2 ^ 59
def prefixEnd_695605 : Nat := 4983230072969 + 3 ^ 40 * 695605 * 2
def baseEnd_695605 : Nat := 119059903556952058646159

theorem tailTrace_695605 : CollatzResearch.WordTrace tailWord_695605 prefixEnd_695605 119059903556952058646159 := by
  unfold tailWord_695605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370798644949359720968269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16913865763299573147312179 25370798644949359720968269)
  ·
    refine ⟨9514049491856009895363101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25370798644949359720968269 9514049491856009895363101)
    ·
      refine ⟨3567768559446003710761163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9514049491856009895363101 3567768559446003710761163)
      ·
        refine ⟨5351652839169005566141745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567768559446003710761163 5351652839169005566141745)
        ·
          refine ⟨4013739629376754174606309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5351652839169005566141745 4013739629376754174606309)
          ·
            refine ⟨752576180508141407738683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4013739629376754174606309 752576180508141407738683)
            ·
              refine ⟨1128864270762212111608025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752576180508141407738683 1128864270762212111608025)
              ·
                refine ⟨846648203071659083706019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128864270762212111608025 846648203071659083706019)
                ·
                  refine ⟨1269972304607488625559029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846648203071659083706019 1269972304607488625559029)
                  ·
                    refine ⟨119059903556952058646159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1269972304607488625559029 119059903556952058646159)
                    ·
                      rfl

theorem cell23_695605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_695605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695605 prefixEnd_695605 := by exact prefixLift 695605
  have htrace : WordTrace (prefixWord ++ tailWord_695605) baseStart_695605 baseEnd_695605 := by
    simpa [prefixWord, tailWord_695605, baseEnd_695605] using wordTrace_append hprefix tailTrace_695605
  have hstable : (prefixWord ++ tailWord_695605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695605).length < 2 ^ (prefixWord ++ tailWord_695605).sum := by decide
  have hdescent : baseEnd_695605 < baseStart_695605 := by decide
  rcases family_descends (prefixWord ++ tailWord_695605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695628 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_695628 : Nat := 118140960795 + 695628 * 2 ^ 59
def prefixEnd_695628 : Nat := 4983230072969 + 3 ^ 40 * 695628 * 2
def baseEnd_695628 : Nat := 357191520725909585950871

theorem tailTrace_695628 : CollatzResearch.WordTrace tailWord_695628 prefixEnd_695628 357191520725909585950871 := by
  unfold tailWord_695628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685818761933017324527769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16914425015910689766037025 12685818761933017324527769)
  ·
    refine ⟨9514364071449762993395827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12685818761933017324527769 9514364071449762993395827)
    ·
      refine ⟨14271546107174644490093741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514364071449762993395827 14271546107174644490093741)
      ·
        refine ⟨5351829790190491683785153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14271546107174644490093741 5351829790190491683785153)
        ·
          refine ⟨4013872342642868762838865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5351829790190491683785153 4013872342642868762838865)
          ·
            refine ⟨3010404256982151572129149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013872342642868762838865 3010404256982151572129149)
            ·
              refine ⟨1128901596368306839548431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3010404256982151572129149 1128901596368306839548431)
              ·
                refine ⟨1693352394552460259322647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128901596368306839548431 1693352394552460259322647)
                ·
                  refine ⟨2540028591828690388983971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693352394552460259322647 2540028591828690388983971)
                  ·
                    refine ⟨3810042887743035583475957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2540028591828690388983971 3810042887743035583475957)
                    ·
                      refine ⟨357191520725909585950871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3810042887743035583475957 357191520725909585950871)
                      ·
                        rfl

theorem cell23_695628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_695628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695628 prefixEnd_695628 := by exact prefixLift 695628
  have htrace : WordTrace (prefixWord ++ tailWord_695628) baseStart_695628 baseEnd_695628 := by
    simpa [prefixWord, tailWord_695628, baseEnd_695628] using wordTrace_append hprefix tailTrace_695628
  have hstable : (prefixWord ++ tailWord_695628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695628).length < 2 ^ (prefixWord ++ tailWord_695628).sum := by decide
  have hdescent : baseEnd_695628 < baseStart_695628 := by decide
  rcases family_descends (prefixWord ++ tailWord_695628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695648 : List Nat := [2, 1, 1, 3, 4, 3, 1, 8]
def baseStart_695648 : Nat := 118140960795 + 695648 * 2 ^ 59
def prefixEnd_695648 : Nat := 4983230072969 + 3 ^ 40 * 695648 * 2
def baseEnd_695648 : Nat := 13229695938481463248177

theorem tailTrace_695648 : CollatzResearch.WordTrace tailWord_695648 prefixEnd_695648 13229695938481463248177 := by
  unfold tailWord_695648
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686183491896789032391799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16914911322529052043189065 12686183491896789032391799)
  ·
    refine ⟨19029275237845183548587699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686183491896789032391799 19029275237845183548587699)
    ·
      refine ⟨28543912856767775322881549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19029275237845183548587699 28543912856767775322881549)
      ·
        refine ⟨10703967321287915746080581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28543912856767775322881549 10703967321287915746080581)
        ·
          refine ⟨2006993872741484202390109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10703967321287915746080581 2006993872741484202390109)
          ·
            refine ⟨752622702278056575896291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2006993872741484202390109 752622702278056575896291)
            ·
              refine ⟨1128934053417084863844437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752622702278056575896291 1128934053417084863844437)
              ·
                refine ⟨13229695938481463248177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1128934053417084863844437 13229695938481463248177)
                ·
                  rfl

theorem cell23_695648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_695648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695648 prefixEnd_695648 := by exact prefixLift 695648
  have htrace : WordTrace (prefixWord ++ tailWord_695648) baseStart_695648 baseEnd_695648 := by
    simpa [prefixWord, tailWord_695648, baseEnd_695648] using wordTrace_append hprefix tailTrace_695648
  have hstable : (prefixWord ++ tailWord_695648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695648).length < 2 ^ (prefixWord ++ tailWord_695648).sum := by decide
  have hdescent : baseEnd_695648 < baseStart_695648 := by decide
  rcases family_descends (prefixWord ++ tailWord_695648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695655 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_695655 : Nat := 118140960795 + 695655 * 2 ^ 59
def prefixEnd_695655 : Nat := 4983230072969 + 3 ^ 40 * 695655 * 2
def baseEnd_695655 : Nat := 357205384703580980313247

theorem tailTrace_695655 : CollatzResearch.WordTrace tailWord_695655 prefixEnd_695655 357205384703580980313247 := by
  unfold tailWord_695655
  simp only [CollatzResearch.WordTrace]
  refine ⟨25372622294768218260288419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915081529845478840192279 25372622294768218260288419)
  ·
    refine ⟨38058933442152327390432629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25372622294768218260288419 38058933442152327390432629)
    ·
      refine ⟨3568025010201780692853059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38058933442152327390432629 3568025010201780692853059)
      ·
        refine ⟨5352037515302671039279589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568025010201780692853059 5352037515302671039279589)
        ·
          refine ⟨1003507034119250819864923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5352037515302671039279589 1003507034119250819864923)
          ·
            refine ⟨1505260551178876229797385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003507034119250819864923 1505260551178876229797385)
            ·
              refine ⟨1128945413384157172348039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505260551178876229797385 1128945413384157172348039)
              ·
                refine ⟨1693418120076235758522059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128945413384157172348039 1693418120076235758522059)
                ·
                  refine ⟨2540127180114353637783089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693418120076235758522059 2540127180114353637783089)
                  ·
                    refine ⟨1905095385085765228337317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540127180114353637783089 1905095385085765228337317)
                    ·
                      refine ⟨357205384703580980313247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1905095385085765228337317 357205384703580980313247)
                      ·
                        rfl

theorem cell23_695655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_695655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695655 prefixEnd_695655 := by exact prefixLift 695655
  have htrace : WordTrace (prefixWord ++ tailWord_695655) baseStart_695655 baseEnd_695655 := by
    simpa [prefixWord, tailWord_695655, baseEnd_695655] using wordTrace_append hprefix tailTrace_695655
  have hstable : (prefixWord ++ tailWord_695655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695655).length < 2 ^ (prefixWord ++ tailWord_695655).sum := by decide
  have hdescent : baseEnd_695655 < baseStart_695655 := by decide
  rcases family_descends (prefixWord ++ tailWord_695655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695671 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_695671 : Nat := 118140960795 + 695671 * 2 ^ 59
def prefixEnd_695671 : Nat := 4983230072969 + 3 ^ 40 * 695671 * 2
def baseEnd_695671 : Nat := 357213600394052917713173

theorem tailTrace_695671 : CollatzResearch.WordTrace tailWord_695671 prefixEnd_695671 357213600394052917713173 := by
  unfold tailWord_695671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373205862710252992870867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915470575140168661913911 25373205862710252992870867)
  ·
    refine ⟨38059808794065379489306301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25373205862710252992870867 38059808794065379489306301)
    ·
      refine ⟨14272428297774517308489863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38059808794065379489306301 14272428297774517308489863)
      ·
        refine ⟨21408642446661775962734795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14272428297774517308489863 21408642446661775962734795)
        ·
          refine ⟨32112963669992663944102193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21408642446661775962734795 32112963669992663944102193)
          ·
            refine ⟨24084722752494497958076645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32112963669992663944102193 24084722752494497958076645)
            ·
              refine ⟨4515885516092718367139371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24084722752494497958076645 4515885516092718367139371)
              ·
                refine ⟨6773828274139077550709057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515885516092718367139371 6773828274139077550709057)
                ·
                  refine ⟨5080371205604308163031793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773828274139077550709057 5080371205604308163031793)
                  ·
                    refine ⟨3810278404203231122273845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080371205604308163031793 3810278404203231122273845)
                    ·
                      refine ⟨357213600394052917713173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3810278404203231122273845 357213600394052917713173)
                      ·
                        rfl

theorem cell23_695671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_695671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695671 prefixEnd_695671 := by exact prefixLift 695671
  have htrace : WordTrace (prefixWord ++ tailWord_695671) baseStart_695671 baseEnd_695671 := by
    simpa [prefixWord, tailWord_695671, baseEnd_695671] using wordTrace_append hprefix tailTrace_695671
  have hstable : (prefixWord ++ tailWord_695671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695671).length < 2 ^ (prefixWord ++ tailWord_695671).sum := by decide
  have hdescent : baseEnd_695671 < baseStart_695671 := by decide
  rcases family_descends (prefixWord ++ tailWord_695671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695691 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 6]
def baseStart_695691 : Nat := 118140960795 + 695691 * 2 ^ 59
def prefixEnd_695691 : Nat := 4983230072969 + 3 ^ 40 * 695691 * 2
def baseEnd_695691 : Nat := 119074623335714279821027

theorem tailTrace_695691 : CollatzResearch.WordTrace tailWord_695691 prefixEnd_695691 119074623335714279821027 := by
  unfold tailWord_695691
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373935322637796408598927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915956881758530939065951 25373935322637796408598927)
  ·
    refine ⟨38060902983956694612898391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25373935322637796408598927 38060902983956694612898391)
    ·
      refine ⟨57091354475935041919347587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38060902983956694612898391 57091354475935041919347587)
      ·
        refine ⟨85637031713902562879021381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57091354475935041919347587 85637031713902562879021381)
        ·
          refine ⟨16056943446356730539816509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85637031713902562879021381 16056943446356730539816509)
          ·
            refine ⟨6021353792383773952431191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16056943446356730539816509 6021353792383773952431191)
            ·
              refine ⟨9032030688575660928646787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021353792383773952431191 9032030688575660928646787)
              ·
                refine ⟨13548046032863491392970181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9032030688575660928646787 13548046032863491392970181)
                ·
                  refine ⟨2540258631161904636181909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13548046032863491392970181 2540258631161904636181909)
                  ·
                    refine ⟨119074623335714279821027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2540258631161904636181909 119074623335714279821027)
                    ·
                      rfl

theorem cell23_695691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_695691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695691 prefixEnd_695691 := by exact prefixLift 695691
  have htrace : WordTrace (prefixWord ++ tailWord_695691) baseStart_695691 baseEnd_695691 := by
    simpa [prefixWord, tailWord_695691, baseEnd_695691] using wordTrace_append hprefix tailTrace_695691
  have hstable : (prefixWord ++ tailWord_695691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695691).length < 2 ^ (prefixWord ++ tailWord_695691).sum := by decide
  have hdescent : baseEnd_695691 < baseStart_695691 := by decide
  rcases family_descends (prefixWord ++ tailWord_695691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695709 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_695709 : Nat := 118140960795 + 695709 * 2 ^ 59
def prefixEnd_695709 : Nat := 4983230072969 + 3 ^ 40 * 695709 * 2
def baseEnd_695709 : Nat := 357233112658923769037999

theorem tailTrace_695709 : CollatzResearch.WordTrace tailWord_695709 prefixEnd_695709 357233112658923769037999 := by
  unfold tailWord_695709
  simp only [CollatzResearch.WordTrace]
  refine ⟨25374591836572585482754181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16916394557715056988502787 25374591836572585482754181)
  ·
    refine ⟨4757735969357359778016409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25374591836572585482754181 4757735969357359778016409)
    ·
      refine ⟨3568301977018019833512307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4757735969357359778016409 3568301977018019833512307)
      ·
        refine ⟨5352452965527029750268461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568301977018019833512307 5352452965527029750268461)
        ·
          refine ⟨2007169862072636156350673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5352452965527029750268461 2007169862072636156350673)
          ·
            refine ⟨1505377396554477117263005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2007169862072636156350673 1505377396554477117263005)
            ·
              refine ⟨564516523707928918973627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1505377396554477117263005 564516523707928918973627)
              ·
                refine ⟨846774785561893378460441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564516523707928918973627 846774785561893378460441)
                ·
                  refine ⟨635081089171420033845331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846774785561893378460441 635081089171420033845331)
                  ·
                    refine ⟨952621633757130050767997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635081089171420033845331 952621633757130050767997)
                    ·
                      refine ⟨357233112658923769037999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 952621633757130050767997 357233112658923769037999)
                      ·
                        rfl

theorem cell23_695709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_695709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695709 prefixEnd_695709 := by exact prefixLift 695709
  have htrace : WordTrace (prefixWord ++ tailWord_695709) baseStart_695709 baseEnd_695709 := by
    simpa [prefixWord, tailWord_695709, baseEnd_695709] using wordTrace_append hprefix tailTrace_695709
  have hstable : (prefixWord ++ tailWord_695709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695709).length < 2 ^ (prefixWord ++ tailWord_695709).sum := by decide
  have hdescent : baseEnd_695709 < baseStart_695709 := by decide
  rcases family_descends (prefixWord ++ tailWord_695709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695766 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_695766 : Nat := 118140960795 + 695766 * 2 ^ 59
def prefixEnd_695766 : Nat := 4983230072969 + 3 ^ 40 * 695766 * 2
def baseEnd_695766 : Nat := 357262381056230046025237

theorem tailTrace_695766 : CollatzResearch.WordTrace tailWord_695766 prefixEnd_695766 357262381056230046025237 := by
  unfold tailWord_695766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586041924835380263598697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16917780531577389478386101 1586041924835380263598697)
  ·
    refine ⟨1189531443626535197699023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1586041924835380263598697 1189531443626535197699023)
    ·
      refine ⟨1784297165439802796548535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189531443626535197699023 1784297165439802796548535)
      ·
        refine ⟨2676445748159704194822803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784297165439802796548535 2676445748159704194822803)
        ·
          refine ⟨4014668622239556292234205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676445748159704194822803 4014668622239556292234205)
          ·
            refine ⟨1505500733339833609587827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4014668622239556292234205 1505500733339833609587827)
            ·
              refine ⟨2258251100009750414381741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505500733339833609587827 2258251100009750414381741)
              ·
                refine ⟨846844162503656405393153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2258251100009750414381741 846844162503656405393153)
                ·
                  refine ⟨635133121877742304044865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846844162503656405393153 635133121877742304044865)
                  ·
                    refine ⟨476349841408306728033649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 635133121877742304044865 476349841408306728033649)
                    ·
                      refine ⟨357262381056230046025237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476349841408306728033649 357262381056230046025237)
                      ·
                        rfl

theorem cell23_695766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_695766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695766 prefixEnd_695766 := by exact prefixLift 695766
  have htrace : WordTrace (prefixWord ++ tailWord_695766) baseStart_695766 baseEnd_695766 := by
    simpa [prefixWord, tailWord_695766, baseEnd_695766] using wordTrace_append hprefix tailTrace_695766
  have hstable : (prefixWord ++ tailWord_695766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695766).length < 2 ^ (prefixWord ++ tailWord_695766).sum := by decide
  have hdescent : baseEnd_695766 < baseStart_695766 := by decide
  rcases family_descends (prefixWord ++ tailWord_695766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695771 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_695771 : Nat := 118140960795 + 695771 * 2 ^ 59
def prefixEnd_695771 : Nat := 4983230072969 + 3 ^ 40 * 695771 * 2
def baseEnd_695771 : Nat := 357264948459502526462713

theorem tailTrace_695771 : CollatzResearch.WordTrace tailWord_695771 prefixEnd_695771 357264948459502526462713 := by
  unfold tailWord_695771
  simp only [CollatzResearch.WordTrace]
  refine ⟨25376853162347970071511167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16917902108231980047674111 25376853162347970071511167)
  ·
    refine ⟨38065279743521955107266751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25376853162347970071511167 38065279743521955107266751)
    ·
      refine ⟨57097919615282932660900127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38065279743521955107266751 57097919615282932660900127)
      ·
        refine ⟨85646879422924398991350191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57097919615282932660900127 85646879422924398991350191)
        ·
          refine ⟨128470319134386598487025287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85646879422924398991350191 128470319134386598487025287)
          ·
            refine ⟨192705478701579897730537931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128470319134386598487025287 192705478701579897730537931)
            ·
              refine ⟨289058218052369846595806897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192705478701579897730537931 289058218052369846595806897)
              ·
                refine ⟨216793663539277384946855173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289058218052369846595806897 216793663539277384946855173)
                ·
                  refine ⟨40648811913614509677535345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216793663539277384946855173 40648811913614509677535345)
                  ·
                    refine ⟨30486608935210882258151509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40648811913614509677535345 30486608935210882258151509)
                    ·
                      refine ⟨357264948459502526462713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30486608935210882258151509 357264948459502526462713)
                      ·
                        rfl

theorem cell23_695771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_695771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695771 prefixEnd_695771 := by exact prefixLift 695771
  have htrace : WordTrace (prefixWord ++ tailWord_695771) baseStart_695771 baseEnd_695771 := by
    simpa [prefixWord, tailWord_695771, baseEnd_695771] using wordTrace_append hprefix tailTrace_695771
  have hstable : (prefixWord ++ tailWord_695771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695771).length < 2 ^ (prefixWord ++ tailWord_695771).sum := by decide
  have hdescent : baseEnd_695771 < baseStart_695771 := by decide
  rcases family_descends (prefixWord ++ tailWord_695771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695805 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_695805 : Nat := 118140960795 + 695805 * 2 ^ 59
def prefixEnd_695805 : Nat := 4983230072969 + 3 ^ 40 * 695805 * 2
def baseEnd_695805 : Nat := 357282406801755393437557

theorem tailTrace_695805 : CollatzResearch.WordTrace tailWord_695805 prefixEnd_695805 357282406801755393437557 := by
  unfold tailWord_695805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378093244224793878248869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16918728829483195918832579 25378093244224793878248869)
  ·
    refine ⟨4758392483292148852171663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25378093244224793878248869 4758392483292148852171663)
    ·
      refine ⟨7137588724938223278257495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758392483292148852171663 7137588724938223278257495)
      ·
        refine ⟨10706383087407334917386243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137588724938223278257495 10706383087407334917386243)
        ·
          refine ⟨16059574631111002376079365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10706383087407334917386243 16059574631111002376079365)
          ·
            refine ⟨3011170243333312945514881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16059574631111002376079365 3011170243333312945514881)
            ·
              refine ⟨2258377682499984709136161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011170243333312945514881 2258377682499984709136161)
              ·
                refine ⟨1693783261874988531852121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258377682499984709136161 1693783261874988531852121)
                ·
                  refine ⟨1270337446406241398889091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693783261874988531852121 1270337446406241398889091)
                  ·
                    refine ⟨1905506169609362098333637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270337446406241398889091 1905506169609362098333637)
                    ·
                      refine ⟨357282406801755393437557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1905506169609362098333637 357282406801755393437557)
                      ·
                        rfl

theorem cell23_695805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_695805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695805 prefixEnd_695805 := by exact prefixLift 695805
  have htrace : WordTrace (prefixWord ++ tailWord_695805) baseStart_695805 baseEnd_695805 := by
    simpa [prefixWord, tailWord_695805, baseEnd_695805] using wordTrace_append hprefix tailTrace_695805
  have hstable : (prefixWord ++ tailWord_695805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695805).length < 2 ^ (prefixWord ++ tailWord_695805).sum := by decide
  have hdescent : baseEnd_695805 < baseStart_695805 := by decide
  rcases family_descends (prefixWord ++ tailWord_695805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695832 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_695832 : Nat := 118140960795 + 695832 * 2 ^ 59
def prefixEnd_695832 : Nat := 4983230072969 + 3 ^ 40 * 695832 * 2
def baseEnd_695832 : Nat := 119098756926475595933311

theorem tailTrace_695832 : CollatzResearch.WordTrace tailWord_695832 prefixEnd_695832 119098756926475595933311 := by
  unfold tailWord_695832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689539007563488744740875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16919385343417984992987833 12689539007563488744740875)
  ·
    refine ⟨19034308511345233117111313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12689539007563488744740875 19034308511345233117111313)
    ·
      refine ⟨14275731383508924837833485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19034308511345233117111313 14275731383508924837833485)
      ·
        refine ⟨5353399268815846814187557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14275731383508924837833485 5353399268815846814187557)
        ·
          refine ⟨1003762362902971277660167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5353399268815846814187557 1003762362902971277660167)
          ·
            refine ⟨1505643544354456916490251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003762362902971277660167 1505643544354456916490251)
            ·
              refine ⟨2258465316531685374735377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505643544354456916490251 2258465316531685374735377)
              ·
                refine ⟨1693848987398764031051533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258465316531685374735377 1693848987398764031051533)
                ·
                  refine ⟨635193370274536511644325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1693848987398764031051533 635193370274536511644325)
                  ·
                    refine ⟨119098756926475595933311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635193370274536511644325 119098756926475595933311)
                    ·
                      rfl

theorem cell23_695832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_695832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695832 prefixEnd_695832 := by exact prefixLift 695832
  have htrace : WordTrace (prefixWord ++ tailWord_695832) baseStart_695832 baseEnd_695832 := by
    simpa [prefixWord, tailWord_695832, baseEnd_695832] using wordTrace_append hprefix tailTrace_695832
  have hstable : (prefixWord ++ tailWord_695832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695832).length < 2 ^ (prefixWord ++ tailWord_695832).sum := by decide
  have hdescent : baseEnd_695832 < baseStart_695832 := by decide
  rcases family_descends (prefixWord ++ tailWord_695832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695842 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_695842 : Nat := 118140960795 + 695842 * 2 ^ 59
def prefixEnd_695842 : Nat := 4983230072969 + 3 ^ 40 * 695842 * 2
def baseEnd_695842 : Nat := 357301405585971748674887

theorem tailTrace_695842 : CollatzResearch.WordTrace tailWord_695842 prefixEnd_695842 357301405585971748674887 := by
  unfold tailWord_695842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344860686272687299336445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16919628496727166131563853 6344860686272687299336445)
  ·
    refine ⟨2379322757352257737251167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6344860686272687299336445 2379322757352257737251167)
    ·
      refine ⟨3568984136028386605876751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379322757352257737251167 3568984136028386605876751)
      ·
        refine ⟨5353476204042579908815127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568984136028386605876751 5353476204042579908815127)
        ·
          refine ⟨8030214306063869863222691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353476204042579908815127 8030214306063869863222691)
          ·
            refine ⟨12045321459095804794834037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030214306063869863222691 12045321459095804794834037)
            ·
              refine ⟨1129248886790231699515691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12045321459095804794834037 1129248886790231699515691)
              ·
                refine ⟨1693873330185347549273537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129248886790231699515691 1693873330185347549273537)
                ·
                  refine ⟨1270404997639010661955153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693873330185347549273537 1270404997639010661955153)
                  ·
                    refine ⟨952803748229257996466365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270404997639010661955153 952803748229257996466365)
                    ·
                      refine ⟨357301405585971748674887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 952803748229257996466365 357301405585971748674887)
                      ·
                        rfl

theorem cell23_695842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_695842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695842 prefixEnd_695842 := by exact prefixLift 695842
  have htrace : WordTrace (prefixWord ++ tailWord_695842) baseStart_695842 baseEnd_695842 := by
    simpa [prefixWord, tailWord_695842, baseEnd_695842] using wordTrace_append hprefix tailTrace_695842
  have hstable : (prefixWord ++ tailWord_695842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695842).length < 2 ^ (prefixWord ++ tailWord_695842).sum := by decide
  have hdescent : baseEnd_695842 < baseStart_695842 := by decide
  rcases family_descends (prefixWord ++ tailWord_695842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695862 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_695862 : Nat := 118140960795 + 695862 * 2 ^ 59
def prefixEnd_695862 : Nat := 4983230072969 + 3 ^ 40 * 695862 * 2
def baseEnd_695862 : Nat := 39701297244340185602755

theorem tailTrace_695862 : CollatzResearch.WordTrace tailWord_695862 prefixEnd_695862 39701297244340185602755 := by
  unfold tailWord_695862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586260762813643288317115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16920114803345528408715893 1586260762813643288317115)
  ·
    refine ⟨2379391144220464932475673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586260762813643288317115 2379391144220464932475673)
    ·
      refine ⟨1784543358165348699356755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2379391144220464932475673 1784543358165348699356755)
      ·
        refine ⟨2676815037248023049035133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784543358165348699356755 2676815037248023049035133)
        ·
          refine ⟨1003805638968008643388175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676815037248023049035133 1003805638968008643388175)
          ·
            refine ⟨1505708458452012965082263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003805638968008643388175 1505708458452012965082263)
            ·
              refine ⟨2258562687678019447623395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505708458452012965082263 2258562687678019447623395)
              ·
                refine ⟨3387844031517029171435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258562687678019447623395 3387844031517029171435093)
                ·
                  refine ⟨39701297244340185602755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3387844031517029171435093 39701297244340185602755)
                  ·
                    rfl

theorem cell23_695862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_695862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695862 prefixEnd_695862 := by exact prefixLift 695862
  have htrace : WordTrace (prefixWord ++ tailWord_695862) baseStart_695862 baseEnd_695862 := by
    simpa [prefixWord, tailWord_695862, baseEnd_695862] using wordTrace_append hprefix tailTrace_695862
  have hstable : (prefixWord ++ tailWord_695862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695862).length < 2 ^ (prefixWord ++ tailWord_695862).sum := by decide
  have hdescent : baseEnd_695862 < baseStart_695862 := by decide
  rcases family_descends (prefixWord ++ tailWord_695862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695892 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_695892 : Nat := 118140960795 + 695892 * 2 ^ 59
def prefixEnd_695892 : Nat := 4983230072969 + 3 ^ 40 * 695892 * 2
def baseEnd_695892 : Nat := 119109026539565517683219

theorem tailTrace_695892 : CollatzResearch.WordTrace tailWord_695892 prefixEnd_695892 119109026539565517683219 := by
  unfold tailWord_695892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690633197454803868332965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16920844263273071824443953 12690633197454803868332965)
  ·
    refine ⟨2379493724522775725312431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12690633197454803868332965 2379493724522775725312431)
    ·
      refine ⟨3569240586784163587968647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379493724522775725312431 3569240586784163587968647)
      ·
        refine ⟨5353860880176245381952971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569240586784163587968647 5353860880176245381952971)
        ·
          refine ⟨8030791320264368072929457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353860880176245381952971 8030791320264368072929457)
          ·
            refine ⟨6023093490198276054697093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8030791320264368072929457 6023093490198276054697093)
            ·
              refine ⟨1129330029412176760255705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6023093490198276054697093 1129330029412176760255705)
              ·
                refine ⟨846997522059132570191779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129330029412176760255705 846997522059132570191779)
                ·
                  refine ⟨1270496283088698855287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846997522059132570191779 1270496283088698855287669)
                  ·
                    refine ⟨119109026539565517683219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1270496283088698855287669 119109026539565517683219)
                    ·
                      rfl

theorem cell23_695892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_695892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695892 prefixEnd_695892 := by exact prefixLift 695892
  have htrace : WordTrace (prefixWord ++ tailWord_695892) baseStart_695892 baseEnd_695892 := by
    simpa [prefixWord, tailWord_695892, baseEnd_695892] using wordTrace_append hprefix tailTrace_695892
  have hstable : (prefixWord ++ tailWord_695892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695892).length < 2 ^ (prefixWord ++ tailWord_695892).sum := by decide
  have hdescent : baseEnd_695892 < baseStart_695892 := by decide
  rcases family_descends (prefixWord ++ tailWord_695892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695905 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_695905 : Nat := 118140960795 + 695905 * 2 ^ 59
def prefixEnd_695905 : Nat := 4983230072969 + 3 ^ 40 * 695905 * 2
def baseEnd_695905 : Nat := 119111251622401667395699

theorem tailTrace_695905 : CollatzResearch.WordTrace tailWord_695905 prefixEnd_695905 119111251622401667395699 := by
  unfold tailWord_695905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381740543862510956889169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16921160362575007304592779 25381740543862510956889169)
  ·
    refine ⟨19036305407896883217666877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25381740543862510956889169 19036305407896883217666877)
    ·
      refine ⟨7138614527961331206625079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19036305407896883217666877 7138614527961331206625079)
      ·
        refine ⟨10707921791941996809937619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138614527961331206625079 10707921791941996809937619)
        ·
          refine ⟨16061882687912995214906429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707921791941996809937619 16061882687912995214906429)
          ·
            refine ⟨6023206007967373205589911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16061882687912995214906429 6023206007967373205589911)
            ·
              refine ⟨9034809011951059808384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023206007967373205589911 9034809011951059808384867)
              ·
                refine ⟨13552213517926589712577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9034809011951059808384867 13552213517926589712577301)
                ·
                  refine ⟨635260008652808892777061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13552213517926589712577301 635260008652808892777061)
                  ·
                    refine ⟨119111251622401667395699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635260008652808892777061 119111251622401667395699)
                    ·
                      rfl

theorem cell23_695905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_695905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695905 prefixEnd_695905 := by exact prefixLift 695905
  have htrace : WordTrace (prefixWord ++ tailWord_695905) baseStart_695905 baseEnd_695905 := by
    simpa [prefixWord, tailWord_695905, baseEnd_695905] using wordTrace_append hprefix tailTrace_695905
  have hstable : (prefixWord ++ tailWord_695905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695905).length < 2 ^ (prefixWord ++ tailWord_695905).sum := by decide
  have hdescent : baseEnd_695905 < baseStart_695905 := by decide
  rcases family_descends (prefixWord ++ tailWord_695905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695922 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_695922 : Nat := 118140960795 + 695922 * 2 ^ 59
def prefixEnd_695922 : Nat := 4983230072969 + 3 ^ 40 * 695922 * 2
def baseEnd_695922 : Nat := 119114161346110478558173

theorem tailTrace_695922 : CollatzResearch.WordTrace tailWord_695922 prefixEnd_695922 119114161346110478558173 := by
  unfold tailWord_695922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345590146200230715064505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16921573723200615240172013 6345590146200230715064505)
  ·
    refine ⟨4759192609650173036298379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6345590146200230715064505 4759192609650173036298379)
    ·
      refine ⟨7138788914475259554447569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759192609650173036298379 7138788914475259554447569)
      ·
        refine ⟨5354091685856444665835677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138788914475259554447569 5354091685856444665835677)
        ·
          refine ⟨2007784382196166749688379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5354091685856444665835677 2007784382196166749688379)
          ·
            refine ⟨3011676573294250124532569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007784382196166749688379 3011676573294250124532569)
            ·
              refine ⟨2258757429970687593399427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011676573294250124532569 2258757429970687593399427)
              ·
                refine ⟨3388136144956031390099141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258757429970687593399427 3388136144956031390099141)
                ·
                  refine ⟨635275527179255885643589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3388136144956031390099141 635275527179255885643589)
                  ·
                    refine ⟨119114161346110478558173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635275527179255885643589 119114161346110478558173)
                    ·
                      rfl

theorem cell23_695922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_695922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695922 prefixEnd_695922 := by exact prefixLift 695922
  have htrace : WordTrace (prefixWord ++ tailWord_695922) baseStart_695922 baseEnd_695922 := by
    simpa [prefixWord, tailWord_695922, baseEnd_695922] using wordTrace_append hprefix tailTrace_695922
  have hstable : (prefixWord ++ tailWord_695922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695922).length < 2 ^ (prefixWord ++ tailWord_695922).sum := by decide
  have hdescent : baseEnd_695922 < baseStart_695922 := by decide
  rcases family_descends (prefixWord ++ tailWord_695922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695928 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_695928 : Nat := 118140960795 + 695928 * 2 ^ 59
def prefixEnd_695928 : Nat := 4983230072969 + 3 ^ 40 * 695928 * 2
def baseEnd_695928 : Nat := 357345564922258412199491

theorem tailTrace_695928 : CollatzResearch.WordTrace tailWord_695928 prefixEnd_695928 357345564922258412199491 := by
  unfold tailWord_695928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691289711389592942488219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16921719615186123923317625 12691289711389592942488219)
  ·
    refine ⟨19036934567084389413732329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691289711389592942488219 19036934567084389413732329)
    ·
      refine ⟨14277700925313292060299247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19036934567084389413732329 14277700925313292060299247)
      ·
        refine ⟨21416551387969938090448871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14277700925313292060299247 21416551387969938090448871)
        ·
          refine ⟨32124827081954907135673307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21416551387969938090448871 32124827081954907135673307)
          ·
            refine ⟨48187240622932360703509961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32124827081954907135673307 48187240622932360703509961)
            ·
              refine ⟨36140430467199270527632471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48187240622932360703509961 36140430467199270527632471)
              ·
                refine ⟨54210645700798905791448707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36140430467199270527632471 54210645700798905791448707)
                ·
                  refine ⟨81315968551198358687173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54210645700798905791448707 81315968551198358687173061)
                  ·
                    refine ⟨15246744103349692253844949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81315968551198358687173061 15246744103349692253844949)
                    ·
                      refine ⟨357345564922258412199491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15246744103349692253844949 357345564922258412199491)
                      ·
                        rfl

theorem cell23_695928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_695928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_695928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_695928 prefixEnd_695928 := by exact prefixLift 695928
  have htrace : WordTrace (prefixWord ++ tailWord_695928) baseStart_695928 baseEnd_695928 := by
    simpa [prefixWord, tailWord_695928, baseEnd_695928] using wordTrace_append hprefix tailTrace_695928
  have hstable : (prefixWord ++ tailWord_695928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695928).length < 2 ^ (prefixWord ++ tailWord_695928).sum := by decide
  have hdescent : baseEnd_695928 < baseStart_695928 := by decide
  rcases family_descends (prefixWord ++ tailWord_695928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696055 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 7]
def baseStart_696055 : Nat := 118140960795 + 696055 * 2 ^ 59
def prefixEnd_696055 : Nat := 4983230072969 + 3 ^ 40 * 696055 * 2
def baseEnd_696055 : Nat := 119136925655126471770469

theorem tailTrace_696055 : CollatzResearch.WordTrace tailWord_696055 prefixEnd_696055 119136925655126471770469 := by
  unfold tailWord_696055
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387211493319086574849619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16924807662212724383233079 25387211493319086574849619)
  ·
    refine ⟨38080817239978629862274429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25387211493319086574849619 38080817239978629862274429)
    ·
      refine ⟨14280306464991986198352911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38080817239978629862274429 14280306464991986198352911)
      ·
        refine ⟨21420459697487979297529367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14280306464991986198352911 21420459697487979297529367)
        ·
          refine ⟨32130689546231968946294051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21420459697487979297529367 32130689546231968946294051)
          ·
            refine ⟨48196034319347953419441077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32130689546231968946294051 48196034319347953419441077)
            ·
              refine ⟨4518378217438870633072601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48196034319347953419441077 4518378217438870633072601)
              ·
                refine ⟨3388783663079152974804451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4518378217438870633072601 3388783663079152974804451)
                ·
                  refine ⟨5083175494618729462206677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388783663079152974804451 5083175494618729462206677)
                  ·
                    refine ⟨119136925655126471770469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5083175494618729462206677 119136925655126471770469)
                    ·
                      rfl

theorem cell23_696055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_696055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696055 prefixEnd_696055 := by exact prefixLift 696055
  have htrace : WordTrace (prefixWord ++ tailWord_696055) baseStart_696055 baseEnd_696055 := by
    simpa [prefixWord, tailWord_696055, baseEnd_696055] using wordTrace_append hprefix tailTrace_696055
  have hstable : (prefixWord ++ tailWord_696055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696055).length < 2 ^ (prefixWord ++ tailWord_696055).sum := by decide
  have hdescent : baseEnd_696055 < baseStart_696055 := by decide
  rcases family_descends (prefixWord ++ tailWord_696055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696072 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_696072 : Nat := 118140960795 + 696072 * 2 ^ 59
def prefixEnd_696072 : Nat := 4983230072969 + 3 ^ 40 * 696072 * 2
def baseEnd_696072 : Nat := 119139835378835282932943

theorem tailTrace_696072 : CollatzResearch.WordTrace tailWord_696072 prefixEnd_696072 119139835378835282932943 := by
  unfold tailWord_696072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693915767128749239109235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16925221022838332318812313 12693915767128749239109235)
  ·
    refine ⟨19040873650693123858663853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12693915767128749239109235 19040873650693123858663853)
    ·
      refine ⟨7140327619009921446998945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19040873650693123858663853 7140327619009921446998945)
      ·
        refine ⟨5355245714257441085249209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7140327619009921446998945 5355245714257441085249209)
        ·
          refine ⟨4016434285693080813936907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355245714257441085249209 4016434285693080813936907)
          ·
            refine ⟨6024651428539621220905361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016434285693080813936907 6024651428539621220905361)
            ·
              refine ⟨4518488571404715915679021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024651428539621220905361 4518488571404715915679021)
              ·
                refine ⟨1694433214276768468379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518488571404715915679021 1694433214276768468379633)
                ·
                  refine ⟨1270824910707576351284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694433214276768468379633 1270824910707576351284725)
                  ·
                    refine ⟨119139835378835282932943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1270824910707576351284725 119139835378835282932943)
                    ·
                      rfl

theorem cell23_696072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_696072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696072 prefixEnd_696072 := by exact prefixLift 696072
  have htrace : WordTrace (prefixWord ++ tailWord_696072) baseStart_696072 baseEnd_696072 := by
    simpa [prefixWord, tailWord_696072, baseEnd_696072] using wordTrace_append hprefix tailTrace_696072
  have hstable : (prefixWord ++ tailWord_696072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696072).length < 2 ^ (prefixWord ++ tailWord_696072).sum := by decide
  have hdescent : baseEnd_696072 < baseStart_696072 := by decide
  rcases family_descends (prefixWord ++ tailWord_696072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696126 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_696126 : Nat := 118140960795 + 696126 * 2 ^ 59
def prefixEnd_696126 : Nat := 4983230072969 + 3 ^ 40 * 696126 * 2
def baseEnd_696126 : Nat := 357447234091848637523581

theorem tailTrace_696126 : CollatzResearch.WordTrace tailWord_696126 prefixEnd_696126 357447234091848637523581 := by
  unfold tailWord_696126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173725134507733212585529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16926534050707910467122821 3173725134507733212585529)
  ·
    refine ⟨2380293850880799909439147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173725134507733212585529 2380293850880799909439147)
    ·
      refine ⟨3570440776321199864158721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380293850880799909439147 3570440776321199864158721)
      ·
        refine ⟨2677830582240899898119041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570440776321199864158721 2677830582240899898119041)
        ·
          refine ⟨2008372936680674923589281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677830582240899898119041 2008372936680674923589281)
          ·
            refine ⟨1506279702510506192691961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2008372936680674923589281 1506279702510506192691961)
            ·
              refine ⟨1129709776882879644518971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506279702510506192691961 1129709776882879644518971)
              ·
                refine ⟨1694564665324319466778457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129709776882879644518971 1694564665324319466778457)
                ·
                  refine ⟨1270923498993239600083843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694564665324319466778457 1270923498993239600083843)
                  ·
                    refine ⟨1906385248489859400125765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270923498993239600083843 1906385248489859400125765)
                    ·
                      refine ⟨357447234091848637523581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1906385248489859400125765 357447234091848637523581)
                      ·
                        rfl

theorem cell23_696126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_696126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696126 prefixEnd_696126 := by exact prefixLift 696126
  have htrace : WordTrace (prefixWord ++ tailWord_696126) baseStart_696126 baseEnd_696126 := by
    simpa [prefixWord, tailWord_696126, baseEnd_696126] using wordTrace_append hprefix tailTrace_696126
  have hstable : (prefixWord ++ tailWord_696126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696126).length < 2 ^ (prefixWord ++ tailWord_696126).sum := by decide
  have hdescent : baseEnd_696126 < baseStart_696126 := by decide
  rcases family_descends (prefixWord ++ tailWord_696126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696149 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 6]
def baseStart_696149 : Nat := 118140960795 + 696149 * 2 ^ 59
def prefixEnd_696149 : Nat := 4983230072969 + 3 ^ 40 * 696149 * 2
def baseEnd_696149 : Nat := 39717671571878005281775

theorem tailTrace_696149 : CollatzResearch.WordTrace tailWord_696149 prefixEnd_696149 39717671571878005281775 := by
  unfold tailWord_696149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390639954978540628771501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16927093303319027085847667 25390639954978540628771501)
  ·
    refine ⟨9521489983116952735789313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25390639954978540628771501 9521489983116952735789313)
    ·
      refine ⟨7141117487337714551841985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9521489983116952735789313 7141117487337714551841985)
      ·
        refine ⟨5355838115503285913881489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7141117487337714551841985 5355838115503285913881489)
        ·
          refine ⟨4016878586627464435411117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355838115503285913881489 4016878586627464435411117)
          ·
            refine ⟨1506329469985299163279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4016878586627464435411117 1506329469985299163279169)
            ·
              refine ⟨1129747102488974372459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506329469985299163279169 1129747102488974372459377)
              ·
                refine ⟨847310326866730779344533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129747102488974372459377 847310326866730779344533)
                ·
                  refine ⟨39717671571878005281775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 847310326866730779344533 39717671571878005281775)
                  ·
                    rfl

theorem cell23_696149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_696149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696149 prefixEnd_696149 := by exact prefixLift 696149
  have htrace : WordTrace (prefixWord ++ tailWord_696149) baseStart_696149 baseEnd_696149 := by
    simpa [prefixWord, tailWord_696149, baseEnd_696149] using wordTrace_append hprefix tailTrace_696149
  have hstable : (prefixWord ++ tailWord_696149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696149).length < 2 ^ (prefixWord ++ tailWord_696149).sum := by decide
  have hdescent : baseEnd_696149 < baseStart_696149 := by decide
  rcases family_descends (prefixWord ++ tailWord_696149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696169 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 4, 3, 2]
def baseStart_696169 : Nat := 118140960795 + 696169 * 2 ^ 59
def prefixEnd_696169 : Nat := 4983230072969 + 3 ^ 40 * 696169 * 2
def baseEnd_696169 : Nat := 357469313759991969285883

theorem tailTrace_696169 : CollatzResearch.WordTrace tailWord_696169 prefixEnd_696169 357469313759991969285883 := by
  unfold tailWord_696169
  simp only [CollatzResearch.WordTrace]
  refine ⟨25391369414906084044499561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16927579609937389362999707 25391369414906084044499561)
  ·
    refine ⟨19043527061179563033374671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25391369414906084044499561 19043527061179563033374671)
    ·
      refine ⟨28565290591769344550062007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043527061179563033374671 28565290591769344550062007)
      ·
        refine ⟨42847935887654016825093011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28565290591769344550062007 42847935887654016825093011)
        ·
          refine ⟨64271903831481025237639517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42847935887654016825093011 64271903831481025237639517)
          ·
            refine ⟨24101963936805384464114819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64271903831481025237639517 24101963936805384464114819)
            ·
              refine ⟨36152945905208076696172229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24101963936805384464114819 36152945905208076696172229)
              ·
                refine ⟨6778677357226514380532293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36152945905208076696172229 6778677357226514380532293)
                ·
                  refine ⟨1271002004479971446349805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6778677357226514380532293 1271002004479971446349805)
                  ·
                    refine ⟨476625751679989292381177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271002004479971446349805 476625751679989292381177)
                    ·
                      refine ⟨357469313759991969285883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476625751679989292381177 357469313759991969285883)
                      ·
                        rfl

theorem cell23_696169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3, 2].length) (baseStart_696169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696169 prefixEnd_696169 := by exact prefixLift 696169
  have htrace : WordTrace (prefixWord ++ tailWord_696169) baseStart_696169 baseEnd_696169 := by
    simpa [prefixWord, tailWord_696169, baseEnd_696169] using wordTrace_append hprefix tailTrace_696169
  have hstable : (prefixWord ++ tailWord_696169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696169).length < 2 ^ (prefixWord ++ tailWord_696169).sum := by decide
  have hdescent : baseEnd_696169 < baseStart_696169 := by decide
  rcases family_descends (prefixWord ++ tailWord_696169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696186 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_696186 : Nat := 118140960795 + 696186 * 2 ^ 59
def prefixEnd_696186 : Nat := 4983230072969 + 3 ^ 40 * 696186 * 2
def baseEnd_696186 : Nat := 357478042931118402773305

theorem tailTrace_696186 : CollatzResearch.WordTrace tailWord_696186 prefixEnd_696186 357478042931118402773305 := by
  unfold tailWord_696186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347997363961123986967103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16927992970562997298578941 6347997363961123986967103)
  ·
    refine ⟨9521996045941685980450655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6347997363961123986967103 9521996045941685980450655)
    ·
      refine ⟨14282994068912528970675983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9521996045941685980450655 14282994068912528970675983)
      ·
        refine ⟨21424491103368793456013975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282994068912528970675983 21424491103368793456013975)
        ·
          refine ⟨32136736655053190184020963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21424491103368793456013975 32136736655053190184020963)
          ·
            refine ⟨48205104982579785276031445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136736655053190184020963 48205104982579785276031445)
            ·
              refine ⟨1129807148029213717406987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48205104982579785276031445 1129807148029213717406987)
              ·
                refine ⟨1694710722043820576110481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129807148029213717406987 1694710722043820576110481)
                ·
                  refine ⟨1271033041532865432082861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694710722043820576110481 1271033041532865432082861)
                  ·
                    refine ⟨476637390574824537031073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271033041532865432082861 476637390574824537031073)
                    ·
                      refine ⟨357478042931118402773305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476637390574824537031073 357478042931118402773305)
                      ·
                        rfl

theorem cell23_696186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_696186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696186 prefixEnd_696186 := by exact prefixLift 696186
  have htrace : WordTrace (prefixWord ++ tailWord_696186) baseStart_696186 baseEnd_696186 := by
    simpa [prefixWord, tailWord_696186, baseEnd_696186] using wordTrace_append hprefix tailTrace_696186
  have hstable : (prefixWord ++ tailWord_696186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696186).length < 2 ^ (prefixWord ++ tailWord_696186).sum := by decide
  have hdescent : baseEnd_696186 < baseStart_696186 := by decide
  rcases family_descends (prefixWord ++ tailWord_696186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696192 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_696192 : Nat := 118140960795 + 696192 * 2 ^ 59
def prefixEnd_696192 : Nat := 4983230072969 + 3 ^ 40 * 696192 * 2
def baseEnd_696192 : Nat := 119160374605015126432759

theorem tailTrace_696192 : CollatzResearch.WordTrace tailWord_696192 prefixEnd_696192 119160374605015126432759 := by
  unfold tailWord_696192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696104146911379486293415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16928138862548505981724553 12696104146911379486293415)
  ·
    refine ⟨19044156220367069229440123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12696104146911379486293415 19044156220367069229440123)
    ·
      refine ⟨28566234330550603844160185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19044156220367069229440123 28566234330550603844160185)
      ·
        refine ⟨21424675747912952883120139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28566234330550603844160185 21424675747912952883120139)
        ·
          refine ⟨32137013621869429324680209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21424675747912952883120139 32137013621869429324680209)
          ·
            refine ⟨24102760216402071993510157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32137013621869429324680209 24102760216402071993510157)
            ·
              refine ⟨9038535081150776997566309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24102760216402071993510157 9038535081150776997566309)
              ·
                refine ⟨1694725327715770687043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9038535081150776997566309 1694725327715770687043683)
                ·
                  refine ⟨2542087991573656030565525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694725327715770687043683 2542087991573656030565525)
                  ·
                    refine ⟨119160374605015126432759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2542087991573656030565525 119160374605015126432759)
                    ·
                      rfl

theorem cell23_696192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_696192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696192 prefixEnd_696192 := by exact prefixLift 696192
  have htrace : WordTrace (prefixWord ++ tailWord_696192) baseStart_696192 baseEnd_696192 := by
    simpa [prefixWord, tailWord_696192, baseEnd_696192] using wordTrace_append hprefix tailTrace_696192
  have hstable : (prefixWord ++ tailWord_696192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696192).length < 2 ^ (prefixWord ++ tailWord_696192).sum := by decide
  have hdescent : baseEnd_696192 < baseStart_696192 := by decide
  rcases family_descends (prefixWord ++ tailWord_696192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696196 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_696196 : Nat := 118140960795 + 696196 * 2 ^ 59
def prefixEnd_696196 : Nat := 4983230072969 + 3 ^ 40 * 696196 * 2
def baseEnd_696196 : Nat := 119161059245887787882753

theorem tailTrace_696196 : CollatzResearch.WordTrace tailWord_696196 prefixEnd_696196 119161059245887787882753 := by
  unfold tailWord_696196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696177092904133827866221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16928236123872178437154961 12696177092904133827866221)
  ·
    refine ⟨4761066409839050185449833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12696177092904133827866221 4761066409839050185449833)
    ·
      refine ⟨3570799807379287639087375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4761066409839050185449833 3570799807379287639087375)
      ·
        refine ⟨5356199711068931458631063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3570799807379287639087375 5356199711068931458631063)
        ·
          refine ⟨8034299566603397187946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5356199711068931458631063 8034299566603397187946595)
          ·
            refine ⟨12051449349905095781919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034299566603397187946595 12051449349905095781919893)
            ·
              refine ⟨564911688276801364777495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12051449349905095781919893 564911688276801364777495)
              ·
                refine ⟨847367532415202047166243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564911688276801364777495 847367532415202047166243)
                ·
                  refine ⟨1271051298622803070749365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847367532415202047166243 1271051298622803070749365)
                  ·
                    refine ⟨119161059245887787882753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1271051298622803070749365 119161059245887787882753)
                    ·
                      rfl

theorem cell23_696196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_696196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696196 prefixEnd_696196 := by exact prefixLift 696196
  have htrace : WordTrace (prefixWord ++ tailWord_696196) baseStart_696196 baseEnd_696196 := by
    simpa [prefixWord, tailWord_696196, baseEnd_696196] using wordTrace_append hprefix tailTrace_696196
  have hstable : (prefixWord ++ tailWord_696196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696196).length < 2 ^ (prefixWord ++ tailWord_696196).sum := by decide
  have hdescent : baseEnd_696196 < baseStart_696196 := by decide
  rcases family_descends (prefixWord ++ tailWord_696196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696210 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_696210 : Nat := 118140960795 + 696210 * 2 ^ 59
def prefixEnd_696210 : Nat := 4983230072969 + 3 ^ 40 * 696210 * 2
def baseEnd_696210 : Nat := 357490366466826308873195

theorem tailTrace_696210 : CollatzResearch.WordTrace tailWord_696210 prefixEnd_696210 357490366466826308873195 := by
  unfold tailWord_696210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348216201939387011685521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16928576538505032031161389 6348216201939387011685521)
  ·
    refine ⟨4761162151454540258764141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6348216201939387011685521 4761162151454540258764141)
    ·
      refine ⟨1785435806795452597036553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4761162151454540258764141 1785435806795452597036553)
      ·
        refine ⟨1339076855096589447777415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1785435806795452597036553 1339076855096589447777415)
        ·
          refine ⟨2008615282644884171666123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339076855096589447777415 2008615282644884171666123)
          ·
            refine ⟨3012922923967326257499185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008615282644884171666123 3012922923967326257499185)
            ·
              refine ⟨2259692192975494693124389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012922923967326257499185 2259692192975494693124389)
              ·
                refine ⟨423692286182905254960823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2259692192975494693124389 423692286182905254960823)
                ·
                  refine ⟨635538429274357882441235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423692286182905254960823 635538429274357882441235)
                  ·
                    refine ⟨953307643911536823661853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635538429274357882441235 953307643911536823661853)
                    ·
                      refine ⟨357490366466826308873195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953307643911536823661853 357490366466826308873195)
                      ·
                        rfl

theorem cell23_696210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_696210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696210 prefixEnd_696210 := by exact prefixLift 696210
  have htrace : WordTrace (prefixWord ++ tailWord_696210) baseStart_696210 baseEnd_696210 := by
    simpa [prefixWord, tailWord_696210, baseEnd_696210] using wordTrace_append hprefix tailTrace_696210
  have hstable : (prefixWord ++ tailWord_696210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696210).length < 2 ^ (prefixWord ++ tailWord_696210).sum := by decide
  have hdescent : baseEnd_696210 < baseStart_696210 := by decide
  rcases family_descends (prefixWord ++ tailWord_696210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696242 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_696242 : Nat := 118140960795 + 696242 * 2 ^ 59
def prefixEnd_696242 : Nat := 4983230072969 + 3 ^ 40 * 696242 * 2
def baseEnd_696242 : Nat := 357506797847770183673047

theorem tailTrace_696242 : CollatzResearch.WordTrace tailWord_696242 prefixEnd_696242 357506797847770183673047 := by
  unfold tailWord_696242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348507985910404377976745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16929354629094411674604653 6348507985910404377976745)
  ·
    refine ⟨4761380989432803283482559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6348507985910404377976745 4761380989432803283482559)
    ·
      refine ⟨7142071484149204925223839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761380989432803283482559 7142071484149204925223839)
      ·
        refine ⟨10713107226223807387835759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142071484149204925223839 10713107226223807387835759)
        ·
          refine ⟨16069660839335711081753639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713107226223807387835759 16069660839335711081753639)
          ·
            refine ⟨24104491259003566622630459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069660839335711081753639 24104491259003566622630459)
            ·
              refine ⟨36156736888505349933945689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24104491259003566622630459 36156736888505349933945689)
              ·
                refine ⟨27117552666379012450459267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36156736888505349933945689 27117552666379012450459267)
                ·
                  refine ⟨40676328999568518675688901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27117552666379012450459267 40676328999568518675688901)
                  ·
                    refine ⟨7626811687419097251691669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40676328999568518675688901 7626811687419097251691669)
                    ·
                      refine ⟨357506797847770183673047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7626811687419097251691669 357506797847770183673047)
                      ·
                        rfl

theorem cell23_696242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_696242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696242 prefixEnd_696242 := by exact prefixLift 696242
  have htrace : WordTrace (prefixWord ++ tailWord_696242) baseStart_696242 baseEnd_696242 := by
    simpa [prefixWord, tailWord_696242, baseEnd_696242] using wordTrace_append hprefix tailTrace_696242
  have hstable : (prefixWord ++ tailWord_696242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696242).length < 2 ^ (prefixWord ++ tailWord_696242).sum := by decide
  have hdescent : baseEnd_696242 < baseStart_696242 := by decide
  rcases family_descends (prefixWord ++ tailWord_696242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696244 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_696244 : Nat := 118140960795 + 696244 * 2 ^ 59
def prefixEnd_696244 : Nat := 4983230072969 + 3 ^ 40 * 696244 * 2
def baseEnd_696244 : Nat := 357507824809079175848039

theorem tailTrace_696244 : CollatzResearch.WordTrace tailWord_696244 prefixEnd_696244 357507824809079175848039 := by
  unfold tailWord_696244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697052444817185926739893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16929403259756247902319857 12697052444817185926739893)
  ·
    refine ⟨1190348666701611180631865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12697052444817185926739893 1190348666701611180631865)
    ·
      refine ⟨892761500026208385473899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190348666701611180631865 892761500026208385473899)
      ·
        refine ⟨1339142250039312578210849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892761500026208385473899 1339142250039312578210849)
        ·
          refine ⟨1004356687529484433658137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339142250039312578210849 1004356687529484433658137)
          ·
            refine ⟨753267515647113325243603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004356687529484433658137 753267515647113325243603)
            ·
              refine ⟨1129901273470669987865405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753267515647113325243603 1129901273470669987865405)
              ·
                refine ⟨423712977551501245449527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1129901273470669987865405 423712977551501245449527)
                ·
                  refine ⟨635569466327251868174291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423712977551501245449527 635569466327251868174291)
                  ·
                    refine ⟨953354199490877802261437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635569466327251868174291 953354199490877802261437)
                    ·
                      refine ⟨357507824809079175848039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953354199490877802261437 357507824809079175848039)
                      ·
                        rfl

theorem cell23_696244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_696244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696244 prefixEnd_696244 := by exact prefixLift 696244
  have htrace : WordTrace (prefixWord ++ tailWord_696244) baseStart_696244 baseEnd_696244 := by
    simpa [prefixWord, tailWord_696244, baseEnd_696244] using wordTrace_append hprefix tailTrace_696244
  have hstable : (prefixWord ++ tailWord_696244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696244).length < 2 ^ (prefixWord ++ tailWord_696244).sum := by decide
  have hdescent : baseEnd_696244 < baseStart_696244 := by decide
  rcases family_descends (prefixWord ++ tailWord_696244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696249 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_696249 : Nat := 118140960795 + 696249 * 2 ^ 59
def prefixEnd_696249 : Nat := 4983230072969 + 3 ^ 40 * 696249 * 2
def baseEnd_696249 : Nat := 357510392212351656285515

theorem tailTrace_696249 : CollatzResearch.WordTrace tailWord_696249 prefixEnd_696249 357510392212351656285515 := by
  unfold tailWord_696249
  simp only [CollatzResearch.WordTrace]
  refine ⟨25394287254616257707411801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16929524836410838471607867 25394287254616257707411801)
  ·
    refine ⟨19045715440962193280558851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25394287254616257707411801 19045715440962193280558851)
    ·
      refine ⟨28568573161443289920838277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19045715440962193280558851 28568573161443289920838277)
      ·
        refine ⟨5356607467770616860157177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28568573161443289920838277 5356607467770616860157177)
        ·
          refine ⟨4017455600827962645117883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5356607467770616860157177 4017455600827962645117883)
          ·
            refine ⟨6026183401241943967676825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017455600827962645117883 6026183401241943967676825)
            ·
              refine ⟨4519637550931457975757619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6026183401241943967676825 4519637550931457975757619)
              ·
                refine ⟨6779456326397186963636429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519637550931457975757619 6779456326397186963636429)
                ·
                  refine ⟨2542296122398945111363661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6779456326397186963636429 2542296122398945111363661)
                  ·
                    refine ⟨953361045899604416761373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542296122398945111363661 953361045899604416761373)
                    ·
                      refine ⟨357510392212351656285515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953361045899604416761373 357510392212351656285515)
                      ·
                        rfl

theorem cell23_696249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_696249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696249 prefixEnd_696249 := by exact prefixLift 696249
  have htrace : WordTrace (prefixWord ++ tailWord_696249) baseStart_696249 baseEnd_696249 := by
    simpa [prefixWord, tailWord_696249, baseEnd_696249] using wordTrace_append hprefix tailTrace_696249
  have hstable : (prefixWord ++ tailWord_696249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696249).length < 2 ^ (prefixWord ++ tailWord_696249).sum := by decide
  have hdescent : baseEnd_696249 < baseStart_696249 := by decide
  rcases family_descends (prefixWord ++ tailWord_696249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696266 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_696266 : Nat := 118140960795 + 696266 * 2 ^ 59
def prefixEnd_696266 : Nat := 4983230072969 + 3 ^ 40 * 696266 * 2
def baseEnd_696266 : Nat := 357519121383478089772937

theorem tailTrace_696266 : CollatzResearch.WordTrace tailWord_696266 prefixEnd_696266 357519121383478089772937 := by
  unfold tailWord_696266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348726823888667402695163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16929938197036446407187101 6348726823888667402695163)
  ·
    refine ⟨9523090235833001104042745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348726823888667402695163 9523090235833001104042745)
    ·
      refine ⟨7142317676874750828032059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9523090235833001104042745 7142317676874750828032059)
      ·
        refine ⟨10713476515312126242048089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142317676874750828032059 10713476515312126242048089)
        ·
          refine ⟨8035107386484094681536067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10713476515312126242048089 8035107386484094681536067)
          ·
            refine ⟨12052661079726142022304101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035107386484094681536067 12052661079726142022304101)
            ·
              refine ⟨2259873952448651629182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12052661079726142022304101 2259873952448651629182019)
              ·
                refine ⟨3389810928672977443773029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259873952448651629182019 3389810928672977443773029)
                ·
                  refine ⟨635589549126183270707443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3389810928672977443773029 635589549126183270707443)
                  ·
                    refine ⟨953384323689274906061165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635589549126183270707443 953384323689274906061165)
                    ·
                      refine ⟨357519121383478089772937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953384323689274906061165 357519121383478089772937)
                      ·
                        rfl

theorem cell23_696266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_696266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696266 prefixEnd_696266 := by exact prefixLift 696266
  have htrace : WordTrace (prefixWord ++ tailWord_696266) baseStart_696266 baseEnd_696266 := by
    simpa [prefixWord, tailWord_696266, baseEnd_696266] using wordTrace_append hprefix tailTrace_696266
  have hstable : (prefixWord ++ tailWord_696266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696266).length < 2 ^ (prefixWord ++ tailWord_696266).sum := by decide
  have hdescent : baseEnd_696266 < baseStart_696266 := by decide
  rcases family_descends (prefixWord ++ tailWord_696266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696284 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_696284 : Nat := 118140960795 + 696284 * 2 ^ 59
def prefixEnd_696284 : Nat := 4983230072969 + 3 ^ 40 * 696284 * 2
def baseEnd_696284 : Nat := 357528364035259019347855

theorem tailTrace_696284 : CollatzResearch.WordTrace tailWord_696284 prefixEnd_696284 357528364035259019347855 := by
  unfold tailWord_696284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697781904744729342467953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16930375872992972456623937 12697781904744729342467953)
  ·
    refine ⟨9523336428558547006850965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12697781904744729342467953 9523336428558547006850965)
    ·
      refine ⟨446406395088681890946139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9523336428558547006850965 446406395088681890946139)
      ·
        refine ⟨669609592633022836419209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446406395088681890946139 669609592633022836419209)
        ·
          refine ⟨502207194474767127314407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669609592633022836419209 502207194474767127314407)
          ·
            refine ⟨753310791712150690971611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502207194474767127314407 753310791712150690971611)
            ·
              refine ⟨1129966187568226036457417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753310791712150690971611 1129966187568226036457417)
              ·
                refine ⟨847474640676169527343063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129966187568226036457417 847474640676169527343063)
                ·
                  refine ⟨1271211961014254291014595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847474640676169527343063 1271211961014254291014595)
                  ·
                    refine ⟨1906817941521381436521893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271211961014254291014595 1906817941521381436521893)
                    ·
                      refine ⟨357528364035259019347855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1906817941521381436521893 357528364035259019347855)
                      ·
                        rfl

theorem cell23_696284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_696284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696284 prefixEnd_696284 := by exact prefixLift 696284
  have htrace : WordTrace (prefixWord ++ tailWord_696284) baseStart_696284 baseEnd_696284 := by
    simpa [prefixWord, tailWord_696284, baseEnd_696284] using wordTrace_append hprefix tailTrace_696284
  have hstable : (prefixWord ++ tailWord_696284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696284).length < 2 ^ (prefixWord ++ tailWord_696284).sum := by decide
  have hdescent : baseEnd_696284 < baseStart_696284 := by decide
  rcases family_descends (prefixWord ++ tailWord_696284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696339 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3]
def baseStart_696339 : Nat := 118140960795 + 696339 * 2 ^ 59
def prefixEnd_696339 : Nat := 4983230072969 + 3 ^ 40 * 696339 * 2
def baseEnd_696339 : Nat := 357556605471256304160101

theorem tailTrace_696339 : CollatzResearch.WordTrace tailWord_696339 prefixEnd_696339 357556605471256304160101 := by
  unfold tailWord_696339
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397569824290203078188071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16931713216193468718792047 25397569824290203078188071)
  ·
    refine ⟨38096354736435304617282107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25397569824290203078188071 38096354736435304617282107)
    ·
      refine ⟨57144532104652956925923161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38096354736435304617282107 57144532104652956925923161)
      ·
        refine ⟨42858399078489717694442371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57144532104652956925923161 42858399078489717694442371)
        ·
          refine ⟨64287598617734576541663557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42858399078489717694442371 64287598617734576541663557)
          ·
            refine ⟨12053924740825233101561917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64287598617734576541663557 12053924740825233101561917)
            ·
              refine ⟨4520221777809462413085719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12053924740825233101561917 4520221777809462413085719)
              ·
                refine ⟨6780332666714193619628579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520221777809462413085719 6780332666714193619628579)
                ·
                  refine ⟨10170499000071290429442869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6780332666714193619628579 10170499000071290429442869)
                  ·
                    refine ⟨953484281256683477760269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10170499000071290429442869 953484281256683477760269)
                    ·
                      refine ⟨357556605471256304160101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953484281256683477760269 357556605471256304160101)
                      ·
                        rfl

theorem cell23_696339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_696339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696339 prefixEnd_696339 := by exact prefixLift 696339
  have htrace : WordTrace (prefixWord ++ tailWord_696339) baseStart_696339 baseEnd_696339 := by
    simpa [prefixWord, tailWord_696339, baseEnd_696339] using wordTrace_append hprefix tailTrace_696339
  have hstable : (prefixWord ++ tailWord_696339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696339).length < 2 ^ (prefixWord ++ tailWord_696339).sum := by decide
  have hdescent : baseEnd_696339 < baseStart_696339 := by decide
  rcases family_descends (prefixWord ++ tailWord_696339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696409 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_696409 : Nat := 118140960795 + 696409 * 2 ^ 59
def prefixEnd_696409 : Nat := 4983230072969 + 3 ^ 40 * 696409 * 2
def baseEnd_696409 : Nat := 357592549117071030284779

theorem tailTrace_696409 : CollatzResearch.WordTrace tailWord_696409 prefixEnd_696409 357592549117071030284779 := by
  unfold tailWord_696409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400122934036605033236281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16933415289357736688824187 25400122934036605033236281)
  ·
    refine ⟨19050092200527453774927211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25400122934036605033236281 19050092200527453774927211)
    ·
      refine ⟨28575138300791180662390817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050092200527453774927211 28575138300791180662390817)
      ·
        refine ⟨21431353725593385496793113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28575138300791180662390817 21431353725593385496793113)
        ·
          refine ⟨16073515294195039122594835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21431353725593385496793113 16073515294195039122594835)
          ·
            refine ⟨24110272941292558683892253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16073515294195039122594835 24110272941292558683892253)
            ·
              refine ⟨9041352352984709506459595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24110272941292558683892253 9041352352984709506459595)
              ·
                refine ⟨13562028529477064259689393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041352352984709506459595 13562028529477064259689393)
                ·
                  refine ⟨10171521397107798194767045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562028529477064259689393 10171521397107798194767045)
                  ·
                    refine ⟨1907160261957712161518821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10171521397107798194767045 1907160261957712161518821)
                    ·
                      refine ⟨357592549117071030284779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1907160261957712161518821 357592549117071030284779)
                      ·
                        rfl

theorem cell23_696409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_696409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696409 prefixEnd_696409 := by exact prefixLift 696409
  have htrace : WordTrace (prefixWord ++ tailWord_696409) baseStart_696409 baseEnd_696409 := by
    simpa [prefixWord, tailWord_696409, baseEnd_696409] using wordTrace_append hprefix tailTrace_696409
  have hstable : (prefixWord ++ tailWord_696409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696409).length < 2 ^ (prefixWord ++ tailWord_696409).sum := by decide
  have hdescent : baseEnd_696409 < baseStart_696409 := by decide
  rcases family_descends (prefixWord ++ tailWord_696409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696413 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_696413 : Nat := 118140960795 + 696413 * 2 ^ 59
def prefixEnd_696413 : Nat := 4983230072969 + 3 ^ 40 * 696413 * 2
def baseEnd_696413 : Nat := 357594603039689014634761

theorem tailTrace_696413 : CollatzResearch.WordTrace tailWord_696413 prefixEnd_696413 357594603039689014634761 := by
  unfold tailWord_696413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400268826022113716381893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16933512550681409144254595 25400268826022113716381893)
  ·
    refine ⟨4762550404879146321821605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25400268826022113716381893 4762550404879146321821605)
    ·
      refine ⟨892978200914839935341551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4762550404879146321821605 892978200914839935341551)
      ·
        refine ⟨1339467301372259903012327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892978200914839935341551 1339467301372259903012327)
        ·
          refine ⟨2009200952058389854518491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339467301372259903012327 2009200952058389854518491)
          ·
            refine ⟨3013801428087584781777737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009200952058389854518491 3013801428087584781777737)
            ·
              refine ⟨2260351071065688586333303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013801428087584781777737 2260351071065688586333303)
              ·
                refine ⟨3390526606598532879499955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260351071065688586333303 3390526606598532879499955)
                ·
                  refine ⟨5085789909897799319249933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390526606598532879499955 5085789909897799319249933)
                  ·
                    refine ⟨1907171216211674744718725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5085789909897799319249933 1907171216211674744718725)
                    ·
                      refine ⟨357594603039689014634761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1907171216211674744718725 357594603039689014634761)
                      ·
                        rfl

theorem cell23_696413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_696413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696413 prefixEnd_696413 := by exact prefixLift 696413
  have htrace : WordTrace (prefixWord ++ tailWord_696413) baseStart_696413 baseEnd_696413 := by
    simpa [prefixWord, tailWord_696413, baseEnd_696413] using wordTrace_append hprefix tailTrace_696413
  have hstable : (prefixWord ++ tailWord_696413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696413).length < 2 ^ (prefixWord ++ tailWord_696413).sum := by decide
  have hdescent : baseEnd_696413 < baseStart_696413 := by decide
  rcases family_descends (prefixWord ++ tailWord_696413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696414 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_696414 : Nat := 118140960795 + 696414 * 2 ^ 59
def prefixEnd_696414 : Nat := 4983230072969 + 3 ^ 40 * 696414 * 2
def baseEnd_696414 : Nat := 39732790724482612302473

theorem tailTrace_696414 : CollatzResearch.WordTrace tailWord_696414 prefixEnd_696414 39732790724482612302473 := by
  unfold tailWord_696414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175038162377311360896037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16933536866012327258112197 3175038162377311360896037)
  ·
    refine ⟨595319655445745880168007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3175038162377311360896037 595319655445745880168007)
    ·
      refine ⟨892979483168618820252011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595319655445745880168007 892979483168618820252011)
      ·
        refine ⟨1339469224752928230378017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892979483168618820252011 1339469224752928230378017)
        ·
          refine ⟨1004601918564696172783513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339469224752928230378017 1004601918564696172783513)
          ·
            refine ⟨753451438923522129587635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004601918564696172783513 753451438923522129587635)
            ·
              refine ⟨1130177158385283194381453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753451438923522129587635 1130177158385283194381453)
              ·
                refine ⟨423816434394481197893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130177158385283194381453 423816434394481197893045)
                ·
                  refine ⟨39732790724482612302473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 423816434394481197893045 39732790724482612302473)
                  ·
                    rfl

theorem cell23_696414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_696414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696414 prefixEnd_696414 := by exact prefixLift 696414
  have htrace : WordTrace (prefixWord ++ tailWord_696414) baseStart_696414 baseEnd_696414 := by
    simpa [prefixWord, tailWord_696414, baseEnd_696414] using wordTrace_append hprefix tailTrace_696414
  have hstable : (prefixWord ++ tailWord_696414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696414).length < 2 ^ (prefixWord ++ tailWord_696414).sum := by decide
  have hdescent : baseEnd_696414 < baseStart_696414 := by decide
  rcases family_descends (prefixWord ++ tailWord_696414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696416 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_696416 : Nat := 118140960795 + 696416 * 2 ^ 59
def prefixEnd_696416 : Nat := 4983230072969 + 3 ^ 40 * 696416 * 2
def baseEnd_696416 : Nat := 357596143481652502897247

theorem tailTrace_696416 : CollatzResearch.WordTrace tailWord_696416 prefixEnd_696416 357596143481652502897247 := by
  unfold tailWord_696416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700189122505622614370551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16933585496674163485827401 12700189122505622614370551)
  ·
    refine ⟨19050283683758433921555827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12700189122505622614370551 19050283683758433921555827)
    ·
      refine ⟨28575425525637650882333741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050283683758433921555827 28575425525637650882333741)
      ·
        refine ⟨10715784572114119080875153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28575425525637650882333741 10715784572114119080875153)
        ·
          refine ⟨8036838429085589310656365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10715784572114119080875153 8036838429085589310656365)
          ·
            refine ⟨3013814410907095991496137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8036838429085589310656365 3013814410907095991496137)
            ·
              refine ⟨2260360808180321993622103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013814410907095991496137 2260360808180321993622103)
              ·
                refine ⟨3390541212270482990433155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260360808180321993622103 3390541212270482990433155)
                ·
                  refine ⟨5085811818405724485649733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390541212270482990433155 5085811818405724485649733)
                  ·
                    refine ⟨953589715951073341059325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5085811818405724485649733 953589715951073341059325)
                    ·
                      refine ⟨357596143481652502897247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953589715951073341059325 357596143481652502897247)
                      ·
                        rfl

theorem cell23_696416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_696416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696416 prefixEnd_696416 := by exact prefixLift 696416
  have htrace : WordTrace (prefixWord ++ tailWord_696416) baseStart_696416 baseEnd_696416 := by
    simpa [prefixWord, tailWord_696416, baseEnd_696416] using wordTrace_append hprefix tailTrace_696416
  have hstable : (prefixWord ++ tailWord_696416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696416).length < 2 ^ (prefixWord ++ tailWord_696416).sum := by decide
  have hdescent : baseEnd_696416 < baseStart_696416 := by decide
  rcases family_descends (prefixWord ++ tailWord_696416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696419 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 8]
def baseStart_696419 : Nat := 118140960795 + 696419 * 2 ^ 59
def prefixEnd_696419 : Nat := 4983230072969 + 3 ^ 40 * 696419 * 2
def baseEnd_696419 : Nat := 39733075991512887906637

theorem tailTrace_696419 : CollatzResearch.WordTrace tailWord_696419 prefixEnd_696419 39733075991512887906637 := by
  unfold tailWord_696419
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400487664000376741100311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16933658442666917827400207 25400487664000376741100311)
  ·
    refine ⟨38100731496000565111650467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25400487664000376741100311 38100731496000565111650467)
    ·
      refine ⟨57151097244000847667475701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38100731496000565111650467 57151097244000847667475701)
      ·
        refine ⟨5357915366625079468825847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57151097244000847667475701 5357915366625079468825847)
        ·
          refine ⟨8036873049937619203238771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357915366625079468825847 8036873049937619203238771)
          ·
            refine ⟨12055309574906428804858157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036873049937619203238771 12055309574906428804858157)
            ·
              refine ⟨4520741090589910801821809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12055309574906428804858157 4520741090589910801821809)
              ·
                refine ⟨3390555817942433101366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4520741090589910801821809 3390555817942433101366357)
                ·
                  refine ⟨39733075991512887906637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3390555817942433101366357 39733075991512887906637)
                  ·
                    rfl

theorem cell23_696419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 8].length) (baseStart_696419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696419 prefixEnd_696419 := by exact prefixLift 696419
  have htrace : WordTrace (prefixWord ++ tailWord_696419) baseStart_696419 baseEnd_696419 := by
    simpa [prefixWord, tailWord_696419, baseEnd_696419] using wordTrace_append hprefix tailTrace_696419
  have hstable : (prefixWord ++ tailWord_696419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696419).length < 2 ^ (prefixWord ++ tailWord_696419).sum := by decide
  have hdescent : baseEnd_696419 < baseStart_696419 := by decide
  rcases family_descends (prefixWord ++ tailWord_696419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696453 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 6]
def baseStart_696453 : Nat := 118140960795 + 696453 * 2 ^ 59
def prefixEnd_696453 : Nat := 4983230072969 + 3 ^ 40 * 696453 * 2
def baseEnd_696453 : Nat := 39735015807318762014953

theorem tailTrace_696453 : CollatzResearch.WordTrace tailWord_696453 prefixEnd_696453 39735015807318762014953 := by
  unfold tailWord_696453
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401727745877200547838013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16934485163918133698558675 25401727745877200547838013)
  ·
    refine ⟨9525647904703950205439255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25401727745877200547838013 9525647904703950205439255)
    ·
      refine ⟨14288471857055925308158883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525647904703950205439255 14288471857055925308158883)
      ·
        refine ⟨21432707785583887962238325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288471857055925308158883 21432707785583887962238325)
        ·
          refine ⟨2009316354898489496459843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21432707785583887962238325 2009316354898489496459843)
          ·
            refine ⟨3013974532347734244689765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009316354898489496459843 3013974532347734244689765)
            ·
              refine ⟨565120224815200170879331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3013974532347734244689765 565120224815200170879331)
              ·
                refine ⟨847680337222800256318997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565120224815200170879331 847680337222800256318997)
                ·
                  refine ⟨39735015807318762014953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 847680337222800256318997 39735015807318762014953)
                  ·
                    rfl

theorem cell23_696453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_696453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696453 prefixEnd_696453 := by exact prefixLift 696453
  have htrace : WordTrace (prefixWord ++ tailWord_696453) baseStart_696453 baseEnd_696453 := by
    simpa [prefixWord, tailWord_696453, baseEnd_696453] using wordTrace_append hprefix tailTrace_696453
  have hstable : (prefixWord ++ tailWord_696453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696453).length < 2 ^ (prefixWord ++ tailWord_696453).sum := by decide
  have hdescent : baseEnd_696453 < baseStart_696453 := by decide
  rcases family_descends (prefixWord ++ tailWord_696453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696506 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_696506 : Nat := 118140960795 + 696506 * 2 ^ 59
def prefixEnd_696506 : Nat := 4983230072969 + 3 ^ 40 * 696506 * 2
def baseEnd_696506 : Nat := 357642356740557150771833

theorem tailTrace_696506 : CollatzResearch.WordTrace tailWord_696506 prefixEnd_696506 357642356740557150771833 := by
  unfold tailWord_696506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350915203671297649879343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16935773876456793733011581 6350915203671297649879343)
  ·
    refine ⟨9526372805506946474819015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350915203671297649879343 9526372805506946474819015)
    ·
      refine ⟨14289559208260419712228523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526372805506946474819015 14289559208260419712228523)
      ·
        refine ⟨21434338812390629568342785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14289559208260419712228523 21434338812390629568342785)
        ·
          refine ⟨16075754109292972176257089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21434338812390629568342785 16075754109292972176257089)
          ·
            refine ⟨12056815581969729132192817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16075754109292972176257089 12056815581969729132192817)
            ·
              refine ⟨9042611686477296849144613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12056815581969729132192817 9042611686477296849144613)
              ·
                refine ⟨1695489691214493159214615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9042611686477296849144613 1695489691214493159214615)
                ·
                  refine ⟨2543234536821739738821923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695489691214493159214615 2543234536821739738821923)
                  ·
                    refine ⟨3814851805232609608232885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2543234536821739738821923 3814851805232609608232885)
                    ·
                      refine ⟨357642356740557150771833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3814851805232609608232885 357642356740557150771833)
                      ·
                        rfl

theorem cell23_696506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_696506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696506 prefixEnd_696506 := by exact prefixLift 696506
  have htrace : WordTrace (prefixWord ++ tailWord_696506) baseStart_696506 baseEnd_696506 := by
    simpa [prefixWord, tailWord_696506, baseEnd_696506] using wordTrace_append hprefix tailTrace_696506
  have hstable : (prefixWord ++ tailWord_696506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696506).length < 2 ^ (prefixWord ++ tailWord_696506).sum := by decide
  have hdescent : baseEnd_696506 < baseStart_696506 := by decide
  rcases family_descends (prefixWord ++ tailWord_696506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696514 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_696514 : Nat := 118140960795 + 696514 * 2 ^ 59
def prefixEnd_696514 : Nat := 4983230072969 + 3 ^ 40 * 696514 * 2
def baseEnd_696514 : Nat := 357646464585793119471797

theorem tailTrace_696514 : CollatzResearch.WordTrace tailWord_696514 prefixEnd_696514 357646464585793119471797 := by
  unfold tailWord_696514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350988149664051991452149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16935968399104138643872397 6350988149664051991452149)
  ·
    refine ⟨595405139031004874198639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6350988149664051991452149 595405139031004874198639)
    ·
      refine ⟨893107708546507311297959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595405139031004874198639 893107708546507311297959)
      ·
        refine ⟨1339661562819760966946939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893107708546507311297959 1339661562819760966946939)
        ·
          refine ⟨2009492344229641450420409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339661562819760966946939 2009492344229641450420409)
          ·
            refine ⟨1507119258172231087815307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009492344229641450420409 1507119258172231087815307)
            ·
              refine ⟨2260678887258346631722961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507119258172231087815307 2260678887258346631722961)
              ·
                refine ⟨1695509165443759973792221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260678887258346631722961 1695509165443759973792221)
                ·
                  refine ⟨635815937041409990172083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1695509165443759973792221 635815937041409990172083)
                  ·
                    refine ⟨953723905562114985258125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635815937041409990172083 953723905562114985258125)
                    ·
                      refine ⟨357646464585793119471797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953723905562114985258125 357646464585793119471797)
                      ·
                        rfl

theorem cell23_696514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_696514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696514 prefixEnd_696514 := by exact prefixLift 696514
  have htrace : WordTrace (prefixWord ++ tailWord_696514) baseStart_696514 baseEnd_696514 := by
    simpa [prefixWord, tailWord_696514, baseEnd_696514] using wordTrace_append hprefix tailTrace_696514
  have hstable : (prefixWord ++ tailWord_696514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696514).length < 2 ^ (prefixWord ++ tailWord_696514).sum := by decide
  have hdescent : baseEnd_696514 < baseStart_696514 := by decide
  rcases family_descends (prefixWord ++ tailWord_696514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696523 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 3]
def baseStart_696523 : Nat := 118140960795 + 696523 * 2 ^ 59
def prefixEnd_696523 : Nat := 4983230072969 + 3 ^ 40 * 696523 * 2
def baseEnd_696523 : Nat := 357651085911683584259255

theorem tailTrace_696523 : CollatzResearch.WordTrace tailWord_696523 prefixEnd_696523 357651085911683584259255 := by
  unfold tailWord_696523
  simp only [CollatzResearch.WordTrace]
  refine ⟨25404280855623602502886223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16936187237082401668590815 25404280855623602502886223)
  ·
    refine ⟨38106421283435403754329335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25404280855623602502886223 38106421283435403754329335)
    ·
      refine ⟨57159631925153105631494003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38106421283435403754329335 57159631925153105631494003)
      ·
        refine ⟨85739447887729658447241005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57159631925153105631494003 85739447887729658447241005)
        ·
          refine ⟨32152292957898621917715377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85739447887729658447241005 32152292957898621917715377)
          ·
            refine ⟨24114219718423966438286533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32152292957898621917715377 24114219718423966438286533)
            ·
              refine ⟨4521416197204493707178725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24114219718423966438286533 4521416197204493707178725)
              ·
                refine ⟨847765536975842570096011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4521416197204493707178725 847765536975842570096011)
                ·
                  refine ⟨1271648305463763855144017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847765536975842570096011 1271648305463763855144017)
                  ·
                    refine ⟨953736229097822891358013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271648305463763855144017 953736229097822891358013)
                    ·
                      refine ⟨357651085911683584259255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953736229097822891358013 357651085911683584259255)
                      ·
                        rfl

theorem cell23_696523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 3].length) (baseStart_696523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696523 prefixEnd_696523 := by exact prefixLift 696523
  have htrace : WordTrace (prefixWord ++ tailWord_696523) baseStart_696523 baseEnd_696523 := by
    simpa [prefixWord, tailWord_696523, baseEnd_696523] using wordTrace_append hprefix tailTrace_696523
  have hstable : (prefixWord ++ tailWord_696523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696523).length < 2 ^ (prefixWord ++ tailWord_696523).sum := by decide
  have hdescent : baseEnd_696523 < baseStart_696523 := by decide
  rcases family_descends (prefixWord ++ tailWord_696523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696524 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_696524 : Nat := 118140960795 + 696524 * 2 ^ 59
def prefixEnd_696524 : Nat := 4983230072969 + 3 ^ 40 * 696524 * 2
def baseEnd_696524 : Nat := 357651599392338080346751

theorem tailTrace_696524 : CollatzResearch.WordTrace tailWord_696524 prefixEnd_696524 357651599392338080346751 := by
  unfold tailWord_696524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702158664309989836836313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16936211552413319782448417 12702158664309989836836313)
  ·
    refine ⟨9526618998232492377627235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12702158664309989836836313 9526618998232492377627235)
    ·
      refine ⟨14289928497348738566440853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526618998232492377627235 14289928497348738566440853)
      ·
        refine ⟨669840398313222120301915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14289928497348738566440853 669840398313222120301915)
        ·
          refine ⟨1004760597469833180452873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669840398313222120301915 1004760597469833180452873)
          ·
            refine ⟨753570448102374885339655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004760597469833180452873 753570448102374885339655)
            ·
              refine ⟨1130355672153562328009483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753570448102374885339655 1130355672153562328009483)
              ·
                refine ⟨1695533508230343492014225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130355672153562328009483 1695533508230343492014225)
                ·
                  refine ⟨1271650131172757619010669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695533508230343492014225 1271650131172757619010669)
                  ·
                    refine ⟨476868799189784107129001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271650131172757619010669 476868799189784107129001)
                    ·
                      refine ⟨357651599392338080346751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476868799189784107129001 357651599392338080346751)
                      ·
                        rfl

theorem cell23_696524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_696524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696524 prefixEnd_696524 := by exact prefixLift 696524
  have htrace : WordTrace (prefixWord ++ tailWord_696524) baseStart_696524 baseEnd_696524 := by
    simpa [prefixWord, tailWord_696524, baseEnd_696524] using wordTrace_append hprefix tailTrace_696524
  have hstable : (prefixWord ++ tailWord_696524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696524).length < 2 ^ (prefixWord ++ tailWord_696524).sum := by decide
  have hdescent : baseEnd_696524 < baseStart_696524 := by decide
  rcases family_descends (prefixWord ++ tailWord_696524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696534 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_696534 : Nat := 118140960795 + 696534 * 2 ^ 59
def prefixEnd_696534 : Nat := 4983230072969 + 3 ^ 40 * 696534 * 2
def baseEnd_696534 : Nat := 119218911399627680407235

theorem tailTrace_696534 : CollatzResearch.WordTrace tailWord_696534 prefixEnd_696534 119218911399627680407235 := by
  unfold tailWord_696534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587792628661484461346041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16936454705722500921024437 1587792628661484461346041)
  ·
    refine ⟨1190844471496113346009531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1587792628661484461346041 1190844471496113346009531)
    ·
      refine ⟨1786266707244170019014297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190844471496113346009531 1786266707244170019014297)
      ·
        refine ⟨1339700030433127514260723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1786266707244170019014297 1339700030433127514260723)
        ·
          refine ⟨2009550045649691271391085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339700030433127514260723 2009550045649691271391085)
          ·
            refine ⟨753581267118634226771657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2009550045649691271391085 753581267118634226771657)
            ·
              refine ⟨565185950338975670078743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753581267118634226771657 565185950338975670078743)
              ·
                refine ⟨847778925508463505118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565185950338975670078743 847778925508463505118115)
                ·
                  refine ⟨1271668388262695257677173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847778925508463505118115 1271668388262695257677173)
                  ·
                    refine ⟨119218911399627680407235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1271668388262695257677173 119218911399627680407235)
                    ·
                      rfl

theorem cell23_696534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_696534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696534 prefixEnd_696534 := by exact prefixLift 696534
  have htrace : WordTrace (prefixWord ++ tailWord_696534) baseStart_696534 baseEnd_696534 := by
    simpa [prefixWord, tailWord_696534, baseEnd_696534] using wordTrace_append hprefix tailTrace_696534
  have hstable : (prefixWord ++ tailWord_696534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696534).length < 2 ^ (prefixWord ++ tailWord_696534).sum := by decide
  have hdescent : baseEnd_696534 < baseStart_696534 := by decide
  rcases family_descends (prefixWord ++ tailWord_696534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696537 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 1, 2, 2]
def baseStart_696537 : Nat := 118140960795 + 696537 * 2 ^ 59
def prefixEnd_696537 : Nat := 4983230072969 + 3 ^ 40 * 696537 * 2
def baseEnd_696537 : Nat := 357658274640846529484191

theorem tailTrace_696537 : CollatzResearch.WordTrace tailWord_696537 prefixEnd_696537 357658274640846529484191 := by
  unfold tailWord_696537
  simp only [CollatzResearch.WordTrace]
  refine ⟨25404791477572882893895865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16936527651715255262597243 25404791477572882893895865)
  ·
    refine ⟨19053593608179662170421899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25404791477572882893895865 19053593608179662170421899)
    ·
      refine ⟨28580390412269493255632849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19053593608179662170421899 28580390412269493255632849)
      ·
        refine ⟨21435292809202119941724637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28580390412269493255632849 21435292809202119941724637)
        ·
          refine ⟨8038234803450794978146739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21435292809202119941724637 8038234803450794978146739)
          ·
            refine ⟨12057352205176192467220109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038234803450794978146739 12057352205176192467220109)
            ·
              refine ⟨4521507076941072175207541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12057352205176192467220109 4521507076941072175207541)
              ·
                refine ⟨423891288463225516425707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4521507076941072175207541 423891288463225516425707)
                ·
                  refine ⟨635836932694838274638561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423891288463225516425707 635836932694838274638561)
                  ·
                    refine ⟨476877699521128705978921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 635836932694838274638561 476877699521128705978921)
                    ·
                      refine ⟨357658274640846529484191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476877699521128705978921 357658274640846529484191)
                      ·
                        rfl

theorem cell23_696537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_696537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696537 prefixEnd_696537 := by exact prefixLift 696537
  have htrace : WordTrace (prefixWord ++ tailWord_696537) baseStart_696537 baseEnd_696537 := by
    simpa [prefixWord, tailWord_696537, baseEnd_696537] using wordTrace_append hprefix tailTrace_696537
  have hstable : (prefixWord ++ tailWord_696537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696537).length < 2 ^ (prefixWord ++ tailWord_696537).sum := by decide
  have hdescent : baseEnd_696537 < baseStart_696537 := by decide
  rcases family_descends (prefixWord ++ tailWord_696537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696553 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_696553 : Nat := 118140960795 + 696553 * 2 ^ 59
def prefixEnd_696553 : Nat := 4983230072969 + 3 ^ 40 * 696553 * 2
def baseEnd_696553 : Nat := 357666490331318466884117

theorem tailTrace_696553 : CollatzResearch.WordTrace tailWord_696553 prefixEnd_696553 357666490331318466884117 := by
  unfold tailWord_696553
  simp only [CollatzResearch.WordTrace]
  refine ⟨25405375045514917626478313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16936916697009945084318875 25405375045514917626478313)
  ·
    refine ⟨19054031284136188219858735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25405375045514917626478313 19054031284136188219858735)
    ·
      refine ⟨28581046926204282329788103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19054031284136188219858735 28581046926204282329788103)
      ·
        refine ⟨42871570389306423494682155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28581046926204282329788103 42871570389306423494682155)
        ·
          refine ⟨64307355583959635242023233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871570389306423494682155 64307355583959635242023233)
          ·
            refine ⟨48230516687969726431517425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64307355583959635242023233 48230516687969726431517425)
            ·
              refine ⟨36172887515977294823638069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48230516687969726431517425 36172887515977294823638069)
              ·
                refine ⟨3391208204622871389716069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36172887515977294823638069 3391208204622871389716069)
                ·
                  refine ⟨635851538366788385571763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3391208204622871389716069 635851538366788385571763)
                  ·
                    refine ⟨953777307550182578357645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635851538366788385571763 953777307550182578357645)
                    ·
                      refine ⟨357666490331318466884117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953777307550182578357645 357666490331318466884117)
                      ·
                        rfl

theorem cell23_696553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_696553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696553 prefixEnd_696553 := by exact prefixLift 696553
  have htrace : WordTrace (prefixWord ++ tailWord_696553) baseStart_696553 baseEnd_696553 := by
    simpa [prefixWord, tailWord_696553, baseEnd_696553] using wordTrace_append hprefix tailTrace_696553
  have hstable : (prefixWord ++ tailWord_696553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696553).length < 2 ^ (prefixWord ++ tailWord_696553).sum := by decide
  have hdescent : baseEnd_696553 < baseStart_696553 := by decide
  rcases family_descends (prefixWord ++ tailWord_696553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696570 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_696570 : Nat := 118140960795 + 696570 * 2 ^ 59
def prefixEnd_696570 : Nat := 4983230072969 + 3 ^ 40 * 696570 * 2
def baseEnd_696570 : Nat := 357675219502444900371539

theorem tailTrace_696570 : CollatzResearch.WordTrace tailWord_696570 prefixEnd_696570 357675219502444900371539 := by
  unfold tailWord_696570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351498771613332382461791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16937330057635553019898109 6351498771613332382461791)
  ·
    refine ⟨9527248157419998573692687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351498771613332382461791 9527248157419998573692687)
    ·
      refine ⟨14290872236129997860539031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527248157419998573692687 14290872236129997860539031)
      ·
        refine ⟨21436308354194996790808547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290872236129997860539031 21436308354194996790808547)
        ·
          refine ⟨32154462531292495186212821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436308354194996790808547 32154462531292495186212821)
          ·
            refine ⟨753620215577167855926863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32154462531292495186212821 753620215577167855926863)
            ·
              refine ⟨1130430323365751783890295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753620215577167855926863 1130430323365751783890295)
              ·
                refine ⟨1695645485048627675835443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130430323365751783890295 1695645485048627675835443)
                ·
                  refine ⟨2543468227572941513753165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695645485048627675835443 2543468227572941513753165)
                  ·
                    refine ⟨953800585339853067657437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2543468227572941513753165 953800585339853067657437)
                    ·
                      refine ⟨357675219502444900371539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953800585339853067657437 357675219502444900371539)
                      ·
                        rfl

theorem cell23_696570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_696570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696570 prefixEnd_696570 := by exact prefixLift 696570
  have htrace : WordTrace (prefixWord ++ tailWord_696570) baseStart_696570 baseEnd_696570 := by
    simpa [prefixWord, tailWord_696570, baseEnd_696570] using wordTrace_append hprefix tailTrace_696570
  have hstable : (prefixWord ++ tailWord_696570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696570).length < 2 ^ (prefixWord ++ tailWord_696570).sum := by decide
  have hdescent : baseEnd_696570 < baseStart_696570 := by decide
  rcases family_descends (prefixWord ++ tailWord_696570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696576 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_696576 : Nat := 118140960795 + 696576 * 2 ^ 59
def prefixEnd_696576 : Nat := 4983230072969 + 3 ^ 40 * 696576 * 2
def baseEnd_696576 : Nat := 357678300386371876896511

theorem tailTrace_696576 : CollatzResearch.WordTrace tailWord_696576 prefixEnd_696576 357678300386371876896511 := by
  unfold tailWord_696576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12703106962215796277282791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16937475949621061703043721 12703106962215796277282791)
  ·
    refine ⟨19054660443323694415924187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12703106962215796277282791 19054660443323694415924187)
    ·
      refine ⟨28581990664985541623886281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19054660443323694415924187 28581990664985541623886281)
      ·
        refine ⟨21436492998739156217914711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28581990664985541623886281 21436492998739156217914711)
        ·
          refine ⟨32154739498108734326872067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436492998739156217914711 32154739498108734326872067)
          ·
            refine ⟨48232109247163101490308101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32154739498108734326872067 48232109247163101490308101)
            ·
              refine ⟨9043520483843081529432769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48232109247163101490308101 9043520483843081529432769)
              ·
                refine ⟨6782640362882311147074577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9043520483843081529432769 6782640362882311147074577)
                ·
                  refine ⟨5086980272161733360305933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6782640362882311147074577 5086980272161733360305933)
                  ·
                    refine ⟨1907617602060650010114725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5086980272161733360305933 1907617602060650010114725)
                    ·
                      refine ⟨357678300386371876896511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1907617602060650010114725 357678300386371876896511)
                      ·
                        rfl

theorem cell23_696576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_696576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696576 prefixEnd_696576 := by exact prefixLift 696576
  have htrace : WordTrace (prefixWord ++ tailWord_696576) baseStart_696576 baseEnd_696576 := by
    simpa [prefixWord, tailWord_696576, baseEnd_696576] using wordTrace_append hprefix tailTrace_696576
  have hstable : (prefixWord ++ tailWord_696576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696576).length < 2 ^ (prefixWord ++ tailWord_696576).sum := by decide
  have hdescent : baseEnd_696576 < baseStart_696576 := by decide
  rcases family_descends (prefixWord ++ tailWord_696576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696586 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_696586 : Nat := 118140960795 + 696586 * 2 ^ 59
def prefixEnd_696586 : Nat := 4983230072969 + 3 ^ 40 * 696586 * 2
def baseEnd_696586 : Nat := 119227811730972279257155

theorem tailTrace_696586 : CollatzResearch.WordTrace tailWord_696586 prefixEnd_696586 119227811730972279257155 := by
  unfold tailWord_696586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351644663598841065607403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16937719102930242841619741 6351644663598841065607403)
  ·
    refine ⟨9527466995398261598411105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351644663598841065607403 9527466995398261598411105)
    ·
      refine ⟨7145600246548696198808329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9527466995398261598411105 7145600246548696198808329)
      ·
        refine ⟨5359200184911522149106247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7145600246548696198808329 5359200184911522149106247)
        ·
          refine ⟨8038800277367283223659371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359200184911522149106247 8038800277367283223659371)
          ·
            refine ⟨12058200416050924835489057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038800277367283223659371 12058200416050924835489057)
            ·
              refine ⟨9043650312038193626616793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058200416050924835489057 9043650312038193626616793)
              ·
                refine ⟨6782737734028645219962595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9043650312038193626616793 6782737734028645219962595)
                ·
                  refine ⟨10174106601042967829943893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6782737734028645219962595 10174106601042967829943893)
                  ·
                    refine ⟨119227811730972279257155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10174106601042967829943893 119227811730972279257155)
                    ·
                      rfl

theorem cell23_696586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_696586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696586 prefixEnd_696586 := by exact prefixLift 696586
  have htrace : WordTrace (prefixWord ++ tailWord_696586) baseStart_696586 baseEnd_696586 := by
    simpa [prefixWord, tailWord_696586, baseEnd_696586] using wordTrace_append hprefix tailTrace_696586
  have hstable : (prefixWord ++ tailWord_696586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696586).length < 2 ^ (prefixWord ++ tailWord_696586).sum := by decide
  have hdescent : baseEnd_696586 < baseStart_696586 := by decide
  rcases family_descends (prefixWord ++ tailWord_696586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696627 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 2, 2, 2]
def baseStart_696627 : Nat := 118140960795 + 696627 * 2 ^ 59
def prefixEnd_696627 : Nat := 4983230072969 + 3 ^ 40 * 696627 * 2
def baseEnd_696627 : Nat := 357704487899751177358777

theorem tailTrace_696627 : CollatzResearch.WordTrace tailWord_696627 prefixEnd_696627 357704487899751177358777 := by
  unfold tailWord_696627
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408074047246828264672135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16938716031497885509781423 25408074047246828264672135)
  ·
    refine ⟨38112111070870242397008203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25408074047246828264672135 38112111070870242397008203)
    ·
      refine ⟨57168166606305363595512305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38112111070870242397008203 57168166606305363595512305)
      ·
        refine ⟨42876124954729022696634229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57168166606305363595512305 42876124954729022696634229)
        ·
          refine ⟨4019636714505845877809459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42876124954729022696634229 4019636714505845877809459)
          ·
            refine ⟨6029455071758768816714189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019636714505845877809459 6029455071758768816714189)
            ·
              refine ⟨2261045651909538306267821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6029455071758768816714189 2261045651909538306267821)
              ·
                refine ⟨847892119466076864850433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261045651909538306267821 847892119466076864850433)
                ·
                  refine ⟨635919089599557648637825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 847892119466076864850433 635919089599557648637825)
                  ·
                    refine ⟨476939317199668236478369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 635919089599557648637825 476939317199668236478369)
                    ·
                      refine ⟨357704487899751177358777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476939317199668236478369 357704487899751177358777)
                      ·
                        rfl

theorem cell23_696627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2, 2].length) (baseStart_696627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696627 prefixEnd_696627 := by exact prefixLift 696627
  have htrace : WordTrace (prefixWord ++ tailWord_696627) baseStart_696627 baseEnd_696627 := by
    simpa [prefixWord, tailWord_696627, baseEnd_696627] using wordTrace_append hprefix tailTrace_696627
  have hstable : (prefixWord ++ tailWord_696627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696627).length < 2 ^ (prefixWord ++ tailWord_696627).sum := by decide
  have hdescent : baseEnd_696627 < baseStart_696627 := by decide
  rcases family_descends (prefixWord ++ tailWord_696627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696644 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_696644 : Nat := 118140960795 + 696644 * 2 ^ 59
def prefixEnd_696644 : Nat := 4983230072969 + 3 ^ 40 * 696644 * 2
def baseEnd_696644 : Nat := 357713217070877610846199

theorem tailTrace_696644 : CollatzResearch.WordTrace tailWord_696644 prefixEnd_696644 357713217070877610846199 := by
  unfold tailWord_696644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704347044092620084020493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16939129392123493445360657 12704347044092620084020493)
  ·
    refine ⟨4764130141534732531507685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12704347044092620084020493 4764130141534732531507685)
    ·
      refine ⟨893274401537762349657691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4764130141534732531507685 893274401537762349657691)
      ·
        refine ⟨1339911602306643524486537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893274401537762349657691 1339911602306643524486537)
        ·
          refine ⟨1004933701729982643364903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339911602306643524486537 1004933701729982643364903)
          ·
            refine ⟨1507400552594973965047355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004933701729982643364903 1507400552594973965047355)
            ·
              refine ⟨2261100828892460947571033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507400552594973965047355 2261100828892460947571033)
              ·
                refine ⟨1695825621669345710678275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261100828892460947571033 1695825621669345710678275)
                ·
                  refine ⟨2543738432504018566017413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695825621669345710678275 2543738432504018566017413)
                  ·
                    refine ⟨476950956094503481128265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543738432504018566017413 476950956094503481128265)
                    ·
                      refine ⟨357713217070877610846199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 476950956094503481128265 357713217070877610846199)
                      ·
                        rfl

theorem cell23_696644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_696644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696644 prefixEnd_696644 := by exact prefixLift 696644
  have htrace : WordTrace (prefixWord ++ tailWord_696644) baseStart_696644 baseEnd_696644 := by
    simpa [prefixWord, tailWord_696644, baseEnd_696644] using wordTrace_append hprefix tailTrace_696644
  have hstable : (prefixWord ++ tailWord_696644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696644).length < 2 ^ (prefixWord ++ tailWord_696644).sum := by decide
  have hdescent : baseEnd_696644 < baseStart_696644 := by decide
  rcases family_descends (prefixWord ++ tailWord_696644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696663 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 2, 5]
def baseStart_696663 : Nat := 118140960795 + 696663 * 2 ^ 59
def prefixEnd_696663 : Nat := 4983230072969 + 3 ^ 40 * 696663 * 2
def baseEnd_696663 : Nat := 119240991067771012169537

theorem tailTrace_696663 : CollatzResearch.WordTrace tailWord_696663 prefixEnd_696663 119240991067771012169537 := by
  unfold tailWord_696663
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409387075116406412982643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16939591383410937608655095 25409387075116406412982643)
  ·
    refine ⟨38114080612674609619473965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25409387075116406412982643 38114080612674609619473965)
    ·
      refine ⟨14292780229752978607302737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38114080612674609619473965 14292780229752978607302737)
      ·
        refine ⟨10719585172314733955477053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14292780229752978607302737 10719585172314733955477053)
        ·
          refine ⟨4019844439618025233303895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10719585172314733955477053 4019844439618025233303895)
          ·
            refine ⟨6029766659427037849955843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019844439618025233303895 6029766659427037849955843)
            ·
              refine ⟨9044649989140556774933765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029766659427037849955843 9044649989140556774933765)
              ·
                refine ⟨1695871872963854395300081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9044649989140556774933765 1695871872963854395300081)
                ·
                  refine ⟨1271903904722890796475061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695871872963854395300081 1271903904722890796475061)
                  ·
                    refine ⟨119240991067771012169537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1271903904722890796475061 119240991067771012169537)
                    ·
                      rfl

theorem cell23_696663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_696663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696663 prefixEnd_696663 := by exact prefixLift 696663
  have htrace : WordTrace (prefixWord ++ tailWord_696663) baseStart_696663 baseEnd_696663 := by
    simpa [prefixWord, tailWord_696663, baseEnd_696663] using wordTrace_append hprefix tailTrace_696663
  have hstable : (prefixWord ++ tailWord_696663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696663).length < 2 ^ (prefixWord ++ tailWord_696663).sum := by decide
  have hdescent : baseEnd_696663 < baseStart_696663 := by decide
  rcases family_descends (prefixWord ++ tailWord_696663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696703 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_696703 : Nat := 118140960795 + 696703 * 2 ^ 59
def prefixEnd_696703 : Nat := 4983230072969 + 3 ^ 40 * 696703 * 2
def baseEnd_696703 : Nat := 357743512429492880008427

theorem tailTrace_696703 : CollatzResearch.WordTrace tailWord_696703 prefixEnd_696703 357743512429492880008427 := by
  unfold tailWord_696703
  simp only [CollatzResearch.WordTrace]
  refine ⟨25410845994971493244438763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16940563996647662162959175 25410845994971493244438763)
  ·
    refine ⟨38116268992457239866658145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25410845994971493244438763 38116268992457239866658145)
    ·
      refine ⟨28587201744342929899993609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38116268992457239866658145 28587201744342929899993609)
      ·
        refine ⟨21440401308257197424995207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28587201744342929899993609 21440401308257197424995207)
        ·
          refine ⟨32160601962385796137492811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21440401308257197424995207 32160601962385796137492811)
          ·
            refine ⟨48240902943578694206239217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32160601962385796137492811 48240902943578694206239217)
            ·
              refine ⟨36180677207684020654679413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48240902943578694206239217 36180677207684020654679413)
              ·
                refine ⟨3391938488220376936376195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36180677207684020654679413 3391938488220376936376195)
                ·
                  refine ⟨5087907732330565404564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391938488220376936376195 5087907732330565404564293)
                  ·
                    refine ⟨953982699811981013355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087907732330565404564293 953982699811981013355805)
                    ·
                      refine ⟨357743512429492880008427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 953982699811981013355805 357743512429492880008427)
                      ·
                        rfl

theorem cell23_696703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_696703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696703 prefixEnd_696703 := by exact prefixLift 696703
  have htrace : WordTrace (prefixWord ++ tailWord_696703) baseStart_696703 baseEnd_696703 := by
    simpa [prefixWord, tailWord_696703, baseEnd_696703] using wordTrace_append hprefix tailTrace_696703
  have hstable : (prefixWord ++ tailWord_696703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696703).length < 2 ^ (prefixWord ++ tailWord_696703).sum := by decide
  have hdescent : baseEnd_696703 < baseStart_696703 := by decide
  rcases family_descends (prefixWord ++ tailWord_696703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696713 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_696713 : Nat := 118140960795 + 696713 * 2 ^ 59
def prefixEnd_696713 : Nat := 4983230072969 + 3 ^ 40 * 696713 * 2
def baseEnd_696713 : Nat := 357748647236037840883381

theorem tailTrace_696713 : CollatzResearch.WordTrace tailWord_696713 prefixEnd_696713 357748647236037840883381 := by
  unfold tailWord_696713
  simp only [CollatzResearch.WordTrace]
  refine ⟨25411210724935264952302793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16940807149956843301535195 25411210724935264952302793)
  ·
    refine ⟨19058408043701448714227095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25411210724935264952302793 19058408043701448714227095)
    ·
      refine ⟨28587612065552173071340643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058408043701448714227095 28587612065552173071340643)
      ·
        refine ⟨42881418098328259607010965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28587612065552173071340643 42881418098328259607010965)
        ·
          refine ⟨2010066473359137169078639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42881418098328259607010965 2010066473359137169078639)
          ·
            refine ⟨3015099710038705753617959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010066473359137169078639 3015099710038705753617959)
            ·
              refine ⟨4522649565058058630426939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015099710038705753617959 4522649565058058630426939)
              ·
                refine ⟨6783974347587087945640409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522649565058058630426939 6783974347587087945640409)
                ·
                  refine ⟨5087980760690315959230307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783974347587087945640409 5087980760690315959230307)
                  ·
                    refine ⟨7631971141035473938845461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087980760690315959230307 7631971141035473938845461)
                    ·
                      refine ⟨357748647236037840883381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7631971141035473938845461 357748647236037840883381)
                      ·
                        rfl

theorem cell23_696713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_696713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696713 prefixEnd_696713 := by exact prefixLift 696713
  have htrace : WordTrace (prefixWord ++ tailWord_696713) baseStart_696713 baseEnd_696713 := by
    simpa [prefixWord, tailWord_696713, baseEnd_696713] using wordTrace_append hprefix tailTrace_696713
  have hstable : (prefixWord ++ tailWord_696713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696713).length < 2 ^ (prefixWord ++ tailWord_696713).sum := by decide
  have hdescent : baseEnd_696713 < baseStart_696713 := by decide
  rcases family_descends (prefixWord ++ tailWord_696713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696727 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 1, 4]
def baseStart_696727 : Nat := 118140960795 + 696727 * 2 ^ 59
def prefixEnd_696727 : Nat := 4983230072969 + 3 ^ 40 * 696727 * 2
def baseEnd_696727 : Nat := 119251945321733595369439

theorem tailTrace_696727 : CollatzResearch.WordTrace tailWord_696727 prefixEnd_696727 119251945321733595369439 := by
  unfold tailWord_696727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25411721346884545343312435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16941147564589696895541623 25411721346884545343312435)
  ·
    refine ⟨38117582020326818014968653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25411721346884545343312435 38117582020326818014968653)
    ·
      refine ⟨14294093257622556755613245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38117582020326818014968653 14294093257622556755613245)
      ·
        refine ⟨5360284971608458783354967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14294093257622556755613245 5360284971608458783354967)
        ·
          refine ⟨8040427457412688175032451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360284971608458783354967 8040427457412688175032451)
          ·
            refine ⟨12060641186119032262548677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040427457412688175032451 12060641186119032262548677)
            ·
              refine ⟨2261370222397318549227877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12060641186119032262548677 2261370222397318549227877)
              ·
                refine ⟨424006916699497227980227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2261370222397318549227877 424006916699497227980227)
                ·
                  refine ⟨636010375049245841970341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424006916699497227980227 636010375049245841970341)
                  ·
                    refine ⟨119251945321733595369439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 636010375049245841970341 119251945321733595369439)
                    ·
                      rfl

theorem cell23_696727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_696727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696727 prefixEnd_696727 := by exact prefixLift 696727
  have htrace : WordTrace (prefixWord ++ tailWord_696727) baseStart_696727 baseEnd_696727 := by
    simpa [prefixWord, tailWord_696727, baseEnd_696727] using wordTrace_append hprefix tailTrace_696727
  have hstable : (prefixWord ++ tailWord_696727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696727).length < 2 ^ (prefixWord ++ tailWord_696727).sum := by decide
  have hdescent : baseEnd_696727 < baseStart_696727 := by decide
  rcases family_descends (prefixWord ++ tailWord_696727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696734 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_696734 : Nat := 118140960795 + 696734 * 2 ^ 59
def prefixEnd_696734 : Nat := 4983230072969 + 3 ^ 40 * 696734 * 2
def baseEnd_696734 : Nat := 357759430329782258720785

theorem tailTrace_696734 : CollatzResearch.WordTrace tailWord_696734 prefixEnd_696734 357759430329782258720785 := by
  unfold tailWord_696734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176497082232398192352157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16941317771906123692544837 3176497082232398192352157)
  ·
    refine ⟨1191186405837149322132059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3176497082232398192352157 1191186405837149322132059)
    ·
      refine ⟨1786779608755723983198089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191186405837149322132059 1786779608755723983198089)
      ·
        refine ⟨1340084706566792987398567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1786779608755723983198089 1340084706566792987398567)
        ·
          refine ⟨2010127059850189481097851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340084706566792987398567 2010127059850189481097851)
          ·
            refine ⟨3015190589775284221646777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010127059850189481097851 3015190589775284221646777)
            ·
              refine ⟨2261392942331463166235083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015190589775284221646777 2261392942331463166235083)
              ·
                refine ⟨3392089413497194749352625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261392942331463166235083 3392089413497194749352625)
                ·
                  refine ⟨2544067060122896062014469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392089413497194749352625 2544067060122896062014469)
                  ·
                    refine ⟨477012573773043011627713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544067060122896062014469 477012573773043011627713)
                    ·
                      refine ⟨357759430329782258720785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477012573773043011627713 357759430329782258720785)
                      ·
                        rfl

theorem cell23_696734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_696734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696734 prefixEnd_696734 := by exact prefixLift 696734
  have htrace : WordTrace (prefixWord ++ tailWord_696734) baseStart_696734 baseEnd_696734 := by
    simpa [prefixWord, tailWord_696734, baseEnd_696734] using wordTrace_append hprefix tailTrace_696734
  have hstable : (prefixWord ++ tailWord_696734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696734).length < 2 ^ (prefixWord ++ tailWord_696734).sum := by decide
  have hdescent : baseEnd_696734 < baseStart_696734 := by decide
  rcases family_descends (prefixWord ++ tailWord_696734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696821 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_696821 : Nat := 118140960795 + 696821 * 2 ^ 59
def prefixEnd_696821 : Nat := 4983230072969 + 3 ^ 40 * 696821 * 2
def baseEnd_696821 : Nat := 119268034382241139444295

theorem tailTrace_696821 : CollatzResearch.WordTrace tailWord_696821 prefixEnd_696821 119268034382241139444295 := by
  unfold tailWord_696821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25415149808543999397234317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16943433205695999598156211 25415149808543999397234317)
  ·
    refine ⟨9530681178203999773962869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25415149808543999397234317 9530681178203999773962869)
    ·
      refine ⟨893501360456624978809019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9530681178203999773962869 893501360456624978809019)
      ·
        refine ⟨1340252040684937468213529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893501360456624978809019 1340252040684937468213529)
        ·
          refine ⟨1005189030513703101160147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340252040684937468213529 1005189030513703101160147)
          ·
            refine ⟨1507783545770554651740221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005189030513703101160147 1507783545770554651740221)
            ·
              refine ⟨565418829663957994402583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507783545770554651740221 565418829663957994402583)
              ·
                refine ⟨848128244495936991603875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565418829663957994402583 848128244495936991603875)
                ·
                  refine ⟨1272192366743905487405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848128244495936991603875 1272192366743905487405813)
                  ·
                    refine ⟨119268034382241139444295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1272192366743905487405813 119268034382241139444295)
                    ·
                      rfl

theorem cell23_696821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_696821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696821 prefixEnd_696821 := by exact prefixLift 696821
  have htrace : WordTrace (prefixWord ++ tailWord_696821) baseStart_696821 baseEnd_696821 := by
    simpa [prefixWord, tailWord_696821, baseEnd_696821] using wordTrace_append hprefix tailTrace_696821
  have hstable : (prefixWord ++ tailWord_696821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696821).length < 2 ^ (prefixWord ++ tailWord_696821).sum := by decide
  have hdescent : baseEnd_696821 < baseStart_696821 := by decide
  rcases family_descends (prefixWord ++ tailWord_696821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696840 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_696840 : Nat := 118140960795 + 696840 * 2 ^ 59
def prefixEnd_696840 : Nat := 4983230072969 + 3 ^ 40 * 696840 * 2
def baseEnd_696840 : Nat := 357813859279158843995297

theorem tailTrace_696840 : CollatzResearch.WordTrace tailWord_696840 prefixEnd_696840 357813859279158843995297 := by
  unfold tailWord_696840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707921397737582821087987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16943895196983443761450649 12707921397737582821087987)
  ·
    refine ⟨19061882096606374231631981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707921397737582821087987 19061882096606374231631981)
    ·
      refine ⟨7148205786227390336861993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19061882096606374231631981 7148205786227390336861993)
      ·
        refine ⟨5361154339670542752646495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148205786227390336861993 5361154339670542752646495)
        ·
          refine ⟨8041731509505814128969743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361154339670542752646495 8041731509505814128969743)
          ·
            refine ⟨12062597264258721193454615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041731509505814128969743 12062597264258721193454615)
            ·
              refine ⟨18093895896388081790181923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12062597264258721193454615 18093895896388081790181923)
              ·
                refine ⟨27140843844582122685272885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18093895896388081790181923 27140843844582122685272885)
                ·
                  refine ⟨2544454110429574001744333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27140843844582122685272885 2544454110429574001744333)
                  ·
                    refine ⟨954170291411090250654125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544454110429574001744333 954170291411090250654125)
                    ·
                      refine ⟨357813859279158843995297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 954170291411090250654125 357813859279158843995297)
                      ·
                        rfl

theorem cell23_696840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_696840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696840 prefixEnd_696840 := by exact prefixLift 696840
  have htrace : WordTrace (prefixWord ++ tailWord_696840) baseStart_696840 baseEnd_696840 := by
    simpa [prefixWord, tailWord_696840, baseEnd_696840] using wordTrace_append hprefix tailTrace_696840
  have hstable : (prefixWord ++ tailWord_696840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696840).length < 2 ^ (prefixWord ++ tailWord_696840).sum := by decide
  have hdescent : baseEnd_696840 < baseStart_696840 := by decide
  rcases family_descends (prefixWord ++ tailWord_696840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696878 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_696878 : Nat := 118140960795 + 696878 * 2 ^ 59
def prefixEnd_696878 : Nat := 4983230072969 + 3 ^ 40 * 696878 * 2
def baseEnd_696878 : Nat := 357833371544029695320123

theorem tailTrace_696878 : CollatzResearch.WordTrace tailWord_696878 prefixEnd_696878 357833371544029695320123 := by
  unfold tailWord_696878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177153596167187266507411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16944819179558332088039525 3177153596167187266507411)
  ·
    refine ⟨4765730394250780899761117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177153596167187266507411 4765730394250780899761117)
    ·
      refine ⟨1787148897844042837410419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4765730394250780899761117 1787148897844042837410419)
      ·
        refine ⟨2680723346766064256115629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787148897844042837410419 2680723346766064256115629)
        ·
          refine ⟨1005271255037274096043361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2680723346766064256115629 1005271255037274096043361)
          ·
            refine ⟨753953441277955572032521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005271255037274096043361 753953441277955572032521)
            ·
              refine ⟨565465080958466679024391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753953441277955572032521 565465080958466679024391)
              ·
                refine ⟨848197621437700018536587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565465080958466679024391 848197621437700018536587)
                ·
                  refine ⟨1272296432156550027804881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848197621437700018536587 1272296432156550027804881)
                  ·
                    refine ⟨954222324117412520853661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272296432156550027804881 954222324117412520853661)
                    ·
                      refine ⟨357833371544029695320123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 954222324117412520853661 357833371544029695320123)
                      ·
                        rfl

theorem cell23_696878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_696878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696878 prefixEnd_696878 := by exact prefixLift 696878
  have htrace : WordTrace (prefixWord ++ tailWord_696878) baseStart_696878 baseEnd_696878 := by
    simpa [prefixWord, tailWord_696878, baseEnd_696878] using wordTrace_append hprefix tailTrace_696878
  have hstable : (prefixWord ++ tailWord_696878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696878).length < 2 ^ (prefixWord ++ tailWord_696878).sum := by decide
  have hdescent : baseEnd_696878 < baseStart_696878 := by decide
  rcases family_descends (prefixWord ++ tailWord_696878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696890 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_696890 : Nat := 118140960795 + 696890 * 2 ^ 59
def prefixEnd_696890 : Nat := 4983230072969 + 3 ^ 40 * 696890 * 2
def baseEnd_696890 : Nat := 119279844437294549456689

theorem tailTrace_696890 : CollatzResearch.WordTrace tailWord_696890 prefixEnd_696890 119279844437294549456689 := by
  unfold tailWord_696890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354416611323506045374031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16945110963529349454330749 6354416611323506045374031)
  ·
    refine ⟨9531624916985259068061047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354416611323506045374031 9531624916985259068061047)
    ·
      refine ⟨14297437375477888602091571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531624916985259068061047 14297437375477888602091571)
      ·
        refine ⟨21446156063216832903137357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14297437375477888602091571 21446156063216832903137357)
        ·
          refine ⟨8042308523706312338676509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21446156063216832903137357 8042308523706312338676509)
          ·
            refine ⟨3015865696389867127003691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8042308523706312338676509 3015865696389867127003691)
            ·
              refine ⟨4523798544584800690505537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015865696389867127003691 4523798544584800690505537)
              ·
                refine ⟨3392848908438600517879153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523798544584800690505537 3392848908438600517879153)
                ·
                  refine ⟨2544636681328950388409365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392848908438600517879153 2544636681328950388409365)
                  ·
                    refine ⟨119279844437294549456689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2544636681328950388409365 119279844437294549456689)
                    ·
                      rfl

theorem cell23_696890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_696890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696890 prefixEnd_696890 := by exact prefixLift 696890
  have htrace : WordTrace (prefixWord ++ tailWord_696890) baseStart_696890 baseEnd_696890 := by
    simpa [prefixWord, tailWord_696890, baseEnd_696890] using wordTrace_append hprefix tailTrace_696890
  have hstable : (prefixWord ++ tailWord_696890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696890).length < 2 ^ (prefixWord ++ tailWord_696890).sum := by decide
  have hdescent : baseEnd_696890 < baseStart_696890 := by decide
  rcases family_descends (prefixWord ++ tailWord_696890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696920 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 7]
def baseStart_696920 : Nat := 118140960795 + 696920 * 2 ^ 59
def prefixEnd_696920 : Nat := 4983230072969 + 3 ^ 40 * 696920 * 2
def baseEnd_696920 : Nat := 39761659747946503443881

theorem tailTrace_696920 : CollatzResearch.WordTrace tailWord_696920 prefixEnd_696920 39761659747946503443881 := by
  unfold tailWord_696920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709380317592669652544107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16945840423456892870058809 12709380317592669652544107)
  ·
    refine ⟨19064070476389004478816161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12709380317592669652544107 19064070476389004478816161)
    ·
      refine ⟨14298052857291753359112121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19064070476389004478816161 14298052857291753359112121)
      ·
        refine ⟨10723539642968815019334091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14298052857291753359112121 10723539642968815019334091)
        ·
          refine ⟨16085309464453222529001137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10723539642968815019334091 16085309464453222529001137)
          ·
            refine ⟨12063982098339916896750853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16085309464453222529001137 12063982098339916896750853)
            ·
              refine ⟨2261996643438734418140785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12063982098339916896750853 2261996643438734418140785)
              ·
                refine ⟨1696497482579050813605589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261996643438734418140785 1696497482579050813605589)
                ·
                  refine ⟨39761659747946503443881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1696497482579050813605589 39761659747946503443881)
                  ·
                    rfl

theorem cell23_696920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_696920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696920 prefixEnd_696920 := by exact prefixLift 696920
  have htrace : WordTrace (prefixWord ++ tailWord_696920) baseStart_696920 baseEnd_696920 := by
    simpa [prefixWord, tailWord_696920, baseEnd_696920] using wordTrace_append hprefix tailTrace_696920
  have hstable : (prefixWord ++ tailWord_696920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696920).length < 2 ^ (prefixWord ++ tailWord_696920).sum := by decide
  have hdescent : baseEnd_696920 < baseStart_696920 := by decide
  rcases family_descends (prefixWord ++ tailWord_696920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696926 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_696926 : Nat := 118140960795 + 696926 * 2 ^ 59
def prefixEnd_696926 : Nat := 4983230072969 + 3 ^ 40 * 696926 * 2
def baseEnd_696926 : Nat := 357858018615445507519903

theorem tailTrace_696926 : CollatzResearch.WordTrace tailWord_696926 prefixEnd_696926 357858018615445507519903 := by
  unfold tailWord_696926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177372434145450291225829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16945986315442401553204421 3177372434145450291225829)
  ·
    refine ⟨595757331402271929604843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3177372434145450291225829 595757331402271929604843)
    ·
      refine ⟨893635997103407894407265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595757331402271929604843 893635997103407894407265)
      ·
        refine ⟨670226997827555920805449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893635997103407894407265 670226997827555920805449)
        ·
          refine ⟨502670248370666940604087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670226997827555920805449 502670248370666940604087)
          ·
            refine ⟨754005372556000410906131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502670248370666940604087 754005372556000410906131)
            ·
              refine ⟨1131008058834000616359197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754005372556000410906131 1131008058834000616359197)
              ·
                refine ⟨424128022062750231134699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131008058834000616359197 424128022062750231134699)
                ·
                  refine ⟨636192033094125346702049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424128022062750231134699 636192033094125346702049)
                  ·
                    refine ⟨477144024820594010026537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636192033094125346702049 477144024820594010026537)
                    ·
                      refine ⟨357858018615445507519903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477144024820594010026537 357858018615445507519903)
                      ·
                        rfl

theorem cell23_696926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_696926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696926 prefixEnd_696926 := by exact prefixLift 696926
  have htrace : WordTrace (prefixWord ++ tailWord_696926) baseStart_696926 baseEnd_696926 := by
    simpa [prefixWord, tailWord_696926, baseEnd_696926] using wordTrace_append hprefix tailTrace_696926
  have hstable : (prefixWord ++ tailWord_696926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696926).length < 2 ^ (prefixWord ++ tailWord_696926).sum := by decide
  have hdescent : baseEnd_696926 < baseStart_696926 := by decide
  rcases family_descends (prefixWord ++ tailWord_696926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696960 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_696960 : Nat := 118140960795 + 696960 * 2 ^ 59
def prefixEnd_696960 : Nat := 4983230072969 + 3 ^ 40 * 696960 * 2
def baseEnd_696960 : Nat := 357875476957698374494745

theorem tailTrace_696960 : CollatzResearch.WordTrace tailWord_696960 prefixEnd_696960 357875476957698374494745 := by
  unfold tailWord_696960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710109777520213068272167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16946813036693617424362889 12710109777520213068272167)
  ·
    refine ⟨19065164666280319602408251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12710109777520213068272167 19065164666280319602408251)
    ·
      refine ⟨28597746999420479403612377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065164666280319602408251 28597746999420479403612377)
      ·
        refine ⟨21448310249565359552709283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28597746999420479403612377 21448310249565359552709283)
        ·
          refine ⟨32172465374348039329063925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21448310249565359552709283 32172465374348039329063925)
          ·
            refine ⟨3016168628845128687099743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32172465374348039329063925 3016168628845128687099743)
            ·
              refine ⟨4524252943267693030649615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016168628845128687099743 4524252943267693030649615)
              ·
                refine ⟨6786379414901539545974423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524252943267693030649615 6786379414901539545974423)
                ·
                  refine ⟨10179569122352309318961635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786379414901539545974423 10179569122352309318961635)
                  ·
                    refine ⟨15269353683528463978442453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10179569122352309318961635 15269353683528463978442453)
                    ·
                      refine ⟨357875476957698374494745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15269353683528463978442453 357875476957698374494745)
                      ·
                        rfl

theorem cell23_696960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_696960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_696960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_696960 prefixEnd_696960 := by exact prefixLift 696960
  have htrace : WordTrace (prefixWord ++ tailWord_696960) baseStart_696960 baseEnd_696960 := by
    simpa [prefixWord, tailWord_696960, baseEnd_696960] using wordTrace_append hprefix tailTrace_696960
  have hstable : (prefixWord ++ tailWord_696960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696960).length < 2 ^ (prefixWord ++ tailWord_696960).sum := by decide
  have hdescent : baseEnd_696960 < baseStart_696960 := by decide
  rcases family_descends (prefixWord ++ tailWord_696960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697071 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_697071 : Nat := 118140960795 + 697071 * 2 ^ 59
def prefixEnd_697071 : Nat := 4983230072969 + 3 ^ 40 * 697071 * 2
def baseEnd_697071 : Nat := 357932473310347440206735

theorem tailTrace_697071 : CollatzResearch.WordTrace tailWord_697071 prefixEnd_697071 357932473310347440206735 := by
  unfold tailWord_697071
  simp only [CollatzResearch.WordTrace]
  refine ⟨25424268057638292093835067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16949512038425528062556711 25424268057638292093835067)
  ·
    refine ⟨38136402086457438140752601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25424268057638292093835067 38136402086457438140752601)
    ·
      refine ⟨28602301564843078605564451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38136402086457438140752601 28602301564843078605564451)
      ·
        refine ⟨42903452347264617908346677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28602301564843078605564451 42903452347264617908346677)
        ·
          refine ⟨4022198657556057928907501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42903452347264617908346677 4022198657556057928907501)
          ·
            refine ⟨1508324496583521723340313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4022198657556057928907501 1508324496583521723340313)
            ·
              refine ⟨1131243372437641292505235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508324496583521723340313 1131243372437641292505235)
              ·
                refine ⟨1696865058656461938757853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131243372437641292505235 1696865058656461938757853)
                ·
                  refine ⟨636324396996173227034195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1696865058656461938757853 636324396996173227034195)
                  ·
                    refine ⟨954486595494259840551293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 636324396996173227034195 954486595494259840551293)
                    ·
                      refine ⟨357932473310347440206735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 954486595494259840551293 357932473310347440206735)
                      ·
                        rfl

theorem cell23_697071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_697071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697071 prefixEnd_697071 := by exact prefixLift 697071
  have htrace : WordTrace (prefixWord ++ tailWord_697071) baseStart_697071 baseEnd_697071 := by
    simpa [prefixWord, tailWord_697071, baseEnd_697071] using wordTrace_append hprefix tailTrace_697071
  have hstable : (prefixWord ++ tailWord_697071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697071).length < 2 ^ (prefixWord ++ tailWord_697071).sum := by decide
  have hdescent : baseEnd_697071 < baseStart_697071 := by decide
  rcases family_descends (prefixWord ++ tailWord_697071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697107 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_697107 : Nat := 118140960795 + 697107 * 2 ^ 59
def prefixEnd_697107 : Nat := 4983230072969 + 3 ^ 40 * 697107 * 2
def baseEnd_697107 : Nat := 357950958613909299356569

theorem tailTrace_697107 : CollatzResearch.WordTrace tailWord_697107 prefixEnd_697107 357950958613909299356569 := by
  unfold tailWord_697107
  simp only [CollatzResearch.WordTrace]
  refine ⟨25425581085507870242145575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16950387390338580161430383 25425581085507870242145575)
  ·
    refine ⟨38138371628261805363218363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25425581085507870242145575 38138371628261805363218363)
    ·
      refine ⟨57207557442392708044827545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38138371628261805363218363 57207557442392708044827545)
      ·
        refine ⟨42905668081794531033620659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57207557442392708044827545 42905668081794531033620659)
        ·
          refine ⟨64358502122691796550430989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42905668081794531033620659 64358502122691796550430989)
          ·
            refine ⟨24134438296009423706411621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64358502122691796550430989 24134438296009423706411621)
            ·
              refine ⟨4525207180501766944952179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24134438296009423706411621 4525207180501766944952179)
              ·
                refine ⟨6787810770752650417428269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525207180501766944952179 6787810770752650417428269)
                ·
                  refine ⟨2545429039032243906535601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787810770752650417428269 2545429039032243906535601)
                  ·
                    refine ⟨1909071779274182929901701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545429039032243906535601 1909071779274182929901701)
                    ·
                      refine ⟨357950958613909299356569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909071779274182929901701 357950958613909299356569)
                      ·
                        rfl

theorem cell23_697107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_697107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697107 prefixEnd_697107 := by exact prefixLift 697107
  have htrace : WordTrace (prefixWord ++ tailWord_697107) baseStart_697107 baseEnd_697107 := by
    simpa [prefixWord, tailWord_697107, baseEnd_697107] using wordTrace_append hprefix tailTrace_697107
  have hstable : (prefixWord ++ tailWord_697107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697107).length < 2 ^ (prefixWord ++ tailWord_697107).sum := by decide
  have hdescent : baseEnd_697107 < baseStart_697107 := by decide
  rcases family_descends (prefixWord ++ tailWord_697107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697114 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_697114 : Nat := 118140960795 + 697114 * 2 ^ 59
def prefixEnd_697114 : Nat := 4983230072969 + 3 ^ 40 * 697114 * 2
def baseEnd_697114 : Nat := 357954552978490771969037

theorem tailTrace_697114 : CollatzResearch.WordTrace tailWord_697114 prefixEnd_697114 357954552978490771969037 := by
  unfold tailWord_697114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356459099120627609412599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16950557597655006958433597 6356459099120627609412599)
  ·
    refine ⟨9534688648680941414118899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356459099120627609412599 9534688648680941414118899)
    ·
      refine ⟨14302032973021412121178349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534688648680941414118899 14302032973021412121178349)
      ·
        refine ⟨5363262364883029545441881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14302032973021412121178349 5363262364883029545441881)
        ·
          refine ⟨4022446773662272159081411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363262364883029545441881 4022446773662272159081411)
          ·
            refine ⟨6033670160493408238622117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022446773662272159081411 6033670160493408238622117)
            ·
              refine ⟨1131313155092514044741647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6033670160493408238622117 1131313155092514044741647)
              ·
                refine ⟨1696969732638771067112471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131313155092514044741647 1696969732638771067112471)
                ·
                  refine ⟨2545454598958156600668707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696969732638771067112471 2545454598958156600668707)
                  ·
                    refine ⟨3818181898437234901003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2545454598958156600668707 3818181898437234901003061)
                    ·
                      refine ⟨357954552978490771969037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3818181898437234901003061 357954552978490771969037)
                      ·
                        rfl

theorem cell23_697114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_697114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697114 prefixEnd_697114 := by exact prefixLift 697114
  have htrace : WordTrace (prefixWord ++ tailWord_697114) baseStart_697114 baseEnd_697114 := by
    simpa [prefixWord, tailWord_697114, baseEnd_697114] using wordTrace_append hprefix tailTrace_697114
  have hstable : (prefixWord ++ tailWord_697114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697114).length < 2 ^ (prefixWord ++ tailWord_697114).sum := by decide
  have hdescent : baseEnd_697114 < baseStart_697114 := by decide
  rcases family_descends (prefixWord ++ tailWord_697114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697134 : List Nat := [4, 1, 3, 2, 1, 1, 1, 10]
def baseStart_697134 : Nat := 118140960795 + 697134 * 2 ^ 59
def prefixEnd_697134 : Nat := 4983230072969 + 3 ^ 40 * 697134 * 2
def baseEnd_697134 : Nat := 13257956392280766434035

theorem tailTrace_697134 : CollatzResearch.WordTrace tailWord_697134 prefixEnd_697134 13257956392280766434035 := by
  unfold tailWord_697134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178320732051256731672307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16951043904273369235585637 3178320732051256731672307)
  ·
    refine ⟨4767481098076885097508461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3178320732051256731672307 4767481098076885097508461)
    ·
      refine ⟨1787805411778831911565673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4767481098076885097508461 1787805411778831911565673)
      ·
        refine ⟨1340854058834123933674255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787805411778831911565673 1340854058834123933674255)
        ·
          refine ⟨2011281088251185900511383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340854058834123933674255 2011281088251185900511383)
          ·
            refine ⟨3016921632376778850767075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011281088251185900511383 3016921632376778850767075)
            ·
              refine ⟨4525382448565168276150613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016921632376778850767075 4525382448565168276150613)
              ·
                refine ⟨13257956392280766434035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4525382448565168276150613 13257956392280766434035)
                ·
                  rfl

theorem cell23_697134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_697134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697134 prefixEnd_697134 := by exact prefixLift 697134
  have htrace : WordTrace (prefixWord ++ tailWord_697134) baseStart_697134 baseEnd_697134 := by
    simpa [prefixWord, tailWord_697134, baseEnd_697134] using wordTrace_append hprefix tailTrace_697134
  have hstable : (prefixWord ++ tailWord_697134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697134).length < 2 ^ (prefixWord ++ tailWord_697134).sum := by decide
  have hdescent : baseEnd_697134 < baseStart_697134 := by decide
  rcases family_descends (prefixWord ++ tailWord_697134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697137 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_697137 : Nat := 118140960795 + 697137 * 2 ^ 59
def prefixEnd_697137 : Nat := 4983230072969 + 3 ^ 40 * 697137 * 2
def baseEnd_697137 : Nat := 357966363033544181981431

theorem tailTrace_697137 : CollatzResearch.WordTrace tailWord_697137 prefixEnd_697137 357966363033544181981431 := by
  unfold tailWord_697137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25426675275399185365737665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951116850266123577158443 25426675275399185365737665)
  ·
    refine ⟨19070006456549389024303249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25426675275399185365737665 19070006456549389024303249)
    ·
      refine ⟨14302504842412041768227437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19070006456549389024303249 14302504842412041768227437)
      ·
        refine ⟨5363439315904515663085289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14302504842412041768227437 5363439315904515663085289)
        ·
          refine ⟨4022579486928386747313967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363439315904515663085289 4022579486928386747313967)
          ·
            refine ⟨6033869230392580120970951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022579486928386747313967 6033869230392580120970951)
            ·
              refine ⟨9050803845588870181456427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6033869230392580120970951 9050803845588870181456427)
              ·
                refine ⟨13576205768383305272184641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9050803845588870181456427 13576205768383305272184641)
                ·
                  refine ⟨10182154326287478954138481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13576205768383305272184641 10182154326287478954138481)
                  ·
                    refine ⟨7636615744715609215603861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10182154326287478954138481 7636615744715609215603861)
                    ·
                      refine ⟨357966363033544181981431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7636615744715609215603861 357966363033544181981431)
                      ·
                        rfl

theorem cell23_697137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_697137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697137 prefixEnd_697137 := by exact prefixLift 697137
  have htrace : WordTrace (prefixWord ++ tailWord_697137) baseStart_697137 baseEnd_697137 := by
    simpa [prefixWord, tailWord_697137, baseEnd_697137] using wordTrace_append hprefix tailTrace_697137
  have hstable : (prefixWord ++ tailWord_697137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697137).length < 2 ^ (prefixWord ++ tailWord_697137).sum := by decide
  have hdescent : baseEnd_697137 < baseStart_697137 := by decide
  rcases family_descends (prefixWord ++ tailWord_697137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697144 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_697144 : Nat := 118140960795 + 697144 * 2 ^ 59
def prefixEnd_697144 : Nat := 4983230072969 + 3 ^ 40 * 697144 * 2
def baseEnd_697144 : Nat := 357969957398125654593899

theorem tailTrace_697144 : CollatzResearch.WordTrace tailWord_697144 prefixEnd_697144 357969957398125654593899 := by
  unfold tailWord_697144
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713465293186912780621243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16951287057582550374161657 12713465293186912780621243)
  ·
    refine ⟨19070197939780369170931865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12713465293186912780621243 19070197939780369170931865)
    ·
      refine ⟨14302648454835276878198899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19070197939780369170931865 14302648454835276878198899)
      ·
        refine ⟨21453972682252915317298349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302648454835276878198899 21453972682252915317298349)
        ·
          refine ⟨8045239755844843243986881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21453972682252915317298349 8045239755844843243986881)
          ·
            refine ⟨6033929816883632432990161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045239755844843243986881 6033929816883632432990161)
            ·
              refine ⟨4525447362662724324742621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033929816883632432990161 4525447362662724324742621)
              ·
                refine ⟨1697042760998521621778483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4525447362662724324742621 1697042760998521621778483)
                ·
                  refine ⟨2545564141497782432667725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697042760998521621778483 2545564141497782432667725)
                  ·
                    refine ⟨954586553061668412250397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2545564141497782432667725 954586553061668412250397)
                    ·
                      refine ⟨357969957398125654593899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 954586553061668412250397 357969957398125654593899)
                      ·
                        rfl

theorem cell23_697144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_697144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697144 prefixEnd_697144 := by exact prefixLift 697144
  have htrace : WordTrace (prefixWord ++ tailWord_697144) baseStart_697144 baseEnd_697144 := by
    simpa [prefixWord, tailWord_697144, baseEnd_697144] using wordTrace_append hprefix tailTrace_697144
  have hstable : (prefixWord ++ tailWord_697144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697144).length < 2 ^ (prefixWord ++ tailWord_697144).sum := by decide
  have hdescent : baseEnd_697144 < baseStart_697144 := by decide
  rcases family_descends (prefixWord ++ tailWord_697144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697157 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_697157 : Nat := 118140960795 + 697157 * 2 ^ 59
def prefixEnd_697157 : Nat := 4983230072969 + 3 ^ 40 * 697157 * 2
def baseEnd_697157 : Nat := 357976632646634103731339

theorem tailTrace_697157 : CollatzResearch.WordTrace tailWord_697157 prefixEnd_697157 357976632646634103731339 := by
  unfold tailWord_697157
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427404735326728781465725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951603156884485854310483 25427404735326728781465725)
  ·
    refine ⟨9535276775747523293049647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25427404735326728781465725 9535276775747523293049647)
    ·
      refine ⟨14302915163621284939574471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535276775747523293049647 14302915163621284939574471)
      ·
        refine ⟨21454372745431927409361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302915163621284939574471 21454372745431927409361707)
        ·
          refine ⟨32181559118147891114042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21454372745431927409361707 32181559118147891114042561)
          ·
            refine ⟨24136169338610918335531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32181559118147891114042561 24136169338610918335531921)
            ·
              refine ⟨18102127003958188751648941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24136169338610918335531921 18102127003958188751648941)
              ·
                refine ⟨6788297626484320781868353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18102127003958188751648941 6788297626484320781868353)
                ·
                  refine ⟨5091223219863240586401265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788297626484320781868353 5091223219863240586401265)
                  ·
                    refine ⟨3818417414897430439800949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091223219863240586401265 3818417414897430439800949)
                    ·
                      refine ⟨357976632646634103731339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3818417414897430439800949 357976632646634103731339)
                      ·
                        rfl

theorem cell23_697157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_697157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697157 prefixEnd_697157 := by exact prefixLift 697157
  have htrace : WordTrace (prefixWord ++ tailWord_697157) baseStart_697157 baseEnd_697157 := by
    simpa [prefixWord, tailWord_697157, baseEnd_697157] using wordTrace_append hprefix tailTrace_697157
  have hstable : (prefixWord ++ tailWord_697157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697157).length < 2 ^ (prefixWord ++ tailWord_697157).sum := by decide
  have hdescent : baseEnd_697157 < baseStart_697157 := by decide
  rcases family_descends (prefixWord ++ tailWord_697157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697165 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_697165 : Nat := 118140960795 + 697165 * 2 ^ 59
def prefixEnd_697165 : Nat := 4983230072969 + 3 ^ 40 * 697165 * 2
def baseEnd_697165 : Nat := 357980740491870072431303

theorem tailTrace_697165 : CollatzResearch.WordTrace tailWord_697165 prefixEnd_697165 357980740491870072431303 := by
  unfold tailWord_697165
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427696519297746147756949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951797679531830765171299 25427696519297746147756949)
  ·
    refine ⟨1191923274342081850676107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25427696519297746147756949 1191923274342081850676107)
    ·
      refine ⟨1787884911513122776014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191923274342081850676107 1787884911513122776014161)
      ·
        refine ⟨1340913683634842082010621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787884911513122776014161 1340913683634842082010621)
        ·
          refine ⟨502842631363065780753983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1340913683634842082010621 502842631363065780753983)
          ·
            refine ⟨754263947044598671130975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502842631363065780753983 754263947044598671130975)
            ·
              refine ⟨1131395920566898006696463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754263947044598671130975 1131395920566898006696463)
              ·
                refine ⟨1697093880850347010044695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131395920566898006696463 1697093880850347010044695)
                ·
                  refine ⟨2545640821275520515067043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697093880850347010044695 2545640821275520515067043)
                  ·
                    refine ⟨3818461231913280772600565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2545640821275520515067043 3818461231913280772600565)
                    ·
                      refine ⟨357980740491870072431303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3818461231913280772600565 357980740491870072431303)
                      ·
                        rfl

theorem cell23_697165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_697165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697165 prefixEnd_697165 := by exact prefixLift 697165
  have htrace : WordTrace (prefixWord ++ tailWord_697165) baseStart_697165 baseEnd_697165 := by
    simpa [prefixWord, tailWord_697165, baseEnd_697165] using wordTrace_append hprefix tailTrace_697165
  have hstable : (prefixWord ++ tailWord_697165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697165).length < 2 ^ (prefixWord ++ tailWord_697165).sum := by decide
  have hdescent : baseEnd_697165 < baseStart_697165 := by decide
  rcases family_descends (prefixWord ++ tailWord_697165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697167 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_697167 : Nat := 118140960795 + 697167 * 2 ^ 59
def prefixEnd_697167 : Nat := 4983230072969 + 3 ^ 40 * 697167 * 2
def baseEnd_697167 : Nat := 357981767453179064606293

theorem tailTrace_697167 : CollatzResearch.WordTrace tailWord_697167 prefixEnd_697167 357981767453179064606293 := by
  unfold tailWord_697167
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427769465290500489329755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951846310193666992886503 25427769465290500489329755)
  ·
    refine ⟨38141654197935750733994633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25427769465290500489329755 38141654197935750733994633)
    ·
      refine ⟨28606240648451813050495975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38141654197935750733994633 28606240648451813050495975)
      ·
        refine ⟨42909360972677719575743963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28606240648451813050495975 42909360972677719575743963)
        ·
          refine ⟨64364041459016579363615945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42909360972677719575743963 64364041459016579363615945)
          ·
            refine ⟨48273031094262434522711959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64364041459016579363615945 48273031094262434522711959)
            ·
              refine ⟨72409546641393651784067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48273031094262434522711959 72409546641393651784067939)
              ·
                refine ⟨108614319962090477676101909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72409546641393651784067939 108614319962090477676101909)
                ·
                  refine ⟨5091296248222991141067277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108614319962090477676101909 5091296248222991141067277)
                  ·
                    refine ⟨1909236093083621677900229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091296248222991141067277 1909236093083621677900229)
                    ·
                      refine ⟨357981767453179064606293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909236093083621677900229 357981767453179064606293)
                      ·
                        rfl

theorem cell23_697167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_697167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697167 prefixEnd_697167 := by exact prefixLift 697167
  have htrace : WordTrace (prefixWord ++ tailWord_697167) baseStart_697167 baseEnd_697167 := by
    simpa [prefixWord, tailWord_697167, baseEnd_697167] using wordTrace_append hprefix tailTrace_697167
  have hstable : (prefixWord ++ tailWord_697167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697167).length < 2 ^ (prefixWord ++ tailWord_697167).sum := by decide
  have hdescent : baseEnd_697167 < baseStart_697167 := by decide
  rcases family_descends (prefixWord ++ tailWord_697167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697171 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 1, 3, 2]
def baseStart_697171 : Nat := 118140960795 + 697171 * 2 ^ 59
def prefixEnd_697171 : Nat := 4983230072969 + 3 ^ 40 * 697171 * 2
def baseEnd_697171 : Nat := 357983821375797048956275

theorem tailTrace_697171 : CollatzResearch.WordTrace tailWord_697171 prefixEnd_697171 357983821375797048956275 := by
  unfold tailWord_697171
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427915357276009172475367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951943571517339448316911 25427915357276009172475367)
  ·
    refine ⟨38141873035914013758713051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25427915357276009172475367 38141873035914013758713051)
    ·
      refine ⟨57212809553871020638069577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38141873035914013758713051 57212809553871020638069577)
      ·
        refine ⟨42909607165403265478552183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57212809553871020638069577 42909607165403265478552183)
        ·
          refine ⟨64364410748104898217828275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42909607165403265478552183 64364410748104898217828275)
          ·
            refine ⟨96546616122157347326742413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64364410748104898217828275 96546616122157347326742413)
            ·
              refine ⟨36204981045809005247528405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96546616122157347326742413 36204981045809005247528405)
              ·
                refine ⟨848554243261148560488947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36204981045809005247528405 848554243261148560488947)
                ·
                  refine ⟨1272831364891722840733421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848554243261148560488947 1272831364891722840733421)
                  ·
                    refine ⟨477311761834396065275033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272831364891722840733421 477311761834396065275033)
                    ·
                      refine ⟨357983821375797048956275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477311761834396065275033 357983821375797048956275)
                      ·
                        rfl

theorem cell23_697171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3, 2].length) (baseStart_697171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697171 prefixEnd_697171 := by exact prefixLift 697171
  have htrace : WordTrace (prefixWord ++ tailWord_697171) baseStart_697171 baseEnd_697171 := by
    simpa [prefixWord, tailWord_697171, baseEnd_697171] using wordTrace_append hprefix tailTrace_697171
  have hstable : (prefixWord ++ tailWord_697171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697171).length < 2 ^ (prefixWord ++ tailWord_697171).sum := by decide
  have hdescent : baseEnd_697171 < baseStart_697171 := by decide
  rcases family_descends (prefixWord ++ tailWord_697171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697178 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_697178 : Nat := 118140960795 + 697178 * 2 ^ 59
def prefixEnd_697178 : Nat := 4983230072969 + 3 ^ 40 * 697178 * 2
def baseEnd_697178 : Nat := 357987415740378521568743

theorem tailTrace_697178 : CollatzResearch.WordTrace tailWord_697178 prefixEnd_697178 357987415740378521568743 := by
  unfold tailWord_697178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357042667062662341995047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16952113778833766245320125 6357042667062662341995047)
  ·
    refine ⟨9535564000593993512992571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6357042667062662341995047 9535564000593993512992571)
    ·
      refine ⟨14303346000890990269488857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535564000593993512992571 14303346000890990269488857)
      ·
        refine ⟨10727509500668242702116643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14303346000890990269488857 10727509500668242702116643)
        ·
          refine ⟨16091264251002364053174965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10727509500668242702116643 16091264251002364053174965)
          ·
            refine ⟨1508556023531471629985153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16091264251002364053174965 1508556023531471629985153)
            ·
              refine ⟨1131417017648603722488865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508556023531471629985153 1131417017648603722488865)
              ·
                refine ⟨848562763236452791866649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131417017648603722488865 848562763236452791866649)
                ·
                  refine ⟨636422072427339593899987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 848562763236452791866649 636422072427339593899987)
                  ·
                    refine ⟨954633108641009390849981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 636422072427339593899987 954633108641009390849981)
                    ·
                      refine ⟨357987415740378521568743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 954633108641009390849981 357987415740378521568743)
                      ·
                        rfl

theorem cell23_697178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_697178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697178 prefixEnd_697178 := by exact prefixLift 697178
  have htrace : WordTrace (prefixWord ++ tailWord_697178) baseStart_697178 baseEnd_697178 := by
    simpa [prefixWord, tailWord_697178, baseEnd_697178] using wordTrace_append hprefix tailTrace_697178
  have hstable : (prefixWord ++ tailWord_697178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697178).length < 2 ^ (prefixWord ++ tailWord_697178).sum := by decide
  have hdescent : baseEnd_697178 < baseStart_697178 := by decide
  rcases family_descends (prefixWord ++ tailWord_697178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697201 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_697201 : Nat := 118140960795 + 697201 * 2 ^ 59
def prefixEnd_697201 : Nat := 4983230072969 + 3 ^ 40 * 697201 * 2
def baseEnd_697201 : Nat := 357999225795431931581137

theorem tailTrace_697201 : CollatzResearch.WordTrace tailWord_697201 prefixEnd_697201 357999225795431931581137 := by
  unfold tailWord_697201
  simp only [CollatzResearch.WordTrace]
  refine ⟨25429009547167324296067457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16952673031444882864044971 25429009547167324296067457)
  ·
    refine ⟨19071757160375493222050593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25429009547167324296067457 19071757160375493222050593)
    ·
      refine ⟨14303817870281619916537945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19071757160375493222050593 14303817870281619916537945)
      ·
        refine ⟨10727863402711214937403459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14303817870281619916537945 10727863402711214937403459)
        ·
          refine ⟨16091795104066822406105189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10727863402711214937403459 16091795104066822406105189)
          ·
            refine ⟨3017211582012529201144723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16091795104066822406105189 3017211582012529201144723)
            ·
              refine ⟨4525817373018793801717085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017211582012529201144723 4525817373018793801717085)
              ·
                refine ⟨1697181514882047675643907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4525817373018793801717085 1697181514882047675643907)
                ·
                  refine ⟨2545772272323071513465861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697181514882047675643907 2545772272323071513465861)
                  ·
                    refine ⟨477332301060575908774849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545772272323071513465861 477332301060575908774849)
                    ·
                      refine ⟨357999225795431931581137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477332301060575908774849 357999225795431931581137)
                      ·
                        rfl

theorem cell23_697201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_697201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697201 prefixEnd_697201 := by exact prefixLift 697201
  have htrace : WordTrace (prefixWord ++ tailWord_697201) baseStart_697201 baseEnd_697201 := by
    simpa [prefixWord, tailWord_697201, baseEnd_697201] using wordTrace_append hprefix tailTrace_697201
  have hstable : (prefixWord ++ tailWord_697201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697201).length < 2 ^ (prefixWord ++ tailWord_697201).sum := by decide
  have hdescent : baseEnd_697201 < baseStart_697201 := by decide
  rcases family_descends (prefixWord ++ tailWord_697201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697274 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_697274 : Nat := 118140960795 + 697274 * 2 ^ 59
def prefixEnd_697274 : Nat := 4983230072969 + 3 ^ 40 * 697274 * 2
def baseEnd_697274 : Nat := 358036709883210145968301

theorem tailTrace_697274 : CollatzResearch.WordTrace tailWord_697274 prefixEnd_697274 358036709883210145968301 := by
  unfold tailWord_697274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357918018975714440868719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16954448050601905175649917 6357918018975714440868719)
  ·
    refine ⟨9536877028463571661303079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6357918018975714440868719 9536877028463571661303079)
    ·
      refine ⟨14305315542695357491954619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9536877028463571661303079 14305315542695357491954619)
      ·
        refine ⟨21457973314043036237931929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14305315542695357491954619 21457973314043036237931929)
        ·
          refine ⟨16093479985532277178448947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21457973314043036237931929 16093479985532277178448947)
          ·
            refine ⟨24140219978298415767673421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16093479985532277178448947 24140219978298415767673421)
            ·
              refine ⟨9052582491861905912877533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24140219978298415767673421 9052582491861905912877533)
              ·
                refine ⟨3394718434448214717329075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9052582491861905912877533 3394718434448214717329075)
                ·
                  refine ⟨5092077651672322075993613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394718434448214717329075 5092077651672322075993613)
                  ·
                    refine ⟨1909529119377120778497605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5092077651672322075993613 1909529119377120778497605)
                    ·
                      refine ⟨358036709883210145968301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909529119377120778497605 358036709883210145968301)
                      ·
                        rfl

theorem cell23_697274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_697274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697274 prefixEnd_697274 := by exact prefixLift 697274
  have htrace : WordTrace (prefixWord ++ tailWord_697274) baseStart_697274 baseEnd_697274 := by
    simpa [prefixWord, tailWord_697274, baseEnd_697274] using wordTrace_append hprefix tailTrace_697274
  have hstable : (prefixWord ++ tailWord_697274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697274).length < 2 ^ (prefixWord ++ tailWord_697274).sum := by decide
  have hdescent : baseEnd_697274 < baseStart_697274 := by decide
  rcases family_descends (prefixWord ++ tailWord_697274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697291 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4]
def baseStart_697291 : Nat := 118140960795 + 697291 * 2 ^ 59
def prefixEnd_697291 : Nat := 4983230072969 + 3 ^ 40 * 697291 * 2
def baseEnd_697291 : Nat := 358045439054336579455723

theorem tailTrace_697291 : CollatzResearch.WordTrace tailWord_697291 prefixEnd_697291 358045439054336579455723 := by
  unfold tailWord_697291
  simp only [CollatzResearch.WordTrace]
  refine ⟨25432292116841269666843727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16954861411227513111229151 25432292116841269666843727)
  ·
    refine ⟨38148438175261904500265591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25432292116841269666843727 38148438175261904500265591)
    ·
      refine ⟨57222657262892856750398387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38148438175261904500265591 57222657262892856750398387)
      ·
        refine ⟨85833985894339285125597581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57222657262892856750398387 85833985894339285125597581)
        ·
          refine ⟨32187744710377231922099093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85833985894339285125597581 32187744710377231922099093)
          ·
            refine ⟨1508800533298932746348395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32187744710377231922099093 1508800533298932746348395)
            ·
              refine ⟨2263200799948399119522593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508800533298932746348395 2263200799948399119522593)
              ·
                refine ⟨1697400599961299339641945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263200799948399119522593 1697400599961299339641945)
                ·
                  refine ⟨1273050449970974504731459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697400599961299339641945 1273050449970974504731459)
                  ·
                    refine ⟨1909575674956461757097189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273050449970974504731459 1909575674956461757097189)
                    ·
                      refine ⟨358045439054336579455723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909575674956461757097189 358045439054336579455723)
                      ·
                        rfl

theorem cell23_697291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_697291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697291 prefixEnd_697291 := by exact prefixLift 697291
  have htrace : WordTrace (prefixWord ++ tailWord_697291) baseStart_697291 baseEnd_697291 := by
    simpa [prefixWord, tailWord_697291, baseEnd_697291] using wordTrace_append hprefix tailTrace_697291
  have hstable : (prefixWord ++ tailWord_697291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697291).length < 2 ^ (prefixWord ++ tailWord_697291).sum := by decide
  have hdescent : baseEnd_697291 < baseStart_697291 := by decide
  rcases family_descends (prefixWord ++ tailWord_697291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697352 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 1, 4]
def baseStart_697352 : Nat := 118140960795 + 697352 * 2 ^ 59
def prefixEnd_697352 : Nat := 4983230072969 + 3 ^ 40 * 697352 * 2
def baseEnd_697352 : Nat := 119358920458086946930981

theorem tailTrace_697352 : CollatzResearch.WordTrace tailWord_697352 prefixEnd_697352 119358920458086946930981 := by
  unfold tailWord_697352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12717258484810138542407155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16956344646413518056542873 12717258484810138542407155)
  ·
    refine ⟨19075887727215207813610733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12717258484810138542407155 19075887727215207813610733)
    ·
      refine ⟨7153457897705702930104025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19075887727215207813610733 7153457897705702930104025)
      ·
        refine ⟨5365093423279277197578019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153457897705702930104025 5365093423279277197578019)
        ·
          refine ⟨8047640134918915796367029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365093423279277197578019 8047640134918915796367029)
          ·
            refine ⟨754466262648648355909409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8047640134918915796367029 754466262648648355909409)
            ·
              refine ⟨565849696986486266932057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754466262648648355909409 565849696986486266932057)
              ·
                refine ⟨424387272739864700199043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565849696986486266932057 424387272739864700199043)
                ·
                  refine ⟨636580909109797050298565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424387272739864700199043 636580909109797050298565)
                  ·
                    refine ⟨119358920458086946930981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 636580909109797050298565 119358920458086946930981)
                    ·
                      rfl

theorem cell23_697352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_697352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697352 prefixEnd_697352 := by exact prefixLift 697352
  have htrace : WordTrace (prefixWord ++ tailWord_697352) baseStart_697352 baseEnd_697352 := by
    simpa [prefixWord, tailWord_697352, baseEnd_697352] using wordTrace_append hprefix tailTrace_697352
  have hstable : (prefixWord ++ tailWord_697352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697352).length < 2 ^ (prefixWord ++ tailWord_697352).sum := by decide
  have hdescent : baseEnd_697352 < baseStart_697352 := by decide
  rcases family_descends (prefixWord ++ tailWord_697352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697381 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_697381 : Nat := 118140960795 + 697381 * 2 ^ 59
def prefixEnd_697381 : Nat := 4983230072969 + 3 ^ 40 * 697381 * 2
def baseEnd_697381 : Nat := 358091652313241227330309

theorem tailTrace_697381 : CollatzResearch.WordTrace tailWord_697381 prefixEnd_697381 358091652313241227330309 := by
  unfold tailWord_697381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25435574686515215037619997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16957049791010143358413331 25435574686515215037619997)
  ·
    refine ⟨9538340507443205639107499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25435574686515215037619997 9538340507443205639107499)
    ·
      refine ⟨14307510761164808458661249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9538340507443205639107499 14307510761164808458661249)
      ·
        refine ⟨10730633070873606343995937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14307510761164808458661249 10730633070873606343995937)
        ·
          refine ⟨8047974803155204757996953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10730633070873606343995937 8047974803155204757996953)
          ·
            refine ⟨6035981102366403568497715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8047974803155204757996953 6035981102366403568497715)
            ·
              refine ⟨9053971653549605352746573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035981102366403568497715 9053971653549605352746573)
              ·
                refine ⟨3395239370081102007279965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9053971653549605352746573 3395239370081102007279965)
                ·
                  refine ⟨1273214763780413252729987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3395239370081102007279965 1273214763780413252729987)
                  ·
                    refine ⟨1909822145670619879094981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273214763780413252729987 1909822145670619879094981)
                    ·
                      refine ⟨358091652313241227330309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909822145670619879094981 358091652313241227330309)
                      ·
                        rfl

theorem cell23_697381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_697381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697381 prefixEnd_697381 := by exact prefixLift 697381
  have htrace : WordTrace (prefixWord ++ tailWord_697381) baseStart_697381 baseEnd_697381 := by
    simpa [prefixWord, tailWord_697381, baseEnd_697381] using wordTrace_append hprefix tailTrace_697381
  have hstable : (prefixWord ++ tailWord_697381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697381).length < 2 ^ (prefixWord ++ tailWord_697381).sum := by decide
  have hdescent : baseEnd_697381 < baseStart_697381 := by decide
  rcases family_descends (prefixWord ++ tailWord_697381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697415 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_697415 : Nat := 118140960795 + 697415 * 2 ^ 59
def prefixEnd_697415 : Nat := 4983230072969 + 3 ^ 40 * 697415 * 2
def baseEnd_697415 : Nat := 358109110655494094305153

theorem tailTrace_697415 : CollatzResearch.WordTrace tailWord_697415 prefixEnd_697415 358109110655494094305153 := by
  unfold tailWord_697415
  simp only [CollatzResearch.WordTrace]
  refine ⟨25436814768392038844357699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16957876512261359229571799 25436814768392038844357699)
  ·
    refine ⟨38155222152588058266536549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25436814768392038844357699 38155222152588058266536549)
    ·
      refine ⟨7154104153610260924975603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38155222152588058266536549 7154104153610260924975603)
      ·
        refine ⟨10731156230415391387463405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7154104153610260924975603 10731156230415391387463405)
        ·
          refine ⟨4024183586405771770298777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10731156230415391387463405 4024183586405771770298777)
          ·
            refine ⟨3018137689804328827724083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024183586405771770298777 3018137689804328827724083)
            ·
              refine ⟨4527206534706493241586125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018137689804328827724083 4527206534706493241586125)
              ·
                refine ⟨1697702450514934965594797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4527206534706493241586125 1697702450514934965594797)
                ·
                  refine ⟨636638418943100612098049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1697702450514934965594797 636638418943100612098049)
                  ·
                    refine ⟨477478814207325459073537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636638418943100612098049 477478814207325459073537)
                    ·
                      refine ⟨358109110655494094305153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477478814207325459073537 358109110655494094305153)
                      ·
                        rfl

theorem cell23_697415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_697415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697415 prefixEnd_697415 := by exact prefixLift 697415
  have htrace : WordTrace (prefixWord ++ tailWord_697415) baseStart_697415 baseEnd_697415 := by
    simpa [prefixWord, tailWord_697415, baseEnd_697415] using wordTrace_append hprefix tailTrace_697415
  have hstable : (prefixWord ++ tailWord_697415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697415).length < 2 ^ (prefixWord ++ tailWord_697415).sum := by decide
  have hdescent : baseEnd_697415 < baseStart_697415 := by decide
  rcases family_descends (prefixWord ++ tailWord_697415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697428 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_697428 : Nat := 118140960795 + 697428 * 2 ^ 59
def prefixEnd_697428 : Nat := 4983230072969 + 3 ^ 40 * 697428 * 2
def baseEnd_697428 : Nat := 358115785904002543442593

theorem tailTrace_697428 : CollatzResearch.WordTrace tailWord_697428 prefixEnd_697428 358115785904002543442593 := by
  unfold tailWord_697428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718644458672471032290469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16958192611563294709720625 12718644458672471032290469)
  ·
    refine ⟨2384745836001088318554463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12718644458672471032290469 2384745836001088318554463)
    ·
      refine ⟨3577118754001632477831695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384745836001088318554463 3577118754001632477831695)
      ·
        refine ⟨5365678131002448716747543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577118754001632477831695 5365678131002448716747543)
        ·
          refine ⟨8048517196503673075121315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365678131002448716747543 8048517196503673075121315)
          ·
            refine ⟨12072775794755509612681973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048517196503673075121315 12072775794755509612681973)
            ·
              refine ⟨1131822730758329026188935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12072775794755509612681973 1131822730758329026188935)
              ·
                refine ⟨1697734096137493539283403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131822730758329026188935 1697734096137493539283403)
                ·
                  refine ⟨2546601144206240308925105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697734096137493539283403 2546601144206240308925105)
                  ·
                    refine ⟨1909950858154680231693829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2546601144206240308925105 1909950858154680231693829)
                    ·
                      refine ⟨358115785904002543442593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1909950858154680231693829 358115785904002543442593)
                      ·
                        rfl

theorem cell23_697428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_697428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697428 prefixEnd_697428 := by exact prefixLift 697428
  have htrace : WordTrace (prefixWord ++ tailWord_697428) baseStart_697428 baseEnd_697428 := by
    simpa [prefixWord, tailWord_697428, baseEnd_697428] using wordTrace_append hprefix tailTrace_697428
  have hstable : (prefixWord ++ tailWord_697428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697428).length < 2 ^ (prefixWord ++ tailWord_697428).sum := by decide
  have hdescent : baseEnd_697428 < baseStart_697428 := by decide
  rcases family_descends (prefixWord ++ tailWord_697428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697449 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 1, 2, 2]
def baseStart_697449 : Nat := 118140960795 + 697449 * 2 ^ 59
def prefixEnd_697449 : Nat := 4983230072969 + 3 ^ 40 * 697449 * 2
def baseEnd_697449 : Nat := 358126568997746961279997

theorem tailTrace_697449 : CollatzResearch.WordTrace tailWord_697449 prefixEnd_697449 358126568997746961279997 := by
  unfold tailWord_697449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25438054850268862651095401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16958703233512575100730267 25438054850268862651095401)
  ·
    refine ⟨19078541137701646988321551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25438054850268862651095401 19078541137701646988321551)
    ·
      refine ⟨28617811706552470482482327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078541137701646988321551 28617811706552470482482327)
      ·
        refine ⟨42926717559828705723723491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28617811706552470482482327 42926717559828705723723491)
        ·
          refine ⟨64390076339743058585585237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42926717559828705723723491 64390076339743058585585237)
          ·
            refine ⟨754571207106363967799827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 64390076339743058585585237 754571207106363967799827)
            ·
              refine ⟨1131856810659545951699741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754571207106363967799827 1131856810659545951699741)
              ·
                refine ⟨424446303997329731887403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131856810659545951699741 424446303997329731887403)
                ·
                  refine ⟨636669455995994597831105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424446303997329731887403 636669455995994597831105)
                  ·
                    refine ⟨477502091996995948373329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636669455995994597831105 477502091996995948373329)
                    ·
                      refine ⟨358126568997746961279997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477502091996995948373329 358126568997746961279997)
                      ·
                        rfl

theorem cell23_697449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 2, 2].length) (baseStart_697449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697449 prefixEnd_697449 := by exact prefixLift 697449
  have htrace : WordTrace (prefixWord ++ tailWord_697449) baseStart_697449 baseEnd_697449 := by
    simpa [prefixWord, tailWord_697449, baseEnd_697449] using wordTrace_append hprefix tailTrace_697449
  have hstable : (prefixWord ++ tailWord_697449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697449).length < 2 ^ (prefixWord ++ tailWord_697449).sum := by decide
  have hdescent : baseEnd_697449 < baseStart_697449 := by decide
  rcases family_descends (prefixWord ++ tailWord_697449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697491 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_697491 : Nat := 118140960795 + 697491 * 2 ^ 59
def prefixEnd_697491 : Nat := 4983230072969 + 3 ^ 40 * 697491 * 2
def baseEnd_697491 : Nat := 358148135185235796954803

theorem tailTrace_697491 : CollatzResearch.WordTrace tailWord_697491 prefixEnd_697491 358148135185235796954803 := by
  unfold tailWord_697491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439586716116703824124327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16959724477411135882749551 25439586716116703824124327)
  ·
    refine ⟨38159380074175055736186491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25439586716116703824124327 38159380074175055736186491)
    ·
      refine ⟨57239070111262583604279737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38159380074175055736186491 57239070111262583604279737)
      ·
        refine ⟨42929302583446937703209803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57239070111262583604279737 42929302583446937703209803)
        ·
          refine ⟨64393953875170406554814705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42929302583446937703209803 64393953875170406554814705)
          ·
            refine ⟨48295465406377804916111029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64393953875170406554814705 48295465406377804916111029)
            ·
              refine ⟨4527699881847919210885409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48295465406377804916111029 4527699881847919210885409)
              ·
                refine ⟨3395774911385939408164057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527699881847919210885409 3395774911385939408164057)
                ·
                  refine ⟨2546831183539454556123043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395774911385939408164057 2546831183539454556123043)
                  ·
                    refine ⟨3820246775309181834184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546831183539454556123043 3820246775309181834184565)
                    ·
                      refine ⟨358148135185235796954803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3820246775309181834184565 358148135185235796954803)
                      ·
                        rfl

theorem cell23_697491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_697491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697491 prefixEnd_697491 := by exact prefixLift 697491
  have htrace : WordTrace (prefixWord ++ tailWord_697491) baseStart_697491 baseEnd_697491 := by
    simpa [prefixWord, tailWord_697491, baseEnd_697491] using wordTrace_append hprefix tailTrace_697491
  have hstable : (prefixWord ++ tailWord_697491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697491).length < 2 ^ (prefixWord ++ tailWord_697491).sum := by decide
  have hdescent : baseEnd_697491 < baseStart_697491 := by decide
  rcases family_descends (prefixWord ++ tailWord_697491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697505 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_697505 : Nat := 118140960795 + 697505 * 2 ^ 59
def prefixEnd_697505 : Nat := 4983230072969 + 3 ^ 40 * 697505 * 2
def baseEnd_697505 : Nat := 358155323914398742179739

theorem tailTrace_697505 : CollatzResearch.WordTrace tailWord_697505 prefixEnd_697505 358155323914398742179739 := by
  unfold tailWord_697505
  simp only [CollatzResearch.WordTrace]
  refine ⟨25440097338065984215133969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16960064892043989476755979 25440097338065984215133969)
  ·
    refine ⟨19080073003549488161350477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25440097338065984215133969 19080073003549488161350477)
    ·
      refine ⟨7155027376331058060506429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19080073003549488161350477 7155027376331058060506429)
      ·
        refine ⟨2683135266124146772689911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7155027376331058060506429 2683135266124146772689911)
        ·
          refine ⟨4024702899186220159034867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683135266124146772689911 4024702899186220159034867)
          ·
            refine ⟨6037054348779330238552301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024702899186220159034867 6037054348779330238552301)
            ·
              refine ⟨2263895380792248839457113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6037054348779330238552301 2263895380792248839457113)
              ·
                refine ⟨1697921535594186629592835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263895380792248839457113 1697921535594186629592835)
                ·
                  refine ⟨2546882303391279944389253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697921535594186629592835 2546882303391279944389253)
                  ·
                    refine ⟨477540431885864989572985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546882303391279944389253 477540431885864989572985)
                    ·
                      refine ⟨358155323914398742179739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477540431885864989572985 358155323914398742179739)
                      ·
                        rfl

theorem cell23_697505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_697505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697505 prefixEnd_697505 := by exact prefixLift 697505
  have htrace : WordTrace (prefixWord ++ tailWord_697505) baseStart_697505 baseEnd_697505 := by
    simpa [prefixWord, tailWord_697505, baseEnd_697505] using wordTrace_append hprefix tailTrace_697505
  have hstable : (prefixWord ++ tailWord_697505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697505).length < 2 ^ (prefixWord ++ tailWord_697505).sum := by decide
  have hdescent : baseEnd_697505 < baseStart_697505 := by decide
  rcases family_descends (prefixWord ++ tailWord_697505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697508 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_697508 : Nat := 118140960795 + 697508 * 2 ^ 59
def prefixEnd_697508 : Nat := 4983230072969 + 3 ^ 40 * 697508 * 2
def baseEnd_697508 : Nat := 358156864356362230442225

theorem tailTrace_697508 : CollatzResearch.WordTrace tailWord_697508 prefixEnd_697508 358156864356362230442225 := by
  unfold tailWord_697508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720103378527557863746589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16960137838036743818328785 12720103378527557863746589)
  ·
    refine ⟨4770038766947834198904971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12720103378527557863746589 4770038766947834198904971)
    ·
      refine ⟨7155058150421751298357457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770038766947834198904971 7155058150421751298357457)
      ·
        refine ⟨5366293612816313473768093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7155058150421751298357457 5366293612816313473768093)
        ·
          refine ⟨2012360104806117552663035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5366293612816313473768093 2012360104806117552663035)
          ·
            refine ⟨3018540157209176328994553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012360104806117552663035 3018540157209176328994553)
            ·
              refine ⟨2263905117906882246745915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018540157209176328994553 2263905117906882246745915)
              ·
                refine ⟨3395857676860323370118873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263905117906882246745915 3395857676860323370118873)
                ·
                  refine ⟨2546893257645242527589155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395857676860323370118873 2546893257645242527589155)
                  ·
                    refine ⟨3820339886467863791383733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546893257645242527589155 3820339886467863791383733)
                    ·
                      refine ⟨358156864356362230442225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3820339886467863791383733 358156864356362230442225)
                      ·
                        rfl

theorem cell23_697508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_697508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697508 prefixEnd_697508 := by exact prefixLift 697508
  have htrace : WordTrace (prefixWord ++ tailWord_697508) baseStart_697508 baseEnd_697508 := by
    simpa [prefixWord, tailWord_697508, baseEnd_697508] using wordTrace_append hprefix tailTrace_697508
  have hstable : (prefixWord ++ tailWord_697508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697508).length < 2 ^ (prefixWord ++ tailWord_697508).sum := by decide
  have hdescent : baseEnd_697508 < baseStart_697508 := by decide
  rcases family_descends (prefixWord ++ tailWord_697508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697522 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_697522 : Nat := 118140960795 + 697522 * 2 ^ 59
def prefixEnd_697522 : Nat := 4983230072969 + 3 ^ 40 * 697522 * 2
def baseEnd_697522 : Nat := 358164053085525175667161

theorem tailTrace_697522 : CollatzResearch.WordTrace tailWord_697522 prefixEnd_697522 358164053085525175667161 := by
  unfold tailWord_697522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360179344751099029625705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16960478252669597412335213 6360179344751099029625705)
  ·
    refine ⟨4770134508563324272219279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6360179344751099029625705 4770134508563324272219279)
    ·
      refine ⟨7155201762844986408328919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770134508563324272219279 7155201762844986408328919)
      ·
        refine ⟨10732802644267479612493379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155201762844986408328919 10732802644267479612493379)
        ·
          refine ⟨16099203966401219418740069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10732802644267479612493379 16099203966401219418740069)
          ·
            refine ⟨3018600743700228641013763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16099203966401219418740069 3018600743700228641013763)
            ·
              refine ⟨4527901115550342961520645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018600743700228641013763 4527901115550342961520645)
              ·
                refine ⟨848981459165689305285121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4527901115550342961520645 848981459165689305285121)
                ·
                  refine ⟨636736094374266978963841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 848981459165689305285121 636736094374266978963841)
                  ·
                    refine ⟨477552070780700234222881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636736094374266978963841 477552070780700234222881)
                    ·
                      refine ⟨358164053085525175667161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477552070780700234222881 358164053085525175667161)
                      ·
                        rfl

theorem cell23_697522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_697522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697522 prefixEnd_697522 := by exact prefixLift 697522
  have htrace : WordTrace (prefixWord ++ tailWord_697522) baseStart_697522 baseEnd_697522 := by
    simpa [prefixWord, tailWord_697522, baseEnd_697522] using wordTrace_append hprefix tailTrace_697522
  have hstable : (prefixWord ++ tailWord_697522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697522).length < 2 ^ (prefixWord ++ tailWord_697522).sum := by decide
  have hdescent : baseEnd_697522 < baseStart_697522 := by decide
  rcases family_descends (prefixWord ++ tailWord_697522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697541 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_697541 : Nat := 118140960795 + 697541 * 2 ^ 59
def prefixEnd_697541 : Nat := 4983230072969 + 3 ^ 40 * 697541 * 2
def baseEnd_697541 : Nat := 119391269739320200443191

theorem tailTrace_697541 : CollatzResearch.WordTrace tailWord_697541 prefixEnd_697541 119391269739320200443191 := by
  unfold tailWord_697541
  simp only [CollatzResearch.WordTrace]
  refine ⟨25441410365935562363444477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16960940243957041575629651 25441410365935562363444477)
  ·
    refine ⟨9540528887225835886291679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25441410365935562363444477 9540528887225835886291679)
    ·
      refine ⟨14310793330838753829437519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9540528887225835886291679 14310793330838753829437519)
      ·
        refine ⟨21466189996258130744156279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14310793330838753829437519 21466189996258130744156279)
        ·
          refine ⟨32199284994387196116234419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21466189996258130744156279 32199284994387196116234419)
          ·
            refine ⟨48298927491580794174351629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32199284994387196116234419 48298927491580794174351629)
            ·
              refine ⟨18112097809342797815381861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48298927491580794174351629 18112097809342797815381861)
              ·
                refine ⟨3396018339251774590384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18112097809342797815381861 3396018339251774590384099)
                ·
                  refine ⟨5094027508877661885576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396018339251774590384099 5094027508877661885576149)
                  ·
                    refine ⟨119391269739320200443191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5094027508877661885576149 119391269739320200443191)
                    ·
                      rfl

theorem cell23_697541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_697541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697541 prefixEnd_697541 := by exact prefixLift 697541
  have htrace : WordTrace (prefixWord ++ tailWord_697541) baseStart_697541 baseEnd_697541 := by
    simpa [prefixWord, tailWord_697541, baseEnd_697541] using wordTrace_append hprefix tailTrace_697541
  have hstable : (prefixWord ++ tailWord_697541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697541).length < 2 ^ (prefixWord ++ tailWord_697541).sum := by decide
  have hdescent : baseEnd_697541 < baseStart_697541 := by decide
  rcases family_descends (prefixWord ++ tailWord_697541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697551 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_697551 : Nat := 118140960795 + 697551 * 2 ^ 59
def prefixEnd_697551 : Nat := 4983230072969 + 3 ^ 40 * 697551 * 2
def baseEnd_697551 : Nat := 358178944024505562204527

theorem tailTrace_697551 : CollatzResearch.WordTrace tailWord_697551 prefixEnd_697551 358178944024505562204527 := by
  unfold tailWord_697551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25441775095899334071308507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16961183397266222714205671 25441775095899334071308507)
  ·
    refine ⟨38162662643849001106962761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25441775095899334071308507 38162662643849001106962761)
    ·
      refine ⟨28621996982886750830222071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38162662643849001106962761 28621996982886750830222071)
      ·
        refine ⟨42932995474330126245333107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28621996982886750830222071 42932995474330126245333107)
        ·
          refine ⟨64399493211495189367999661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42932995474330126245333107 64399493211495189367999661)
          ·
            refine ⟨24149809954310696012999873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64399493211495189367999661 24149809954310696012999873)
            ·
              refine ⟨18112357465733022009749905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24149809954310696012999873 18112357465733022009749905)
              ·
                refine ⟨13584268099299766507312429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18112357465733022009749905 13584268099299766507312429)
                ·
                  refine ⟨5094100537237412440242161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13584268099299766507312429 5094100537237412440242161)
                  ·
                    refine ⟨3820575402928059330181621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094100537237412440242161 3820575402928059330181621)
                    ·
                      refine ⟨358178944024505562204527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3820575402928059330181621 358178944024505562204527)
                      ·
                        rfl

theorem cell23_697551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_697551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697551 prefixEnd_697551 := by exact prefixLift 697551
  have htrace : WordTrace (prefixWord ++ tailWord_697551) baseStart_697551 baseEnd_697551 := by
    simpa [prefixWord, tailWord_697551, baseEnd_697551] using wordTrace_append hprefix tailTrace_697551
  have hstable : (prefixWord ++ tailWord_697551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697551).length < 2 ^ (prefixWord ++ tailWord_697551).sum := by decide
  have hdescent : baseEnd_697551 < baseStart_697551 := by decide
  rcases family_descends (prefixWord ++ tailWord_697551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697632 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_697632 : Nat := 118140960795 + 697632 * 2 ^ 59
def prefixEnd_697632 : Nat := 4983230072969 + 3 ^ 40 * 697632 * 2
def baseEnd_697632 : Nat := 358220535957519745291655

theorem tailTrace_697632 : CollatzResearch.WordTrace tailWord_697632 prefixEnd_697632 358220535957519745291655 := by
  unfold tailWord_697632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722364704302942452503575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16963152939070589936671433 12722364704302942452503575)
  ·
    refine ⟨19083547056454413678755363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722364704302942452503575 19083547056454413678755363)
    ·
      refine ⟨28625320584681620518133045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083547056454413678755363 28625320584681620518133045)
      ·
        refine ⟨2683623804813901923574973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28625320584681620518133045 2683623804813901923574973)
        ·
          refine ⟨1006358926805213221340615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2683623804813901923574973 1006358926805213221340615)
          ·
            refine ⟨1509538390207819832010923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006358926805213221340615 1509538390207819832010923)
            ·
              refine ⟨2264307585311729748016385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509538390207819832010923 2264307585311729748016385)
              ·
                refine ⟨1698230688983797311012289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264307585311729748016385 1698230688983797311012289)
                ·
                  refine ⟨1273673016737847983259217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698230688983797311012289 1273673016737847983259217)
                  ·
                    refine ⟨955254762553385987444413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1273673016737847983259217 955254762553385987444413)
                    ·
                      refine ⟨358220535957519745291655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955254762553385987444413 358220535957519745291655)
                      ·
                        rfl

theorem cell23_697632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_697632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697632 prefixEnd_697632 := by exact prefixLift 697632
  have htrace : WordTrace (prefixWord ++ tailWord_697632) baseStart_697632 baseEnd_697632 := by
    simpa [prefixWord, tailWord_697632, baseEnd_697632] using wordTrace_append hprefix tailTrace_697632
  have hstable : (prefixWord ++ tailWord_697632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697632).length < 2 ^ (prefixWord ++ tailWord_697632).sum := by decide
  have hdescent : baseEnd_697632 < baseStart_697632 := by decide
  rcases family_descends (prefixWord ++ tailWord_697632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697648 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_697648 : Nat := 118140960795 + 697648 * 2 ^ 59
def prefixEnd_697648 : Nat := 4983230072969 + 3 ^ 40 * 697648 * 2
def baseEnd_697648 : Nat := 119409583882663894230527

theorem tailTrace_697648 : CollatzResearch.WordTrace tailWord_697648 prefixEnd_697648 119409583882663894230527 := by
  unfold tailWord_697648
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722656488273959818794799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16963541984365279758393065 12722656488273959818794799)
  ·
    refine ⟨19083984732410939728192199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722656488273959818794799 19083984732410939728192199)
    ·
      refine ⟨28625977098616409592288299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083984732410939728192199 28625977098616409592288299)
      ·
        refine ⟨42938965647924614388432449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28625977098616409592288299 42938965647924614388432449)
        ·
          refine ⟨32204224235943460791324337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42938965647924614388432449 32204224235943460791324337)
          ·
            refine ⟨24153168176957595593493253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32204224235943460791324337 24153168176957595593493253)
            ·
              refine ⟨4528719033179549173779985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24153168176957595593493253 4528719033179549173779985)
              ·
                refine ⟨3396539274884661880334989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528719033179549173779985 3396539274884661880334989)
                ·
                  refine ⟨1273702228081748205125621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3396539274884661880334989 1273702228081748205125621)
                  ·
                    refine ⟨119409583882663894230527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1273702228081748205125621 119409583882663894230527)
                    ·
                      rfl

theorem cell23_697648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_697648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697648 prefixEnd_697648 := by exact prefixLift 697648
  have htrace : WordTrace (prefixWord ++ tailWord_697648) baseStart_697648 baseEnd_697648 := by
    simpa [prefixWord, tailWord_697648, baseEnd_697648] using wordTrace_append hprefix tailTrace_697648
  have hstable : (prefixWord ++ tailWord_697648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697648).length < 2 ^ (prefixWord ++ tailWord_697648).sum := by decide
  have hdescent : baseEnd_697648 < baseStart_697648 := by decide
  rcases family_descends (prefixWord ++ tailWord_697648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697662 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_697662 : Nat := 118140960795 + 697662 * 2 ^ 59
def prefixEnd_697662 : Nat := 4983230072969 + 3 ^ 40 * 697662 * 2
def baseEnd_697662 : Nat := 358235940377154627916517

theorem tailTrace_697662 : CollatzResearch.WordTrace tailWord_697662 prefixEnd_697662 358235940377154627916517 := by
  unfold tailWord_697662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180727949812150003574905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16963882398998133352399493 3180727949812150003574905)
  ·
    refine ⟨2385545962359112502681179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3180727949812150003574905 2385545962359112502681179)
    ·
      refine ⟨3578318943538668754021769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385545962359112502681179 3578318943538668754021769)
      ·
        refine ⟨2683739207654001565516327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578318943538668754021769 2683739207654001565516327)
        ·
          refine ⟨4025608811481002348274491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683739207654001565516327 4025608811481002348274491)
          ·
            refine ⟨6038413217221503522411737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025608811481002348274491 6038413217221503522411737)
            ·
              refine ⟨4528809912916127641808803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038413217221503522411737 4528809912916127641808803)
              ·
                refine ⟨6793214869374191462713205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528809912916127641808803 6793214869374191462713205)
                ·
                  refine ⟨636863894003830449629363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6793214869374191462713205 636863894003830449629363)
                  ·
                    refine ⟨955295841005745674444045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 636863894003830449629363 955295841005745674444045)
                    ·
                      refine ⟨358235940377154627916517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955295841005745674444045 358235940377154627916517)
                      ·
                        rfl

theorem cell23_697662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_697662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697662 prefixEnd_697662 := by exact prefixLift 697662
  have htrace : WordTrace (prefixWord ++ tailWord_697662) baseStart_697662 baseEnd_697662 := by
    simpa [prefixWord, tailWord_697662, baseEnd_697662] using wordTrace_append hprefix tailTrace_697662
  have hstable : (prefixWord ++ tailWord_697662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697662).length < 2 ^ (prefixWord ++ tailWord_697662).sum := by decide
  have hdescent : baseEnd_697662 < baseStart_697662 := by decide
  rcases family_descends (prefixWord ++ tailWord_697662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697696 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 1, 1, 3]
def baseStart_697696 : Nat := 118140960795 + 697696 * 2 ^ 59
def prefixEnd_697696 : Nat := 4983230072969 + 3 ^ 40 * 697696 * 2
def baseEnd_697696 : Nat := 358253398719407494891361

theorem tailTrace_697696 : CollatzResearch.WordTrace tailWord_697696 prefixEnd_697696 358253398719407494891361 := by
  unfold tailWord_697696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723531840187011917668471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16964709120249349223557961 12723531840187011917668471)
  ·
    refine ⟨19085297760280517876502707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12723531840187011917668471 19085297760280517876502707)
    ·
      refine ⟨28627946640420776814754061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19085297760280517876502707 28627946640420776814754061)
      ·
        refine ⟨10735479990157791305532773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28627946640420776814754061 10735479990157791305532773)
        ·
          refine ⟨2012902498154585869787395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10735479990157791305532773 2012902498154585869787395)
          ·
            refine ⟨3019353747231878804681093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012902498154585869787395 3019353747231878804681093)
            ·
              refine ⟨566128827605977275877705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3019353747231878804681093 566128827605977275877705)
              ·
                refine ⟨424596620704482956908279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566128827605977275877705 424596620704482956908279)
                ·
                  refine ⟨636894931056724435362419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424596620704482956908279 636894931056724435362419)
                  ·
                    refine ⟨955342396585086653043629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 636894931056724435362419 955342396585086653043629)
                    ·
                      refine ⟨358253398719407494891361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955342396585086653043629 358253398719407494891361)
                      ·
                        rfl

theorem cell23_697696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_697696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697696 prefixEnd_697696 := by exact prefixLift 697696
  have htrace : WordTrace (prefixWord ++ tailWord_697696) baseStart_697696 baseEnd_697696 := by
    simpa [prefixWord, tailWord_697696, baseEnd_697696] using wordTrace_append hprefix tailTrace_697696
  have hstable : (prefixWord ++ tailWord_697696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697696).length < 2 ^ (prefixWord ++ tailWord_697696).sum := by decide
  have hdescent : baseEnd_697696 < baseStart_697696 := by decide
  rcases family_descends (prefixWord ++ tailWord_697696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697725 : List Nat := [1, 4, 1, 1, 2, 2, 5, 7]
def baseStart_697725 : Nat := 118140960795 + 697725 * 2 ^ 59
def prefixEnd_697725 : Nat := 4983230072969 + 3 ^ 40 * 697725 * 2
def baseEnd_697725 : Nat := 13269195913273625238101

theorem tailTrace_697725 : CollatzResearch.WordTrace tailWord_697725 prefixEnd_697725 13269195913273625238101 := by
  unfold tailWord_697725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25448121397268961788142629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16965414264845974525428419 25448121397268961788142629)
  ·
    refine ⟨4771522761987930335276743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25448121397268961788142629 4771522761987930335276743)
    ·
      refine ⟨7157284142981895502915115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771522761987930335276743 7157284142981895502915115)
      ·
        refine ⟨10735926214472843254372673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157284142981895502915115 10735926214472843254372673)
        ·
          refine ⟨8051944660854632440779505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10735926214472843254372673 8051944660854632440779505)
          ·
            refine ⟨6038958495640974330584629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8051944660854632440779505 6038958495640974330584629)
            ·
              refine ⟨566152358966341343492309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6038958495640974330584629 566152358966341343492309)
              ·
                refine ⟨13269195913273625238101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 566152358966341343492309 13269195913273625238101)
                ·
                  rfl

theorem cell23_697725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 7].length) (baseStart_697725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697725 prefixEnd_697725 := by exact prefixLift 697725
  have htrace : WordTrace (prefixWord ++ tailWord_697725) baseStart_697725 baseEnd_697725 := by
    simpa [prefixWord, tailWord_697725, baseEnd_697725] using wordTrace_append hprefix tailTrace_697725
  have hstable : (prefixWord ++ tailWord_697725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697725).length < 2 ^ (prefixWord ++ tailWord_697725).sum := by decide
  have hdescent : baseEnd_697725 < baseStart_697725 := by decide
  rcases family_descends (prefixWord ++ tailWord_697725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697736 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_697736 : Nat := 118140960795 + 697736 * 2 ^ 59
def prefixEnd_697736 : Nat := 4983230072969 + 3 ^ 40 * 697736 * 2
def baseEnd_697736 : Nat := 358273937945587338391177

theorem tailTrace_697736 : CollatzResearch.WordTrace tailWord_697736 prefixEnd_697736 358273937945587338391177 := by
  unfold tailWord_697736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724261300114555333396531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16965681733486073777862041 12724261300114555333396531)
  ·
    refine ⟨19086391950171833000094797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12724261300114555333396531 19086391950171833000094797)
    ·
      refine ⟨7157396981314437375035549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19086391950171833000094797 7157396981314437375035549)
      ·
        refine ⟨2684023867992914015638331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7157396981314437375035549 2684023867992914015638331)
        ·
          refine ⟨4026035801989371023457497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684023867992914015638331 4026035801989371023457497)
          ·
            refine ⟨3019526851492028267593123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4026035801989371023457497 3019526851492028267593123)
            ·
              refine ⟨4529290277238042401389685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019526851492028267593123 4529290277238042401389685)
              ·
                refine ⟨424620963491066475130283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4529290277238042401389685 424620963491066475130283)
                ·
                  refine ⟨636931445236599712695425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424620963491066475130283 636931445236599712695425)
                  ·
                    refine ⟨477698583927449784521569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636931445236599712695425 477698583927449784521569)
                    ·
                      refine ⟨358273937945587338391177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477698583927449784521569 358273937945587338391177)
                      ·
                        rfl

theorem cell23_697736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_697736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697736 prefixEnd_697736 := by exact prefixLift 697736
  have htrace : WordTrace (prefixWord ++ tailWord_697736) baseStart_697736 baseEnd_697736 := by
    simpa [prefixWord, tailWord_697736, baseEnd_697736] using wordTrace_append hprefix tailTrace_697736
  have hstable : (prefixWord ++ tailWord_697736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697736).length < 2 ^ (prefixWord ++ tailWord_697736).sum := by decide
  have hdescent : baseEnd_697736 < baseStart_697736 := by decide
  rcases family_descends (prefixWord ++ tailWord_697736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697792 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2]
def baseStart_697792 : Nat := 118140960795 + 697792 * 2 ^ 59
def prefixEnd_697792 : Nat := 4983230072969 + 3 ^ 40 * 697792 * 2
def baseEnd_697792 : Nat := 358302692862239119290919

theorem tailTrace_697792 : CollatzResearch.WordTrace tailWord_697792 prefixEnd_697792 358302692862239119290919 := by
  unfold tailWord_697792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725282544013116115415815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16967043392017488153887753 12725282544013116115415815)
  ·
    refine ⟨19087923816019674173123723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12725282544013116115415815 19087923816019674173123723)
    ·
      refine ⟨28631885724029511259685585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19087923816019674173123723 28631885724029511259685585)
      ·
        refine ⟨21473914293022133444764189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28631885724029511259685585 21473914293022133444764189)
        ·
          refine ⟨8052717859883300041786571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21473914293022133444764189 8052717859883300041786571)
          ·
            refine ⟨12079076789824950062679857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052717859883300041786571 12079076789824950062679857)
            ·
              refine ⟨9059307592368712547009893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12079076789824950062679857 9059307592368712547009893)
              ·
                refine ⟨1698620173569133602564355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9059307592368712547009893 1698620173569133602564355)
                ·
                  refine ⟨2547930260353700403846533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698620173569133602564355 2547930260353700403846533)
                  ·
                    refine ⟨477736923816318825721225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547930260353700403846533 477736923816318825721225)
                    ·
                      refine ⟨358302692862239119290919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477736923816318825721225 358302692862239119290919)
                      ·
                        rfl

theorem cell23_697792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_697792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697792 prefixEnd_697792 := by exact prefixLift 697792
  have htrace : WordTrace (prefixWord ++ tailWord_697792) baseStart_697792 baseEnd_697792 := by
    simpa [prefixWord, tailWord_697792, baseEnd_697792] using wordTrace_append hprefix tailTrace_697792
  have hstable : (prefixWord ++ tailWord_697792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697792).length < 2 ^ (prefixWord ++ tailWord_697792).sum := by decide
  have hdescent : baseEnd_697792 < baseStart_697792 := by decide
  rcases family_descends (prefixWord ++ tailWord_697792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697796 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_697796 : Nat := 118140960795 + 697796 * 2 ^ 59
def prefixEnd_697796 : Nat := 4983230072969 + 3 ^ 40 * 697796 * 2
def baseEnd_697796 : Nat := 358304746784857103640901

theorem tailTrace_697796 : CollatzResearch.WordTrace tailWord_697796 prefixEnd_697796 358304746784857103640901 := by
  unfold tailWord_697796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725355490005870456988621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16967140653341160609318161 12725355490005870456988621)
  ·
    refine ⟨4772008308752201421370733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12725355490005870456988621 4772008308752201421370733)
    ·
      refine ⟨1789503115782075533014025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4772008308752201421370733 1789503115782075533014025)
      ·
        refine ⟨1342127336836556649760519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1789503115782075533014025 1342127336836556649760519)
        ·
          refine ⟨2013191005254834974640779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342127336836556649760519 2013191005254834974640779)
          ·
            refine ⟨3019786507882252461961169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013191005254834974640779 3019786507882252461961169)
            ·
              refine ⟨2264839880911689346470877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019786507882252461961169 2264839880911689346470877)
              ·
                refine ⟨849314955341883504926579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264839880911689346470877 849314955341883504926579)
                ·
                  refine ⟨1273972433012825257389869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849314955341883504926579 1273972433012825257389869)
                  ·
                    refine ⟨477739662379809471521201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273972433012825257389869 477739662379809471521201)
                    ·
                      refine ⟨358304746784857103640901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477739662379809471521201 358304746784857103640901)
                      ·
                        rfl

theorem cell23_697796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_697796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697796 prefixEnd_697796 := by exact prefixLift 697796
  have htrace : WordTrace (prefixWord ++ tailWord_697796) baseStart_697796 baseEnd_697796 := by
    simpa [prefixWord, tailWord_697796, baseEnd_697796] using wordTrace_append hprefix tailTrace_697796
  have hstable : (prefixWord ++ tailWord_697796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697796).length < 2 ^ (prefixWord ++ tailWord_697796).sum := by decide
  have hdescent : baseEnd_697796 < baseStart_697796 := by decide
  rcases family_descends (prefixWord ++ tailWord_697796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697866 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_697866 : Nat := 118140960795 + 697866 * 2 ^ 59
def prefixEnd_697866 : Nat := 4983230072969 + 3 ^ 40 * 697866 * 2
def baseEnd_697866 : Nat := 39815632270074647751731

theorem tailTrace_697866 : CollatzResearch.WordTrace tailWord_697866 prefixEnd_697866 39815632270074647751731 := by
  unfold tailWord_697866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363316022439535717256363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16968842726505428579350301 6363316022439535717256363)
  ·
    refine ⟨9544974033659303575884545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6363316022439535717256363 9544974033659303575884545)
    ·
      refine ⟨7158730525244477681913409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9544974033659303575884545 7158730525244477681913409)
      ·
        refine ⟨5369047893933358261435057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7158730525244477681913409 5369047893933358261435057)
        ·
          refine ⟨4026785920450018696076293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5369047893933358261435057 4026785920450018696076293)
          ·
            refine ⟨755022360084378505514305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4026785920450018696076293 755022360084378505514305)
            ·
              refine ⟨566266770063283879135729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755022360084378505514305 566266770063283879135729)
              ·
                refine ⟨424700077547462909351797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566266770063283879135729 424700077547462909351797)
                ·
                  refine ⟨39815632270074647751731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424700077547462909351797 39815632270074647751731)
                  ·
                    rfl

theorem cell23_697866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_697866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697866 prefixEnd_697866 := by exact prefixLift 697866
  have htrace : WordTrace (prefixWord ++ tailWord_697866) baseStart_697866 baseEnd_697866 := by
    simpa [prefixWord, tailWord_697866, baseEnd_697866] using wordTrace_append hprefix tailTrace_697866
  have hstable : (prefixWord ++ tailWord_697866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697866).length < 2 ^ (prefixWord ++ tailWord_697866).sum := by decide
  have hdescent : baseEnd_697866 < baseStart_697866 := by decide
  rcases family_descends (prefixWord ++ tailWord_697866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697876 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_697876 : Nat := 118140960795 + 697876 * 2 ^ 59
def prefixEnd_697876 : Nat := 4983230072969 + 3 ^ 40 * 697876 * 2
def baseEnd_697876 : Nat := 358345825237216790640533

theorem tailTrace_697876 : CollatzResearch.WordTrace tailWord_697876 prefixEnd_697876 358345825237216790640533 := by
  unfold tailWord_697876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726814409860957288444741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16969085879814609717926321 12726814409860957288444741)
  ·
    refine ⟨2386277701848929491583389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12726814409860957288444741 2386277701848929491583389)
    ·
      refine ⟨894854138193348559343771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2386277701848929491583389 894854138193348559343771)
      ·
        refine ⟨1342281207290022839015657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894854138193348559343771 1342281207290022839015657)
        ·
          refine ⟨1006710905467517129261743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342281207290022839015657 1006710905467517129261743)
          ·
            refine ⟨1510066358201275693892615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006710905467517129261743 1510066358201275693892615)
            ·
              refine ⟨2265099537301913540838923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510066358201275693892615 2265099537301913540838923)
              ·
                refine ⟨3397649305952870311258385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265099537301913540838923 3397649305952870311258385)
                ·
                  refine ⟨2548236979464652733443789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397649305952870311258385 2548236979464652733443789)
                  ·
                    refine ⟨955588867299244775041421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548236979464652733443789 955588867299244775041421)
                    ·
                      refine ⟨358345825237216790640533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955588867299244775041421 358345825237216790640533)
                      ·
                        rfl

theorem cell23_697876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_697876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697876 prefixEnd_697876 := by exact prefixLift 697876
  have htrace : WordTrace (prefixWord ++ tailWord_697876) baseStart_697876 baseEnd_697876 := by
    simpa [prefixWord, tailWord_697876, baseEnd_697876] using wordTrace_append hprefix tailTrace_697876
  have hstable : (prefixWord ++ tailWord_697876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697876).length < 2 ^ (prefixWord ++ tailWord_697876).sum := by decide
  have hdescent : baseEnd_697876 < baseStart_697876 := by decide
  rcases family_descends (prefixWord ++ tailWord_697876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697896 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_697896 : Nat := 118140960795 + 697896 * 2 ^ 59
def prefixEnd_697896 : Nat := 4983230072969 + 3 ^ 40 * 697896 * 2
def baseEnd_697896 : Nat := 119452031616768904130147

theorem tailTrace_697896 : CollatzResearch.WordTrace tailWord_697896 prefixEnd_697896 119452031616768904130147 := by
  unfold tailWord_697896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727179139824728996308771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16969572186432971995078361 12727179139824728996308771)
  ·
    refine ⟨19090768709737093494463157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12727179139824728996308771 19090768709737093494463157)
    ·
      refine ⟨1789759566537852515105921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19090768709737093494463157 1789759566537852515105921)
      ·
        refine ⟨1342319674903389386329441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1789759566537852515105921 1342319674903389386329441)
        ·
          refine ⟨1006739756177542039747081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342319674903389386329441 1006739756177542039747081)
          ·
            refine ⟨755054817133156529810311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006739756177542039747081 755054817133156529810311)
            ·
              refine ⟨1132582225699734794715467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755054817133156529810311 1132582225699734794715467)
              ·
                refine ⟨1698873338549602192073201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132582225699734794715467 1698873338549602192073201)
                ·
                  refine ⟨1274155003912201644054901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698873338549602192073201 1274155003912201644054901)
                  ·
                    refine ⟨119452031616768904130147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1274155003912201644054901 119452031616768904130147)
                    ·
                      rfl

theorem cell23_697896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_697896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697896 prefixEnd_697896 := by exact prefixLift 697896
  have htrace : WordTrace (prefixWord ++ tailWord_697896) baseStart_697896 baseEnd_697896 := by
    simpa [prefixWord, tailWord_697896, baseEnd_697896] using wordTrace_append hprefix tailTrace_697896
  have hstable : (prefixWord ++ tailWord_697896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697896).length < 2 ^ (prefixWord ++ tailWord_697896).sum := by decide
  have hdescent : baseEnd_697896 < baseStart_697896 := by decide
  rcases family_descends (prefixWord ++ tailWord_697896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697905 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 8]
def baseStart_697905 : Nat := 118140960795 + 697905 * 2 ^ 59
def prefixEnd_697905 : Nat := 4983230072969 + 3 ^ 40 * 697905 * 2
def baseEnd_697905 : Nat := 39817857352910797464211

theorem tailTrace_697905 : CollatzResearch.WordTrace tailWord_697905 prefixEnd_697905 39817857352910797464211 := by
  unfold tailWord_697905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25454686536616852529695169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16969791024411235019796779 25454686536616852529695169)
  ·
    refine ⟨19091014902462639397271377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25454686536616852529695169 19091014902462639397271377)
    ·
      refine ⟨14318261176846979547953533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19091014902462639397271377 14318261176846979547953533)
      ·
        refine ⟨5369347941317617330482575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14318261176846979547953533 5369347941317617330482575)
        ·
          refine ⟨8054021911976425995723863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369347941317617330482575 8054021911976425995723863)
          ·
            refine ⟨12081032867964638993585795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054021911976425995723863 12081032867964638993585795)
            ·
              refine ⟨18121549301946958490378693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081032867964638993585795 18121549301946958490378693)
              ·
                refine ⟨3397790494115054716946005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18121549301946958490378693 3397790494115054716946005)
                ·
                  refine ⟨39817857352910797464211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3397790494115054716946005 39817857352910797464211)
                  ·
                    rfl

theorem cell23_697905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_697905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697905 prefixEnd_697905 := by exact prefixLift 697905
  have htrace : WordTrace (prefixWord ++ tailWord_697905) baseStart_697905 baseEnd_697905 := by
    simpa [prefixWord, tailWord_697905, baseEnd_697905] using wordTrace_append hprefix tailTrace_697905
  have hstable : (prefixWord ++ tailWord_697905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697905).length < 2 ^ (prefixWord ++ tailWord_697905).sum := by decide
  have hdescent : baseEnd_697905 < baseStart_697905 := by decide
  rcases family_descends (prefixWord ++ tailWord_697905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697925 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_697925 : Nat := 118140960795 + 697925 * 2 ^ 59
def prefixEnd_697925 : Nat := 4983230072969 + 3 ^ 40 * 697925 * 2
def baseEnd_697925 : Nat := 358370985789287098927807

theorem tailTrace_697925 : CollatzResearch.WordTrace tailWord_697925 prefixEnd_697925 358370985789287098927807 := by
  unfold tailWord_697925
  simp only [CollatzResearch.WordTrace]
  refine ⟨25455415996544395945423229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16970277331029597296948819 25455415996544395945423229)
  ·
    refine ⟨9545780998704148479533711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25455415996544395945423229 9545780998704148479533711)
    ·
      refine ⟨14318671498056222719300567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545780998704148479533711 14318671498056222719300567)
      ·
        refine ⟨21478007247084334078950851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318671498056222719300567 21478007247084334078950851)
        ·
          refine ⟨32217010870626501118426277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21478007247084334078950851 32217010870626501118426277)
          ·
            refine ⟨6040689538242468959704927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32217010870626501118426277 6040689538242468959704927)
            ·
              refine ⟨9061034307363703439557391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040689538242468959704927 9061034307363703439557391)
              ·
                refine ⟨13591551461045555159336087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9061034307363703439557391 13591551461045555159336087)
                ·
                  refine ⟨20387327191568332739004131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13591551461045555159336087 20387327191568332739004131)
                  ·
                    refine ⟨30580990787352499108506197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20387327191568332739004131 30580990787352499108506197)
                    ·
                      refine ⟨358370985789287098927807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30580990787352499108506197 358370985789287098927807)
                      ·
                        rfl

theorem cell23_697925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_697925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697925 prefixEnd_697925 := by exact prefixLift 697925
  have htrace : WordTrace (prefixWord ++ tailWord_697925) baseStart_697925 baseEnd_697925 := by
    simpa [prefixWord, tailWord_697925, baseEnd_697925] using wordTrace_append hprefix tailTrace_697925
  have hstable : (prefixWord ++ tailWord_697925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697925).length < 2 ^ (prefixWord ++ tailWord_697925).sum := by decide
  have hdescent : baseEnd_697925 < baseStart_697925 := by decide
  rcases family_descends (prefixWord ++ tailWord_697925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697945 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_697945 : Nat := 118140960795 + 697945 * 2 ^ 59
def prefixEnd_697945 : Nat := 4983230072969 + 3 ^ 40 * 697945 * 2
def baseEnd_697945 : Nat := 358381255402377020677715

theorem tailTrace_697945 : CollatzResearch.WordTrace tailWord_697945 prefixEnd_697945 358381255402377020677715 := by
  unfold tailWord_697945
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456145456471939361151289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16970763637647959574100859 25456145456471939361151289)
  ·
    refine ⟨19092109092353954520863467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25456145456471939361151289 19092109092353954520863467)
    ·
      refine ⟨28638163638530931781295201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19092109092353954520863467 28638163638530931781295201)
      ·
        refine ⟨21478622728898198835971401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28638163638530931781295201 21478622728898198835971401)
        ·
          refine ⟨16108967046673649126978551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21478622728898198835971401 16108967046673649126978551)
          ·
            refine ⟨24163450570010473690467827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16108967046673649126978551 24163450570010473690467827)
            ·
              refine ⟨36245175855015710535701741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24163450570010473690467827 36245175855015710535701741)
              ·
                refine ⟨13591940945630891450888153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36245175855015710535701741 13591940945630891450888153)
                ·
                  refine ⟨10193955709223168588166115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13591940945630891450888153 10193955709223168588166115)
                  ·
                    refine ⟨15290933563834752882249173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10193955709223168588166115 15290933563834752882249173)
                    ·
                      refine ⟨358381255402377020677715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15290933563834752882249173 358381255402377020677715)
                      ·
                        rfl

theorem cell23_697945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_697945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697945 prefixEnd_697945 := by exact prefixLift 697945
  have htrace : WordTrace (prefixWord ++ tailWord_697945) baseStart_697945 baseEnd_697945 := by
    simpa [prefixWord, tailWord_697945, baseEnd_697945] using wordTrace_append hprefix tailTrace_697945
  have hstable : (prefixWord ++ tailWord_697945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697945).length < 2 ^ (prefixWord ++ tailWord_697945).sum := by decide
  have hdescent : baseEnd_697945 < baseStart_697945 := by decide
  rcases family_descends (prefixWord ++ tailWord_697945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697959 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_697959 : Nat := 118140960795 + 697959 * 2 ^ 59
def prefixEnd_697959 : Nat := 4983230072969 + 3 ^ 40 * 697959 * 2
def baseEnd_697959 : Nat := 358388444131539965902651

theorem tailTrace_697959 : CollatzResearch.WordTrace tailWord_697959 prefixEnd_697959 358388444131539965902651 := by
  unfold tailWord_697959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456656078421219752160931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16971104052280813168107287 25456656078421219752160931)
  ·
    refine ⟨38184984117631829628241397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25456656078421219752160931 38184984117631829628241397)
    ·
      refine ⟨3579842261027984027647631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38184984117631829628241397 3579842261027984027647631)
      ·
        refine ⟨5369763391541976041471447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579842261027984027647631 5369763391541976041471447)
        ·
          refine ⟨8054645087312964062207171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369763391541976041471447 8054645087312964062207171)
          ·
            refine ⟨12081967630969446093310757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054645087312964062207171 12081967630969446093310757)
            ·
              refine ⟨2265368930806771142495767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12081967630969446093310757 2265368930806771142495767)
              ·
                refine ⟨3398053396210156713743651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265368930806771142495767 3398053396210156713743651)
                ·
                  refine ⟨5097080094315235070615477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398053396210156713743651 5097080094315235070615477)
                  ·
                    refine ⟨477851258842053287870201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5097080094315235070615477 477851258842053287870201)
                    ·
                      refine ⟨358388444131539965902651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477851258842053287870201 358388444131539965902651)
                      ·
                        rfl

theorem cell23_697959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_697959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_697959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_697959 prefixEnd_697959 := by exact prefixLift 697959
  have htrace : WordTrace (prefixWord ++ tailWord_697959) baseStart_697959 baseEnd_697959 := by
    simpa [prefixWord, tailWord_697959, baseEnd_697959] using wordTrace_append hprefix tailTrace_697959
  have hstable : (prefixWord ++ tailWord_697959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697959).length < 2 ^ (prefixWord ++ tailWord_697959).sum := by decide
  have hdescent : baseEnd_697959 < baseStart_697959 := by decide
  rcases family_descends (prefixWord ++ tailWord_697959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698009 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_698009 : Nat := 118140960795 + 698009 * 2 ^ 59
def prefixEnd_698009 : Nat := 4983230072969 + 3 ^ 40 * 698009 * 2
def baseEnd_698009 : Nat := 358414118164264770277421

theorem tailTrace_698009 : CollatzResearch.WordTrace tailWord_698009 prefixEnd_698009 358414118164264770277421 := by
  unfold tailWord_698009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458479728240078291481081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16972319818826718860987387 25458479728240078291481081)
  ·
    refine ⟨19093859796180058718610811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25458479728240078291481081 19093859796180058718610811)
    ·
      refine ⟨28640789694270088077916217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19093859796180058718610811 28640789694270088077916217)
      ·
        refine ⟨21480592270702566058437163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28640789694270088077916217 21480592270702566058437163)
        ·
          refine ⟨32220888406053849087655745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21480592270702566058437163 32220888406053849087655745)
          ·
            refine ⟨24165666304540386815741809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32220888406053849087655745 24165666304540386815741809)
            ·
              refine ⟨18124249728405290111806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24165666304540386815741809 18124249728405290111806357)
              ·
                refine ⟨849574206018997973990923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18124249728405290111806357 849574206018997973990923)
                ·
                  refine ⟨1274361309028496960986385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849574206018997973990923 1274361309028496960986385)
                  ·
                    refine ⟨955770981771372720739789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274361309028496960986385 955770981771372720739789)
                    ·
                      refine ⟨358414118164264770277421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955770981771372720739789 358414118164264770277421)
                      ·
                        rfl

theorem cell23_698009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_698009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698009 prefixEnd_698009 := by exact prefixLift 698009
  have htrace : WordTrace (prefixWord ++ tailWord_698009) baseStart_698009 baseEnd_698009 := by
    simpa [prefixWord, tailWord_698009, baseEnd_698009] using wordTrace_append hprefix tailTrace_698009
  have hstable : (prefixWord ++ tailWord_698009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698009).length < 2 ^ (prefixWord ++ tailWord_698009).sum := by decide
  have hdescent : baseEnd_698009 < baseStart_698009 := by decide
  rcases family_descends (prefixWord ++ tailWord_698009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698042 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_698042 : Nat := 118140960795 + 698042 * 2 ^ 59
def prefixEnd_698042 : Nat := 4983230072969 + 3 ^ 40 * 698042 * 2
def baseEnd_698042 : Nat := 119477021008621047054923

theorem tailTrace_698042 : CollatzResearch.WordTrace tailWord_698042 prefixEnd_698042 119477021008621047054923 := by
  unfold tailWord_698042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364920834280131231858095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16973122224747016618288253 6364920834280131231858095)
  ·
    refine ⟨9547381251420196847787143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6364920834280131231858095 9547381251420196847787143)
    ·
      refine ⟨14321071877130295271680715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9547381251420196847787143 14321071877130295271680715)
      ·
        refine ⟨21481607815695442907521073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321071877130295271680715 21481607815695442907521073)
        ·
          refine ⟨16111205861771582180640805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21481607815695442907521073 16111205861771582180640805)
          ·
            refine ⟨3020851099082171658870151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16111205861771582180640805 3020851099082171658870151)
            ·
              refine ⟨4531276648623257488305227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020851099082171658870151 4531276648623257488305227)
              ·
                refine ⟨6796914972934886232457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531276648623257488305227 6796914972934886232457841)
                ·
                  refine ⟨5097686229701164674343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796914972934886232457841 5097686229701164674343381)
                  ·
                    refine ⟨119477021008621047054923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5097686229701164674343381 119477021008621047054923)
                    ·
                      rfl

theorem cell23_698042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_698042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698042 prefixEnd_698042 := by exact prefixLift 698042
  have htrace : WordTrace (prefixWord ++ tailWord_698042) baseStart_698042 baseEnd_698042 := by
    simpa [prefixWord, tailWord_698042, baseEnd_698042] using wordTrace_append hprefix tailTrace_698042
  have hstable : (prefixWord ++ tailWord_698042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698042).length < 2 ^ (prefixWord ++ tailWord_698042).sum := by decide
  have hdescent : baseEnd_698042 < baseStart_698042 := by decide
  rcases family_descends (prefixWord ++ tailWord_698042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698050 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_698050 : Nat := 118140960795 + 698050 * 2 ^ 59
def prefixEnd_698050 : Nat := 4983230072969 + 3 ^ 40 * 698050 * 2
def baseEnd_698050 : Nat := 119478390290366369954911

theorem tailTrace_698050 : CollatzResearch.WordTrace tailWord_698050 prefixEnd_698050 119478390290366369954911 := by
  unfold tailWord_698050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364993780272885573430901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16973316747394361529149069 6364993780272885573430901)
  ·
    refine ⟨596718166900583022509147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6364993780272885573430901 596718166900583022509147)
    ·
      refine ⟨895077250350874533763721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596718166900583022509147 895077250350874533763721)
      ·
        refine ⟨671307937763155900322791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895077250350874533763721 671307937763155900322791)
        ·
          refine ⟨1006961906644733850484187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671307937763155900322791 1006961906644733850484187)
          ·
            refine ⟨1510442859967100775726281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006961906644733850484187 1510442859967100775726281)
            ·
              refine ⟨1132832144975325581794711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510442859967100775726281 1132832144975325581794711)
              ·
                refine ⟨1699248217462988372692067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132832144975325581794711 1699248217462988372692067)
                ·
                  refine ⟨2548872326194482559038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699248217462988372692067 2548872326194482559038101)
                  ·
                    refine ⟨119478390290366369954911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2548872326194482559038101 119478390290366369954911)
                    ·
                      rfl

theorem cell23_698050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_698050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698050 prefixEnd_698050 := by exact prefixLift 698050
  have htrace : WordTrace (prefixWord ++ tailWord_698050) baseStart_698050 baseEnd_698050 := by
    simpa [prefixWord, tailWord_698050, baseEnd_698050] using wordTrace_append hprefix tailTrace_698050
  have hstable : (prefixWord ++ tailWord_698050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698050).length < 2 ^ (prefixWord ++ tailWord_698050).sum := by decide
  have hdescent : baseEnd_698050 < baseStart_698050 := by decide
  rcases family_descends (prefixWord ++ tailWord_698050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698056 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_698056 : Nat := 118140960795 + 698056 * 2 ^ 59
def prefixEnd_698056 : Nat := 4983230072969 + 3 ^ 40 * 698056 * 2
def baseEnd_698056 : Nat := 358438251755026086389705

theorem tailTrace_698056 : CollatzResearch.WordTrace tailWord_698056 prefixEnd_698056 358438251755026086389705 := by
  unfold tailWord_698056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730096979534902659221011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16973462639379870212294681 12730096979534902659221011)
  ·
    refine ⟨19095145469302353988831517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730096979534902659221011 19095145469302353988831517)
    ·
      refine ⟨7160679550988382745811819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19095145469302353988831517 7160679550988382745811819)
      ·
        refine ⟨10741019326482574118717729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7160679550988382745811819 10741019326482574118717729)
        ·
          refine ⟨8055764494861930589038297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10741019326482574118717729 8055764494861930589038297)
          ·
            refine ⟨6041823371146447941778723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055764494861930589038297 6041823371146447941778723)
            ·
              refine ⟨9062735056719671912668085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041823371146447941778723 9062735056719671912668085)
              ·
                refine ⟨849631411567469241812633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9062735056719671912668085 849631411567469241812633)
                ·
                  refine ⟨637223558675601931359475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849631411567469241812633 637223558675601931359475)
                  ·
                    refine ⟨955835338013402897039213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 637223558675601931359475 955835338013402897039213)
                    ·
                      refine ⟨358438251755026086389705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955835338013402897039213 358438251755026086389705)
                      ·
                        rfl

theorem cell23_698056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_698056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698056 prefixEnd_698056 := by exact prefixLift 698056
  have htrace : WordTrace (prefixWord ++ tailWord_698056) baseStart_698056 baseEnd_698056 := by
    simpa [prefixWord, tailWord_698056, baseEnd_698056] using wordTrace_append hprefix tailTrace_698056
  have hstable : (prefixWord ++ tailWord_698056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698056).length < 2 ^ (prefixWord ++ tailWord_698056).sum := by decide
  have hdescent : baseEnd_698056 < baseStart_698056 := by decide
  rcases family_descends (prefixWord ++ tailWord_698056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698072 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_698072 : Nat := 118140960795 + 698072 * 2 ^ 59
def prefixEnd_698072 : Nat := 4983230072969 + 3 ^ 40 * 698072 * 2
def baseEnd_698072 : Nat := 119482155815166007929877

theorem tailTrace_698072 : CollatzResearch.WordTrace tailWord_698072 prefixEnd_698072 119482155815166007929877 := by
  unfold tailWord_698072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730388763505920025512235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16973851684674560034016313 12730388763505920025512235)
  ·
    refine ⟨19095583145258880038268353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730388763505920025512235 19095583145258880038268353)
    ·
      refine ⟨14321687358944160028701265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19095583145258880038268353 14321687358944160028701265)
      ·
        refine ⟨10741265519208120021525949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14321687358944160028701265 10741265519208120021525949)
        ·
          refine ⟨4027974569703045008072231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10741265519208120021525949 4027974569703045008072231)
          ·
            refine ⟨6041961854554567512108347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027974569703045008072231 6041961854554567512108347)
            ·
              refine ⟨9062942781831851268162521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041961854554567512108347 9062942781831851268162521)
              ·
                refine ⟨6797207086373888451121891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9062942781831851268162521 6797207086373888451121891)
                ·
                  refine ⟨10195810629560832676682837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797207086373888451121891 10195810629560832676682837)
                  ·
                    refine ⟨119482155815166007929877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10195810629560832676682837 119482155815166007929877)
                    ·
                      rfl

theorem cell23_698072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_698072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698072 prefixEnd_698072 := by exact prefixLift 698072
  have htrace : WordTrace (prefixWord ++ tailWord_698072) baseStart_698072 baseEnd_698072 := by
    simpa [prefixWord, tailWord_698072, baseEnd_698072] using wordTrace_append hprefix tailTrace_698072
  have hstable : (prefixWord ++ tailWord_698072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698072).length < 2 ^ (prefixWord ++ tailWord_698072).sum := by decide
  have hdescent : baseEnd_698072 < baseStart_698072 := by decide
  rcases family_descends (prefixWord ++ tailWord_698072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698077 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_698077 : Nat := 118140960795 + 698077 * 2 ^ 59
def prefixEnd_698077 : Nat := 4983230072969 + 3 ^ 40 * 698077 * 2
def baseEnd_698077 : Nat := 358449034848770504227109

theorem tailTrace_698077 : CollatzResearch.WordTrace tailWord_698077 prefixEnd_698077 358449034848770504227109 := by
  unfold tailWord_698077
  simp only [CollatzResearch.WordTrace]
  refine ⟨25460959891993725904956485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16973973261329150603304323 25460959891993725904956485)
  ·
    refine ⟨4773929979748823607179341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25460959891993725904956485 4773929979748823607179341)
    ·
      refine ⟨1790223742405808852692253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4773929979748823607179341 1790223742405808852692253)
      ·
        refine ⟨671333903402178319759595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1790223742405808852692253 671333903402178319759595)
        ·
          refine ⟨1007000855103267479639393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671333903402178319759595 1007000855103267479639393)
          ·
            refine ⟨755250641327450609729545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007000855103267479639393 755250641327450609729545)
            ·
              refine ⟨566437980995587957297159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755250641327450609729545 566437980995587957297159)
              ·
                refine ⟨849656971493381935945739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566437980995587957297159 849656971493381935945739)
                ·
                  refine ⟨1274485457240072903918609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849656971493381935945739 1274485457240072903918609)
                  ·
                    refine ⟨955864092930054677938957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274485457240072903918609 955864092930054677938957)
                    ·
                      refine ⟨358449034848770504227109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 955864092930054677938957 358449034848770504227109)
                      ·
                        rfl

theorem cell23_698077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_698077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698077 prefixEnd_698077 := by exact prefixLift 698077
  have htrace : WordTrace (prefixWord ++ tailWord_698077) baseStart_698077 baseEnd_698077 := by
    simpa [prefixWord, tailWord_698077, baseEnd_698077] using wordTrace_append hprefix tailTrace_698077
  have hstable : (prefixWord ++ tailWord_698077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698077).length < 2 ^ (prefixWord ++ tailWord_698077).sum := by decide
  have hdescent : baseEnd_698077 < baseStart_698077 := by decide
  rcases family_descends (prefixWord ++ tailWord_698077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698113 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_698113 : Nat := 118140960795 + 698113 * 2 ^ 59
def prefixEnd_698113 : Nat := 4983230072969 + 3 ^ 40 * 698113 * 2
def baseEnd_698113 : Nat := 358467520152332363376943

theorem tailTrace_698113 : CollatzResearch.WordTrace tailWord_698113 prefixEnd_698113 358467520152332363376943 := by
  unfold tailWord_698113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25462272919863304053266993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16974848613242202702177995 25462272919863304053266993)
  ·
    refine ⟨19096704689897478039950245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25462272919863304053266993 19096704689897478039950245)
    ·
      refine ⟨3580632129355777132490671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19096704689897478039950245 3580632129355777132490671)
      ·
        refine ⟨5370948194033665698736007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580632129355777132490671 5370948194033665698736007)
        ·
          refine ⟨8056422291050498548104011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370948194033665698736007 8056422291050498548104011)
          ·
            refine ⟨12084633436575747822156017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056422291050498548104011 12084633436575747822156017)
            ·
              refine ⟨9063475077431810866617013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12084633436575747822156017 9063475077431810866617013)
              ·
                refine ⟨849700788509232268745345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9063475077431810866617013 849700788509232268745345)
                ·
                  refine ⟨637275591381924201559009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849700788509232268745345 637275591381924201559009)
                  ·
                    refine ⟨477956693536443151169257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637275591381924201559009 477956693536443151169257)
                    ·
                      refine ⟨358467520152332363376943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477956693536443151169257 358467520152332363376943)
                      ·
                        rfl

theorem cell23_698113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_698113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698113 prefixEnd_698113 := by exact prefixLift 698113
  have htrace : WordTrace (prefixWord ++ tailWord_698113) baseStart_698113 baseEnd_698113 := by
    simpa [prefixWord, tailWord_698113, baseEnd_698113] using wordTrace_append hprefix tailTrace_698113
  have hstable : (prefixWord ++ tailWord_698113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698113).length < 2 ^ (prefixWord ++ tailWord_698113).sum := by decide
  have hdescent : baseEnd_698113 < baseStart_698113 := by decide
  rcases family_descends (prefixWord ++ tailWord_698113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698125 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_698125 : Nat := 118140960795 + 698125 * 2 ^ 59
def prefixEnd_698125 : Nat := 4983230072969 + 3 ^ 40 * 698125 * 2
def baseEnd_698125 : Nat := 358473681920186316426889

theorem tailTrace_698125 : CollatzResearch.WordTrace tailWord_698125 prefixEnd_698125 358473681920186316426889 := by
  unfold tailWord_698125
  simp only [CollatzResearch.WordTrace]
  refine ⟨25462710595819830102703829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16975140397213220068469219 25462710595819830102703829)
  ·
    refine ⟨596782279589527268032121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25462710595819830102703829 596782279589527268032121)
    ·
      refine ⟨447586709692145451024091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 596782279589527268032121 447586709692145451024091)
      ·
        refine ⟨671380064538218176536137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447586709692145451024091 671380064538218176536137)
        ·
          refine ⟨503535048403663632402103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671380064538218176536137 503535048403663632402103)
          ·
            refine ⟨755302572605495448603155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503535048403663632402103 755302572605495448603155)
            ·
              refine ⟨1132953858908243172904733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755302572605495448603155 1132953858908243172904733)
              ·
                refine ⟨424857697090591189839275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132953858908243172904733 424857697090591189839275)
                ·
                  refine ⟨637286545635886784758913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424857697090591189839275 637286545635886784758913)
                  ·
                    refine ⟨477964909226915088569185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637286545635886784758913 477964909226915088569185)
                    ·
                      refine ⟨358473681920186316426889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477964909226915088569185 358473681920186316426889)
                      ·
                        rfl

theorem cell23_698125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_698125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698125 prefixEnd_698125 := by exact prefixLift 698125
  have htrace : WordTrace (prefixWord ++ tailWord_698125) baseStart_698125 baseEnd_698125 := by
    simpa [prefixWord, tailWord_698125, baseEnd_698125] using wordTrace_append hprefix tailTrace_698125
  have hstable : (prefixWord ++ tailWord_698125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698125).length < 2 ^ (prefixWord ++ tailWord_698125).sum := by decide
  have hdescent : baseEnd_698125 < baseStart_698125 := by decide
  rcases family_descends (prefixWord ++ tailWord_698125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698130 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_698130 : Nat := 118140960795 + 698130 * 2 ^ 59
def prefixEnd_698130 : Nat := 4983230072969 + 3 ^ 40 * 698130 * 2
def baseEnd_698130 : Nat := 358476249323458796864365

theorem tailTrace_698130 : CollatzResearch.WordTrace tailWord_698130 prefixEnd_698130 358476249323458796864365 := by
  unfold tailWord_698130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365723240200428989158961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16975261973867810637757229 6365723240200428989158961)
  ·
    refine ⟨4774292430150321741869221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6365723240200428989158961 4774292430150321741869221)
    ·
      refine ⟨895179830653185326600479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4774292430150321741869221 895179830653185326600479)
      ·
        refine ⟨1342769745979777989900719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895179830653185326600479 1342769745979777989900719)
        ·
          refine ⟨2014154618969666984851079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342769745979777989900719 2014154618969666984851079)
          ·
            refine ⟨3021231928454500477276619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014154618969666984851079 3021231928454500477276619)
            ·
              refine ⟨4531847892681750715914929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021231928454500477276619 4531847892681750715914929)
              ·
                refine ⟨3398885919511313036936197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531847892681750715914929 3398885919511313036936197)
                ·
                  refine ⟨637291109908371194425537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3398885919511313036936197 637291109908371194425537)
                  ·
                    refine ⟨477968332431278395819153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637291109908371194425537 477968332431278395819153)
                    ·
                      refine ⟨358476249323458796864365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477968332431278395819153 358476249323458796864365)
                      ·
                        rfl

theorem cell23_698130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_698130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698130 prefixEnd_698130 := by exact prefixLift 698130
  have htrace : WordTrace (prefixWord ++ tailWord_698130) baseStart_698130 baseEnd_698130 := by
    simpa [prefixWord, tailWord_698130, baseEnd_698130] using wordTrace_append hprefix tailTrace_698130
  have hstable : (prefixWord ++ tailWord_698130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698130).length < 2 ^ (prefixWord ++ tailWord_698130).sum := by decide
  have hdescent : baseEnd_698130 < baseStart_698130 := by decide
  rcases family_descends (prefixWord ++ tailWord_698130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
