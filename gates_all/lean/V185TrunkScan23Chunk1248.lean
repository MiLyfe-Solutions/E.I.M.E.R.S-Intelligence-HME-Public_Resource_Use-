import V185TrunkScan23Chunk1247

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7392651 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 3, 2, 2]
def baseStart_7392651 : Nat := 118140960795 + 7392651 * 2 ^ 59
def prefixEnd_7392651 : Nat := 4983230072969 + 3 ^ 40 * 7392651 * 2
def baseEnd_7392651 : Nat := 3795983273941260952664323

theorem tailTrace_7392651 : CollatzResearch.WordTrace tailWord_7392651 prefixEnd_7392651 3795983273941260952664323 := by
  unfold tailWord_7392651
  simp only [CollatzResearch.WordTrace]
  refine ⟨269632133140695466118033807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179754755427130310745355871 269632133140695466118033807)
  ·
    refine ⟨404448199711043199177050711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269632133140695466118033807 404448199711043199177050711)
    ·
      refine ⟨606672299566564798765576067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404448199711043199177050711 606672299566564798765576067)
      ·
        refine ⟨910008449349847198148364101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606672299566564798765576067 910008449349847198148364101)
        ·
          refine ⟨170626584253096349652818269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910008449349847198148364101 170626584253096349652818269)
          ·
            refine ⟨63984969094911131119806851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170626584253096349652818269 63984969094911131119806851)
            ·
              refine ⟨95977453642366696679710277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63984969094911131119806851 95977453642366696679710277)
              ·
                refine ⟨17995772557943755627445677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95977453642366696679710277 17995772557943755627445677)
                ·
                  refine ⟨6748414709228908360292129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17995772557943755627445677 6748414709228908360292129)
                  ·
                    refine ⟨5061311031921681270219097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748414709228908360292129 5061311031921681270219097)
                    ·
                      refine ⟨3795983273941260952664323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061311031921681270219097 3795983273941260952664323)
                      ·
                        rfl

theorem cell23_7392651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2, 2].length) (baseStart_7392651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392651 prefixEnd_7392651 := by exact prefixLift 7392651
  have htrace : WordTrace (prefixWord ++ tailWord_7392651) baseStart_7392651 baseEnd_7392651 := by
    simpa [prefixWord, tailWord_7392651, baseEnd_7392651] using wordTrace_append hprefix tailTrace_7392651
  have hstable : (prefixWord ++ tailWord_7392651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392651).length < 2 ^ (prefixWord ++ tailWord_7392651).sum := by decide
  have hdescent : baseEnd_7392651 < baseStart_7392651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3]
def baseStart_7392667 : Nat := 118140960795 + 7392667 * 2 ^ 59
def prefixEnd_7392667 : Nat := 4983230072969 + 3 ^ 40 * 7392667 * 2
def baseEnd_7392667 : Nat := 3795991489631732890064249

theorem tailTrace_7392667 : CollatzResearch.WordTrace tailWord_7392667 prefixEnd_7392667 3795991489631732890064249 := by
  unfold tailWord_7392667
  simp only [CollatzResearch.WordTrace]
  refine ⟨269632716708637500850616255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179755144472425000567077503 269632716708637500850616255)
  ·
    refine ⟨404449075062956251275924383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269632716708637500850616255 404449075062956251275924383)
    ·
      refine ⟨606673612594434376913886575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404449075062956251275924383 606673612594434376913886575)
      ·
        refine ⟨910010418891651565370829863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606673612594434376913886575 910010418891651565370829863)
        ·
          refine ⟨1365015628337477348056244795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910010418891651565370829863 1365015628337477348056244795)
          ·
            refine ⟨2047523442506216022084367193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365015628337477348056244795 2047523442506216022084367193)
            ·
              refine ⟨1535642581879662016563275395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047523442506216022084367193 1535642581879662016563275395)
              ·
                refine ⟨2303463872819493024844913093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535642581879662016563275395 2303463872819493024844913093)
                ·
                  refine ⟨431899476153654942158421205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303463872819493024844913093 431899476153654942158421205)
                  ·
                    refine ⟨10122643972351287706837997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 431899476153654942158421205 10122643972351287706837997)
                    ·
                      refine ⟨3795991489631732890064249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122643972351287706837997 3795991489631732890064249)
                      ·
                        rfl

theorem cell23_7392667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].length) (baseStart_7392667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392667 prefixEnd_7392667 := by exact prefixLift 7392667
  have htrace : WordTrace (prefixWord ++ tailWord_7392667) baseStart_7392667 baseEnd_7392667 := by
    simpa [prefixWord, tailWord_7392667, baseEnd_7392667] using wordTrace_append hprefix tailTrace_7392667
  have hstable : (prefixWord ++ tailWord_7392667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392667).length < 2 ^ (prefixWord ++ tailWord_7392667).sum := by decide
  have hdescent : baseEnd_7392667 < baseStart_7392667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392671 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7392671 : Nat := 118140960795 + 7392671 * 2 ^ 59
def prefixEnd_7392671 : Nat := 4983230072969 + 3 ^ 40 * 7392671 * 2
def baseEnd_7392671 : Nat := 3795993543554350874414231

theorem tailTrace_7392671 : CollatzResearch.WordTrace tailWord_7392671 prefixEnd_7392671 3795993543554350874414231 := by
  unfold tailWord_7392671
  simp only [CollatzResearch.WordTrace]
  refine ⟨269632862600623009533761867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179755241733748673022507911 269632862600623009533761867)
  ·
    refine ⟨404449293900934514300642801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269632862600623009533761867 404449293900934514300642801)
    ·
      refine ⟨303336970425700885725482101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404449293900934514300642801 303336970425700885725482101)
      ·
        refine ⟨28437840977409458036763947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303336970425700885725482101 28437840977409458036763947)
        ·
          refine ⟨42656761466114187055145921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28437840977409458036763947 42656761466114187055145921)
          ·
            refine ⟨31992571099585640291359441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42656761466114187055145921 31992571099585640291359441)
            ·
              refine ⟨23994428324689230218519581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31992571099585640291359441 23994428324689230218519581)
              ·
                refine ⟨8997910621758461331944843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23994428324689230218519581 8997910621758461331944843)
                ·
                  refine ⟨13496865932637691997917265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997910621758461331944843 13496865932637691997917265)
                  ·
                    refine ⟨10122649449478268998437949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13496865932637691997917265 10122649449478268998437949)
                    ·
                      refine ⟨3795993543554350874414231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122649449478268998437949 3795993543554350874414231)
                      ·
                        rfl

theorem cell23_7392671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7392671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392671 prefixEnd_7392671 := by exact prefixLift 7392671
  have htrace : WordTrace (prefixWord ++ tailWord_7392671) baseStart_7392671 baseEnd_7392671 := by
    simpa [prefixWord, tailWord_7392671, baseEnd_7392671] using wordTrace_append hprefix tailTrace_7392671
  have hstable : (prefixWord ++ tailWord_7392671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392671).length < 2 ^ (prefixWord ++ tailWord_7392671).sum := by decide
  have hdescent : baseEnd_7392671 < baseStart_7392671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392674 : List Nat := [3, 3, 1, 2, 1, 4, 9]
def baseStart_7392674 : Nat := 118140960795 + 7392674 * 2 ^ 59
def prefixEnd_7392674 : Nat := 4983230072969 + 3 ^ 40 * 7392674 * 2
def baseEnd_7392674 : Nat := 46864136839460671144157

theorem tailTrace_7392674 : CollatzResearch.WordTrace tailWord_7392674 prefixEnd_7392674 46864136839460671144157 := by
  unfold tailWord_7392674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67408243004903035261530269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179755314679741427364080717 67408243004903035261530269)
  ·
    refine ⟨25278091126838638223073851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67408243004903035261530269 25278091126838638223073851)
    ·
      refine ⟨37917136690257957334610777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25278091126838638223073851 37917136690257957334610777)
      ·
        refine ⟨28437852517693468000958083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37917136690257957334610777 28437852517693468000958083)
        ·
          refine ⟨42656778776540202001437125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28437852517693468000958083 42656778776540202001437125)
          ·
            refine ⟨7998146020601287875269461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42656778776540202001437125 7998146020601287875269461)
            ·
              refine ⟨46864136839460671144157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7998146020601287875269461 46864136839460671144157)
              ·
                rfl

theorem cell23_7392674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 9].length) (baseStart_7392674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392674 prefixEnd_7392674 := by exact prefixLift 7392674
  have htrace : WordTrace (prefixWord ++ tailWord_7392674) baseStart_7392674 baseEnd_7392674 := by
    simpa [prefixWord, tailWord_7392674, baseEnd_7392674] using wordTrace_append hprefix tailTrace_7392674
  have hstable : (prefixWord ++ tailWord_7392674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392674).length < 2 ^ (prefixWord ++ tailWord_7392674).sum := by decide
  have hdescent : baseEnd_7392674 < baseStart_7392674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392685 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7392685 : Nat := 118140960795 + 7392685 * 2 ^ 59
def prefixEnd_7392685 : Nat := 4983230072969 + 3 ^ 40 * 7392685 * 2
def baseEnd_7392685 : Nat := 3796000732283513819639167

theorem tailTrace_7392685 : CollatzResearch.WordTrace tailWord_7392685 prefixEnd_7392685 3796000732283513819639167 := by
  unfold tailWord_7392685
  simp only [CollatzResearch.WordTrace]
  refine ⟨269633373222572289924771509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179755582148381526616514339 269633373222572289924771509)
  ·
    refine ⟨25278128739616152180447329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269633373222572289924771509 25278128739616152180447329)
    ·
      refine ⟨18958596554712114135335497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25278128739616152180447329 18958596554712114135335497)
      ·
        refine ⟨14218947416034085601501623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18958596554712114135335497 14218947416034085601501623)
        ·
          refine ⟨21328421124051128402252435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14218947416034085601501623 21328421124051128402252435)
          ·
            refine ⟨31992631686076692603378653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21328421124051128402252435 31992631686076692603378653)
            ·
              refine ⟨11997236882278759726266995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31992631686076692603378653 11997236882278759726266995)
              ·
                refine ⟨17995855323418139589400493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997236882278759726266995 17995855323418139589400493)
                ·
                  refine ⟨6748445746281802346025185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17995855323418139589400493 6748445746281802346025185)
                  ·
                    refine ⟨5061334309711351759518889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748445746281802346025185 5061334309711351759518889)
                    ·
                      refine ⟨3796000732283513819639167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061334309711351759518889 3796000732283513819639167)
                      ·
                        rfl

theorem cell23_7392685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7392685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392685 prefixEnd_7392685 := by exact prefixLift 7392685
  have htrace : WordTrace (prefixWord ++ tailWord_7392685) baseStart_7392685 baseEnd_7392685 := by
    simpa [prefixWord, tailWord_7392685, baseEnd_7392685] using wordTrace_append hprefix tailTrace_7392685
  have hstable : (prefixWord ++ tailWord_7392685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392685).length < 2 ^ (prefixWord ++ tailWord_7392685).sum := by decide
  have hdescent : baseEnd_7392685 < baseStart_7392685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392711 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_7392711 : Nat := 118140960795 + 7392711 * 2 ^ 59
def prefixEnd_7392711 : Nat := 4983230072969 + 3 ^ 40 * 7392711 * 2
def baseEnd_7392711 : Nat := 3796014082780530717914047

theorem tailTrace_7392711 : CollatzResearch.WordTrace tailWord_7392711 prefixEnd_7392711 3796014082780530717914047 := by
  unfold tailWord_7392711
  simp only [CollatzResearch.WordTrace]
  refine ⟨269634321520478096365217987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179756214346985397576811991 269634321520478096365217987)
  ·
    refine ⟨404451482280717144547826981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269634321520478096365217987 404451482280717144547826981)
    ·
      refine ⟨75834652927634464602717559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404451482280717144547826981 75834652927634464602717559)
      ·
        refine ⟨113751979391451696904076339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75834652927634464602717559 113751979391451696904076339)
        ·
          refine ⟨170627969087177545356114509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113751979391451696904076339 170627969087177545356114509)
          ·
            refine ⟨63985488407691579508542941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170627969087177545356114509 63985488407691579508542941)
            ·
              refine ⟨23994558152884342315703603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63985488407691579508542941 23994558152884342315703603)
              ·
                refine ⟨35991837229326513473555405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23994558152884342315703603 35991837229326513473555405)
                ·
                  refine ⟨13496938960997442552583277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35991837229326513473555405 13496938960997442552583277)
                  ·
                    refine ⟨5061352110374040957218729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13496938960997442552583277 5061352110374040957218729)
                    ·
                      refine ⟨3796014082780530717914047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061352110374040957218729 3796014082780530717914047)
                      ·
                        rfl

theorem cell23_7392711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_7392711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392711 prefixEnd_7392711 := by exact prefixLift 7392711
  have htrace : WordTrace (prefixWord ++ tailWord_7392711) baseStart_7392711 baseEnd_7392711 := by
    simpa [prefixWord, tailWord_7392711, baseEnd_7392711] using wordTrace_append hprefix tailTrace_7392711
  have hstable : (prefixWord ++ tailWord_7392711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392711).length < 2 ^ (prefixWord ++ tailWord_7392711).sum := by decide
  have hdescent : baseEnd_7392711 < baseStart_7392711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392744 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7392744 : Nat := 118140960795 + 7392744 * 2 ^ 59
def prefixEnd_7392744 : Nat := 4983230072969 + 3 ^ 40 * 7392744 * 2
def baseEnd_7392744 : Nat := 3796031027642129088801395

theorem tailTrace_7392744 : CollatzResearch.WordTrace tailWord_7392744 prefixEnd_7392744 3796031027642129088801395 := by
  unfold tailWord_7392744
  simp only [CollatzResearch.WordTrace]
  refine ⟨134817762564679271500584643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179757016752905695334112857 134817762564679271500584643)
  ·
    refine ⟨202226643847018907250876965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134817762564679271500584643 202226643847018907250876965)
    ·
      refine ⟨37917495721316045109539431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202226643847018907250876965 37917495721316045109539431)
      ·
        refine ⟨56876243581974067664309147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37917495721316045109539431 56876243581974067664309147)
        ·
          refine ⟨85314365372961101496463721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56876243581974067664309147 85314365372961101496463721)
          ·
            refine ⟨63985774029720826122347791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85314365372961101496463721 63985774029720826122347791)
            ·
              refine ⟨95978661044581239183521687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63985774029720826122347791 95978661044581239183521687)
              ·
                refine ⟨143967991566871858775282531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95978661044581239183521687 143967991566871858775282531)
                ·
                  refine ⟨215951987350307788162923797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143967991566871858775282531 215951987350307788162923797)
                  ·
                    refine ⟨10122749407045677570137053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215951987350307788162923797 10122749407045677570137053)
                    ·
                      refine ⟨3796031027642129088801395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122749407045677570137053 3796031027642129088801395)
                      ·
                        rfl

theorem cell23_7392744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7392744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392744 prefixEnd_7392744 := by exact prefixLift 7392744
  have htrace : WordTrace (prefixWord ++ tailWord_7392744) baseStart_7392744 baseEnd_7392744 := by
    simpa [prefixWord, tailWord_7392744, baseEnd_7392744] using wordTrace_append hprefix tailTrace_7392744
  have hstable : (prefixWord ++ tailWord_7392744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392744).length < 2 ^ (prefixWord ++ tailWord_7392744).sum := by decide
  have hdescent : baseEnd_7392744 < baseStart_7392744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392758 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7392758 : Nat := 118140960795 + 7392758 * 2 ^ 59
def prefixEnd_7392758 : Nat := 4983230072969 + 3 ^ 40 * 7392758 * 2
def baseEnd_7392758 : Nat := 3796038216371292034026331

theorem tailTrace_7392758 : CollatzResearch.WordTrace tailWord_7392758 prefixEnd_7392758 3796038216371292034026331 := by
  unfold tailWord_7392758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852252234456738962011183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179757357167538548928119285 16852252234456738962011183)
  ·
    refine ⟨25278378351685108443016775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16852252234456738962011183 25278378351685108443016775)
    ·
      refine ⟨37917567527527662664525163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25278378351685108443016775 37917567527527662664525163)
      ·
        refine ⟨56876351291291493996787745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37917567527527662664525163 56876351291291493996787745)
        ·
          refine ⟨42657263468468620497590809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56876351291291493996787745 42657263468468620497590809)
          ·
            refine ⟨31992947601351465373193107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42657263468468620497590809 31992947601351465373193107)
            ·
              refine ⟨47989421402027198059789661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31992947601351465373193107 47989421402027198059789661)
              ·
                refine ⟨17996033025760199272421123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47989421402027198059789661 17996033025760199272421123)
                ·
                  refine ⟨26994049538640298908631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17996033025760199272421123 26994049538640298908631685)
                  ·
                    refine ⟨5061384288495056045368441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26994049538640298908631685 5061384288495056045368441)
                    ·
                      refine ⟨3796038216371292034026331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061384288495056045368441 3796038216371292034026331)
                      ·
                        rfl

theorem cell23_7392758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7392758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392758 prefixEnd_7392758 := by exact prefixLift 7392758
  have htrace : WordTrace (prefixWord ++ tailWord_7392758) baseStart_7392758 baseEnd_7392758 := by
    simpa [prefixWord, tailWord_7392758, baseEnd_7392758] using wordTrace_append hprefix tailTrace_7392758
  have hstable : (prefixWord ++ tailWord_7392758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392758).length < 2 ^ (prefixWord ++ tailWord_7392758).sum := by decide
  have hdescent : baseEnd_7392758 < baseStart_7392758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392792 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7392792 : Nat := 118140960795 + 7392792 * 2 ^ 59
def prefixEnd_7392792 : Nat := 4983230072969 + 3 ^ 40 * 7392792 * 2
def baseEnd_7392792 : Nat := 3796055674713544901001175

theorem tailTrace_7392792 : CollatzResearch.WordTrace tailWord_7392792 prefixEnd_7392792 3796055674713544901001175 := by
  unfold tailWord_7392792
  simp only [CollatzResearch.WordTrace]
  refine ⟨134818637916592323599458315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179758183888789764799277753 134818637916592323599458315)
  ·
    refine ⟨202227956874888485399187473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134818637916592323599458315 202227956874888485399187473)
    ·
      refine ⟨151670967656166364049390605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202227956874888485399187473 151670967656166364049390605)
      ·
        refine ⟨56876612871062386518521477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151670967656166364049390605 56876612871062386518521477)
        ·
          refine ⟨10664364913324197472222777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56876612871062386518521477 10664364913324197472222777)
          ·
            refine ⟨7998273684993148104167083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10664364913324197472222777 7998273684993148104167083)
            ·
              refine ⟨11997410527489722156250625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998273684993148104167083 11997410527489722156250625)
              ·
                refine ⟨8998057895617291617187969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997410527489722156250625 8998057895617291617187969)
                ·
                  refine ⟨6748543421712968712890977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998057895617291617187969 6748543421712968712890977)
                  ·
                    refine ⟨5061407566284726534668233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748543421712968712890977 5061407566284726534668233)
                    ·
                      refine ⟨3796055674713544901001175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061407566284726534668233 3796055674713544901001175)
                      ·
                        rfl

theorem cell23_7392792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7392792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392792 prefixEnd_7392792 := by exact prefixLift 7392792
  have htrace : WordTrace (prefixWord ++ tailWord_7392792) baseStart_7392792 baseEnd_7392792 := by
    simpa [prefixWord, tailWord_7392792, baseEnd_7392792] using wordTrace_append hprefix tailTrace_7392792
  have hstable : (prefixWord ++ tailWord_7392792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392792).length < 2 ^ (prefixWord ++ tailWord_7392792).sum := by decide
  have hdescent : baseEnd_7392792 < baseStart_7392792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392794 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_7392794 : Nat := 118140960795 + 7392794 * 2 ^ 59
def prefixEnd_7392794 : Nat := 4983230072969 + 3 ^ 40 * 7392794 * 2
def baseEnd_7392794 : Nat := 1265352233891617964392055

theorem tailTrace_7392794 : CollatzResearch.WordTrace tailWord_7392794 prefixEnd_7392794 1265352233891617964392055 := by
  unfold tailWord_7392794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67409337194794350385122359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179758232519451601026992957 67409337194794350385122359)
  ·
    refine ⟨101114005792191525577683539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67409337194794350385122359 101114005792191525577683539)
    ·
      refine ⟨151671008688287288366525309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101114005792191525577683539 151671008688287288366525309)
      ·
        refine ⟨56876628258107733137446991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151671008688287288366525309 56876628258107733137446991)
        ·
          refine ⟨85314942387161599706170487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56876628258107733137446991 85314942387161599706170487)
          ·
            refine ⟨127972413580742399559255731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85314942387161599706170487 127972413580742399559255731)
            ·
              refine ⟨191958620371113599338883597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127972413580742399559255731 191958620371113599338883597)
              ·
                refine ⟨71984482639167599752081349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191958620371113599338883597 71984482639167599752081349)
                ·
                  refine ⟨13497090494843924953515253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71984482639167599752081349 13497090494843924953515253)
                  ·
                    refine ⟨1265352233891617964392055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13497090494843924953515253 1265352233891617964392055)
                    ·
                      rfl

theorem cell23_7392794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_7392794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392794 prefixEnd_7392794 := by exact prefixLift 7392794
  have htrace : WordTrace (prefixWord ++ tailWord_7392794) baseStart_7392794 baseEnd_7392794 := by
    simpa [prefixWord, tailWord_7392794, baseEnd_7392794] using wordTrace_append hprefix tailTrace_7392794
  have hstable : (prefixWord ++ tailWord_7392794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392794).length < 2 ^ (prefixWord ++ tailWord_7392794).sum := by decide
  have hdescent : baseEnd_7392794 < baseStart_7392794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392858 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_7392858 : Nat := 118140960795 + 7392858 * 2 ^ 59
def prefixEnd_7392858 : Nat := 4983230072969 + 3 ^ 40 * 7392858 * 2
def baseEnd_7392858 : Nat := 1265363188145580547591957

theorem tailTrace_7392858 : CollatzResearch.WordTrace tailWord_7392858 prefixEnd_7392858 1265363188145580547591957 := by
  unfold tailWord_7392858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67409920762736385117704807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179759788700630360313879485 67409920762736385117704807)
  ·
    refine ⟨101114881144104577676557211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67409920762736385117704807 101114881144104577676557211)
    ·
      refine ⟨151672321716156866514835817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101114881144104577676557211 151672321716156866514835817)
      ·
        refine ⟨113754241287117649886126863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151672321716156866514835817 113754241287117649886126863)
        ·
          refine ⟨170631361930676474829190295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113754241287117649886126863 170631361930676474829190295)
          ·
            refine ⟨255947042896014712243785443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170631361930676474829190295 255947042896014712243785443)
            ·
              refine ⟨383920564344022068365678165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255947042896014712243785443 383920564344022068365678165)
              ·
                refine ⟨4499069113406508613660291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 383920564344022068365678165 4499069113406508613660291)
                ·
                  refine ⟨6748603670109762920490437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499069113406508613660291 6748603670109762920490437)
                  ·
                    refine ⟨1265363188145580547591957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748603670109762920490437 1265363188145580547591957)
                    ·
                      rfl

theorem cell23_7392858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_7392858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392858 prefixEnd_7392858 := by exact prefixLift 7392858
  have htrace : WordTrace (prefixWord ++ tailWord_7392858) baseStart_7392858 baseEnd_7392858 := by
    simpa [prefixWord, tailWord_7392858, baseEnd_7392858] using wordTrace_append hprefix tailTrace_7392858
  have hstable : (prefixWord ++ tailWord_7392858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392858).length < 2 ^ (prefixWord ++ tailWord_7392858).sum := by decide
  have hdescent : baseEnd_7392858 < baseStart_7392858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392885 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7392885 : Nat := 118140960795 + 7392885 * 2 ^ 59
def prefixEnd_7392885 : Nat := 4983230072969 + 3 ^ 40 * 7392885 * 2
def baseEnd_7392885 : Nat := 3796103428414413037138247

theorem tailTrace_7392885 : CollatzResearch.WordTrace tailWord_7392885 prefixEnd_7392885 3796103428414413037138247 := by
  unfold tailWord_7392885
  simp only [CollatzResearch.WordTrace]
  refine ⟨269640667821847724082052109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179760445214565149388034739 269640667821847724082052109)
  ·
    refine ⟨101115250433192896530769541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269640667821847724082052109 101115250433192896530769541)
    ·
      refine ⟨18959109456223668099519289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101115250433192896530769541 18959109456223668099519289)
      ·
        refine ⟨14219332092167751074639467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18959109456223668099519289 14219332092167751074639467)
        ·
          refine ⟨21328998138251626611959201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219332092167751074639467 21328998138251626611959201)
          ·
            refine ⟨15996748603688719958969401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21328998138251626611959201 15996748603688719958969401)
            ·
              refine ⟨11997561452766539969227051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15996748603688719958969401 11997561452766539969227051)
              ·
                refine ⟨17996342179149809953840577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997561452766539969227051 17996342179149809953840577)
                ·
                  refine ⟨13497256634362357465380433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17996342179149809953840577 13497256634362357465380433)
                  ·
                    refine ⟨10122942475771768099035325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13497256634362357465380433 10122942475771768099035325)
                    ·
                      refine ⟨3796103428414413037138247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122942475771768099035325 3796103428414413037138247)
                      ·
                        rfl

theorem cell23_7392885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7392885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392885 prefixEnd_7392885 := by exact prefixLift 7392885
  have htrace : WordTrace (prefixWord ++ tailWord_7392885) baseStart_7392885 baseEnd_7392885 := by
    simpa [prefixWord, tailWord_7392885, baseEnd_7392885] using wordTrace_append hprefix tailTrace_7392885
  have hstable : (prefixWord ++ tailWord_7392885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392885).length < 2 ^ (prefixWord ++ tailWord_7392885).sum := by decide
  have hdescent : baseEnd_7392885 < baseStart_7392885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392908 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_7392908 : Nat := 118140960795 + 7392908 * 2 ^ 59
def prefixEnd_7392908 : Nat := 4983230072969 + 3 ^ 40 * 7392908 * 2
def baseEnd_7392908 : Nat := 3796115238469466447150641

theorem tailTrace_7392908 : CollatzResearch.WordTrace tailWord_7392908 prefixEnd_7392908 3796115238469466447150641 := by
  unfold tailWord_7392908
  simp only [CollatzResearch.WordTrace]
  refine ⟨134820753350382199505069689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179761004467176266006759585 134820753350382199505069689)
  ·
    refine ⟨101115565012786649628802267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134820753350382199505069689 101115565012786649628802267)
    ·
      refine ⟨151673347519179974443203401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101115565012786649628802267 151673347519179974443203401)
      ·
        refine ⟨113755010639384980832402551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151673347519179974443203401 113755010639384980832402551)
        ·
          refine ⟨170632515959077471248603827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113755010639384980832402551 170632515959077471248603827)
          ·
            refine ⟨255948773938616206872905741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170632515959077471248603827 255948773938616206872905741)
            ·
              refine ⟨95980790226981077577339653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255948773938616206872905741 95980790226981077577339653)
              ·
                refine ⟨17996398167558952045751185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95980790226981077577339653 17996398167558952045751185)
                ·
                  refine ⟨13497298625669214034313389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17996398167558952045751185 13497298625669214034313389)
                  ·
                    refine ⟨5061486984625955262867521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13497298625669214034313389 5061486984625955262867521)
                    ·
                      refine ⟨3796115238469466447150641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061486984625955262867521 3796115238469466447150641)
                      ·
                        rfl

theorem cell23_7392908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_7392908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392908 prefixEnd_7392908 := by exact prefixLift 7392908
  have htrace : WordTrace (prefixWord ++ tailWord_7392908) baseStart_7392908 baseEnd_7392908 := by
    simpa [prefixWord, tailWord_7392908, baseEnd_7392908] using wordTrace_append hprefix tailTrace_7392908
  have hstable : (prefixWord ++ tailWord_7392908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392908).length < 2 ^ (prefixWord ++ tailWord_7392908).sum := by decide
  have hdescent : baseEnd_7392908 < baseStart_7392908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392931 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 6]
def baseStart_7392931 : Nat := 118140960795 + 7392931 * 2 ^ 59
def prefixEnd_7392931 : Nat := 4983230072969 + 3 ^ 40 * 7392931 * 2
def baseEnd_7392931 : Nat := 1265375682841506619054345

theorem tailTrace_7392931 : CollatzResearch.WordTrace tailWord_7392931 prefixEnd_7392931 1265375682841506619054345 := by
  unfold tailWord_7392931
  simp only [CollatzResearch.WordTrace]
  refine ⟨269642345579681073938226647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179761563719787382625484431 269642345579681073938226647)
  ·
    refine ⟨404463518369521610907339971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269642345579681073938226647 404463518369521610907339971)
    ·
      refine ⟨606695277554282416361009957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404463518369521610907339971 606695277554282416361009957)
      ·
        refine ⟨113755364541427953067689367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 606695277554282416361009957 113755364541427953067689367)
        ·
          refine ⟨170633046812141929601534051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113755364541427953067689367 170633046812141929601534051)
          ·
            refine ⟨255949570218212894402301077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170633046812141929601534051 255949570218212894402301077)
            ·
              refine ⟨11997636103978729425107863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255949570218212894402301077 11997636103978729425107863)
              ·
                refine ⟨17996454155968094137661795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997636103978729425107863 17996454155968094137661795)
                ·
                  refine ⟨26994681233952141206492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17996454155968094137661795 26994681233952141206492693)
                  ·
                    refine ⟨1265375682841506619054345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26994681233952141206492693 1265375682841506619054345)
                    ·
                      rfl

theorem cell23_7392931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].length) (baseStart_7392931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392931 prefixEnd_7392931 := by exact prefixLift 7392931
  have htrace : WordTrace (prefixWord ++ tailWord_7392931) baseStart_7392931 baseEnd_7392931 := by
    simpa [prefixWord, tailWord_7392931, baseEnd_7392931] using wordTrace_append hprefix tailTrace_7392931
  have hstable : (prefixWord ++ tailWord_7392931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392931).length < 2 ^ (prefixWord ++ tailWord_7392931).sum := by decide
  have hdescent : baseEnd_7392931 < baseStart_7392931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392936 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7392936 : Nat := 118140960795 + 7392936 * 2 ^ 59
def prefixEnd_7392936 : Nat := 4983230072969 + 3 ^ 40 * 7392936 * 2
def baseEnd_7392936 : Nat := 3796129615927792337600513

theorem tailTrace_7392936 : CollatzResearch.WordTrace tailWord_7392936 prefixEnd_7392936 3796129615927792337600513 := by
  unfold tailWord_7392936
  simp only [CollatzResearch.WordTrace]
  refine ⟨134821263972331479896079331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179761685296441973194772441 134821263972331479896079331)
  ·
    refine ⟨202231895958497219844118997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134821263972331479896079331 202231895958497219844118997)
    ·
      refine ⟨4739810061527278590096539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202231895958497219844118997 4739810061527278590096539)
      ·
        refine ⟨7109715092290917885144809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739810061527278590096539 7109715092290917885144809)
        ·
          refine ⟨5332286319218188413858607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7109715092290917885144809 5332286319218188413858607)
          ·
            refine ⟨7998429478827282620787911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332286319218188413858607 7998429478827282620787911)
            ·
              refine ⟨11997644218240923931181867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998429478827282620787911 11997644218240923931181867)
              ·
                refine ⟨17996466327361385896772801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997644218240923931181867 17996466327361385896772801)
                ·
                  refine ⟨13497349745521039422579601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17996466327361385896772801 13497349745521039422579601)
                  ·
                    refine ⟨10123012309140779566934701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13497349745521039422579601 10123012309140779566934701)
                    ·
                      refine ⟨3796129615927792337600513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123012309140779566934701 3796129615927792337600513)
                      ·
                        rfl

theorem cell23_7392936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7392936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392936 prefixEnd_7392936 := by exact prefixLift 7392936
  have htrace : WordTrace (prefixWord ++ tailWord_7392936) baseStart_7392936 baseEnd_7392936 := by
    simpa [prefixWord, tailWord_7392936, baseEnd_7392936] using wordTrace_append hprefix tailTrace_7392936
  have hstable : (prefixWord ++ tailWord_7392936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392936).length < 2 ^ (prefixWord ++ tailWord_7392936).sum := by decide
  have hdescent : baseEnd_7392936 < baseStart_7392936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392942 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7392942 : Nat := 118140960795 + 7392942 * 2 ^ 59
def prefixEnd_7392942 : Nat := 4983230072969 + 3 ^ 40 * 7392942 * 2
def baseEnd_7392942 : Nat := 3796132696811719314125485

theorem tailTrace_7392942 : CollatzResearch.WordTrace tailWord_7392942 prefixEnd_7392942 3796132696811719314125485 := by
  unfold tailWord_7392942
  simp only [CollatzResearch.WordTrace]
  refine ⟨33705343347830152852109635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179761831188427481877918053 33705343347830152852109635)
  ·
    refine ⟨50558015021745229278164453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33705343347830152852109635 50558015021745229278164453)
    ·
      refine ⟨9479627816577230489655835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50558015021745229278164453 9479627816577230489655835)
      ·
        refine ⟨14219441724865845734483753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479627816577230489655835 14219441724865845734483753)
        ·
          refine ⟨10664581293649384300862815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219441724865845734483753 10664581293649384300862815)
          ·
            refine ⟨15996871940474076451294223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10664581293649384300862815 15996871940474076451294223)
            ·
              refine ⟨23995307910711114676941335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15996871940474076451294223 23995307910711114676941335)
              ·
                refine ⟨35992961866066672015412003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23995307910711114676941335 35992961866066672015412003)
                ·
                  refine ⟨53989442799100008023118005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35992961866066672015412003 53989442799100008023118005)
                  ·
                    refine ⟨5061510262415625752167313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53989442799100008023118005 5061510262415625752167313)
                    ·
                      refine ⟨3796132696811719314125485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061510262415625752167313 3796132696811719314125485)
                      ·
                        rfl

theorem cell23_7392942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7392942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392942 prefixEnd_7392942 := by exact prefixLift 7392942
  have htrace : WordTrace (prefixWord ++ tailWord_7392942) baseStart_7392942 baseEnd_7392942 := by
    simpa [prefixWord, tailWord_7392942, baseEnd_7392942] using wordTrace_append hprefix tailTrace_7392942
  have hstable : (prefixWord ++ tailWord_7392942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392942).length < 2 ^ (prefixWord ++ tailWord_7392942).sum := by decide
  have hdescent : baseEnd_7392942 < baseStart_7392942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392944 : List Nat := [2, 1, 1, 1, 2, 1, 4, 11]
def baseStart_7392944 : Nat := 118140960795 + 7392944 * 2 ^ 59
def prefixEnd_7392944 : Nat := 4983230072969 + 3 ^ 40 * 7392944 * 2
def baseEnd_7392944 : Nat := 140597545324926974307425

theorem tailTrace_7392944 : CollatzResearch.WordTrace tailWord_7392944 prefixEnd_7392944 140597545324926974307425 := by
  unfold tailWord_7392944
  simp only [CollatzResearch.WordTrace]
  refine ⟨134821409864316988579224943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179761879819089318105633257 134821409864316988579224943)
  ·
    refine ⟨202232114796475482868837415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134821409864316988579224943 202232114796475482868837415)
    ·
      refine ⟨303348172194713224303256123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202232114796475482868837415 303348172194713224303256123)
      ·
        refine ⟨455022258292069836454884185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303348172194713224303256123 455022258292069836454884185)
        ·
          refine ⟨341266693719052377341163139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455022258292069836454884185 341266693719052377341163139)
          ·
            refine ⟨511900040578578566011744709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341266693719052377341163139 511900040578578566011744709)
            ·
              refine ⟨95981257608483481127202133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511900040578578566011744709 95981257608483481127202133)
              ·
                refine ⟨140597545324926974307425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95981257608483481127202133 140597545324926974307425)
                ·
                  rfl

theorem cell23_7392944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_7392944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392944 prefixEnd_7392944 := by exact prefixLift 7392944
  have htrace : WordTrace (prefixWord ++ tailWord_7392944) baseStart_7392944 baseEnd_7392944 := by
    simpa [prefixWord, tailWord_7392944, baseEnd_7392944] using wordTrace_append hprefix tailTrace_7392944
  have hstable : (prefixWord ++ tailWord_7392944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392944).length < 2 ^ (prefixWord ++ tailWord_7392944).sum := by decide
  have hdescent : baseEnd_7392944 < baseStart_7392944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392949 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7392949 : Nat := 118140960795 + 7392949 * 2 ^ 59
def prefixEnd_7392949 : Nat := 4983230072969 + 3 ^ 40 * 7392949 * 2
def baseEnd_7392949 : Nat := 3796136291176300786737953

theorem tailTrace_7392949 : CollatzResearch.WordTrace tailWord_7392949 prefixEnd_7392949 3796136291176300786737953 := by
  unfold tailWord_7392949
  simp only [CollatzResearch.WordTrace]
  refine ⟨269643002093615863012381901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179762001395743908674921267 269643002093615863012381901)
  ·
    refine ⟨101116125785105948629643213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269643002093615863012381901 101116125785105948629643213)
    ·
      refine ⟨37918547169414730736116205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101116125785105948629643213 37918547169414730736116205)
      ·
        refine ⟨14219455188530524026043577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37918547169414730736116205 14219455188530524026043577)
        ·
          refine ⟨10664591391397893019532683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219455188530524026043577 10664591391397893019532683)
          ·
            refine ⟨15996887087096839529299025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10664591391397893019532683 15996887087096839529299025)
            ·
              refine ⟨11997665315322629646974269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15996887087096839529299025 11997665315322629646974269)
              ·
                refine ⟨4499124493245986117615351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11997665315322629646974269 4499124493245986117615351)
                ·
                  refine ⟨6748686739868979176423027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499124493245986117615351 6748686739868979176423027)
                  ·
                    refine ⟨10123030109803468764634541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748686739868979176423027 10123030109803468764634541)
                    ·
                      refine ⟨3796136291176300786737953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123030109803468764634541 3796136291176300786737953)
                      ·
                        rfl

theorem cell23_7392949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7392949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392949 prefixEnd_7392949 := by exact prefixLift 7392949
  have htrace : WordTrace (prefixWord ++ tailWord_7392949) baseStart_7392949 baseEnd_7392949 := by
    simpa [prefixWord, tailWord_7392949, baseEnd_7392949] using wordTrace_append hprefix tailTrace_7392949
  have hstable : (prefixWord ++ tailWord_7392949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392949).length < 2 ^ (prefixWord ++ tailWord_7392949).sum := by decide
  have hdescent : baseEnd_7392949 < baseStart_7392949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392966 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7392966 : Nat := 118140960795 + 7392966 * 2 ^ 59
def prefixEnd_7392966 : Nat := 4983230072969 + 3 ^ 40 * 7392966 * 2
def baseEnd_7392966 : Nat := 3796145020347427220225375

theorem tailTrace_7392966 : CollatzResearch.WordTrace tailWord_7392966 prefixEnd_7392966 3796145020347427220225375 := by
  unfold tailWord_7392966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426363191704821091117211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179762414756369516610500501 8426363191704821091117211)
  ·
    refine ⟨12639544787557231636675817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8426363191704821091117211 12639544787557231636675817)
    ·
      refine ⟨9479658590667923727506863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12639544787557231636675817 9479658590667923727506863)
      ·
        refine ⟨14219487886001885591260295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479658590667923727506863 14219487886001885591260295)
        ·
          refine ⟨21329231829002828386890443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219487886001885591260295 21329231829002828386890443)
          ·
            refine ⟨31993847743504242580335665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21329231829002828386890443 31993847743504242580335665)
            ·
              refine ⟨23995385807628181935251749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31993847743504242580335665 23995385807628181935251749)
              ·
                refine ⟨4499134838930284112859703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23995385807628181935251749 4499134838930284112859703)
                ·
                  refine ⟨6748702258395426169289555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499134838930284112859703 6748702258395426169289555)
                  ·
                    refine ⟨10123053387593139253934333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748702258395426169289555 10123053387593139253934333)
                    ·
                      refine ⟨3796145020347427220225375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123053387593139253934333 3796145020347427220225375)
                      ·
                        rfl

theorem cell23_7392966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7392966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392966 prefixEnd_7392966 := by exact prefixLift 7392966
  have htrace : WordTrace (prefixWord ++ tailWord_7392966) baseStart_7392966 baseEnd_7392966 := by
    simpa [prefixWord, tailWord_7392966, baseEnd_7392966] using wordTrace_append hprefix tailTrace_7392966
  have hstable : (prefixWord ++ tailWord_7392966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392966).length < 2 ^ (prefixWord ++ tailWord_7392966).sum := by decide
  have hdescent : baseEnd_7392966 < baseStart_7392966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392971 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3]
def baseStart_7392971 : Nat := 118140960795 + 7392971 * 2 ^ 59
def prefixEnd_7392971 : Nat := 4983230072969 + 3 ^ 40 * 7392971 * 2
def baseEnd_7392971 : Nat := 3796147587750699700662851

theorem tailTrace_7392971 : CollatzResearch.WordTrace tailWord_7392971 prefixEnd_7392971 3796147587750699700662851 := by
  unfold tailWord_7392971
  simp only [CollatzResearch.WordTrace]
  refine ⟨269643804499536160769682767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179762536333024107179788511 269643804499536160769682767)
  ·
    refine ⟨404465706749304241154524151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269643804499536160769682767 404465706749304241154524151)
    ·
      refine ⟨606698560123956361731786227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404465706749304241154524151 606698560123956361731786227)
      ·
        refine ⟨910047840185934542597679341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606698560123956361731786227 910047840185934542597679341)
        ·
          refine ⟨341267940069725453474129753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910047840185934542597679341 341267940069725453474129753)
          ·
            refine ⟨255950955052294090105597315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341267940069725453474129753 255950955052294090105597315)
            ·
              refine ⟨383926432578441135158395973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255950955052294090105597315 383926432578441135158395973)
              ·
                refine ⟨71986206108457712842199245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383926432578441135158395973 71986206108457712842199245)
                ·
                  refine ⟨26994827290671642315824717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71986206108457712842199245 26994827290671642315824717)
                  ·
                    refine ⟨10123060234001865868434269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26994827290671642315824717 10123060234001865868434269)
                    ·
                      refine ⟨3796147587750699700662851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123060234001865868434269 3796147587750699700662851)
                      ·
                        rfl

theorem cell23_7392971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].length) (baseStart_7392971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392971 prefixEnd_7392971 := by exact prefixLift 7392971
  have htrace : WordTrace (prefixWord ++ tailWord_7392971) baseStart_7392971 baseEnd_7392971 := by
    simpa [prefixWord, tailWord_7392971, baseEnd_7392971] using wordTrace_append hprefix tailTrace_7392971
  have hstable : (prefixWord ++ tailWord_7392971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392971).length < 2 ^ (prefixWord ++ tailWord_7392971).sum := by decide
  have hdescent : baseEnd_7392971 < baseStart_7392971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392995 : List Nat := [1, 1, 1, 7, 2, 2, 2, 7]
def baseStart_7392995 : Nat := 118140960795 + 7392995 * 2 ^ 59
def prefixEnd_7392995 : Nat := 4983230072969 + 3 ^ 40 * 7392995 * 2
def baseEnd_7392995 : Nat := 140598515232829911361583

theorem tailTrace_7392995 : CollatzResearch.WordTrace tailWord_7392995 prefixEnd_7392995 140598515232829911361583 := by
  unfold tailWord_7392995
  simp only [CollatzResearch.WordTrace]
  refine ⟨269644679851449212868556439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179763119900966141912370959 269644679851449212868556439)
  ·
    refine ⟨404467019777173819302834659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269644679851449212868556439 404467019777173819302834659)
    ·
      refine ⟨606700529665760728954251989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404467019777173819302834659 606700529665760728954251989)
      ·
        refine ⟨14219543664041267084865281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 606700529665760728954251989 14219543664041267084865281)
        ·
          refine ⟨10664657748030950313648961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219543664041267084865281 10664657748030950313648961)
          ·
            refine ⟨7998493311023212735236721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10664657748030950313648961 7998493311023212735236721)
            ·
              refine ⟨5998869983267409551427541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7998493311023212735236721 5998869983267409551427541)
              ·
                refine ⟨140598515232829911361583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5998869983267409551427541 140598515232829911361583)
                ·
                  rfl

theorem cell23_7392995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 7].length) (baseStart_7392995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392995 prefixEnd_7392995 := by exact prefixLift 7392995
  have htrace : WordTrace (prefixWord ++ tailWord_7392995) baseStart_7392995 baseEnd_7392995 := by
    simpa [prefixWord, tailWord_7392995, baseEnd_7392995] using wordTrace_append hprefix tailTrace_7392995
  have hstable : (prefixWord ++ tailWord_7392995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392995).length < 2 ^ (prefixWord ++ tailWord_7392995).sum := by decide
  have hdescent : baseEnd_7392995 < baseStart_7392995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393005 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7393005 : Nat := 118140960795 + 7393005 * 2 ^ 59
def prefixEnd_7393005 : Nat := 4983230072969 + 3 ^ 40 * 7393005 * 2
def baseEnd_7393005 : Nat := 3796165046092952567637695

theorem tailTrace_7393005 : CollatzResearch.WordTrace tailWord_7393005 prefixEnd_7393005 3796165046092952567637695 := by
  unfold tailWord_7393005
  simp only [CollatzResearch.WordTrace]
  refine ⟨269645044581412984576420469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179763363054275323050946979 269645044581412984576420469)
  ·
    refine ⟨25279222929507467304039419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269645044581412984576420469 25279222929507467304039419)
    ·
      refine ⟨37918834394261200956059129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25279222929507467304039419 37918834394261200956059129)
      ·
        refine ⟨28439125795695900717044347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37918834394261200956059129 28439125795695900717044347)
        ·
          refine ⟨42658688693543851075566521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28439125795695900717044347 42658688693543851075566521)
          ·
            refine ⟨31994016520157888306674891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42658688693543851075566521 31994016520157888306674891)
            ·
              refine ⟨47991024780236832460012337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31994016520157888306674891 47991024780236832460012337)
              ·
                refine ⟨35993268585177624345009253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47991024780236832460012337 35993268585177624345009253)
                ·
                  refine ⟨6748737859720804564689235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35993268585177624345009253 6748737859720804564689235)
                  ·
                    refine ⟨10123106789581206847033853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748737859720804564689235 10123106789581206847033853)
                    ·
                      refine ⟨3796165046092952567637695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123106789581206847033853 3796165046092952567637695)
                      ·
                        rfl

theorem cell23_7393005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7393005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393005 prefixEnd_7393005 := by exact prefixLift 7393005
  have htrace : WordTrace (prefixWord ++ tailWord_7393005) baseStart_7393005 baseEnd_7393005 := by
    simpa [prefixWord, tailWord_7393005, baseEnd_7393005] using wordTrace_append hprefix tailTrace_7393005
  have hstable : (prefixWord ++ tailWord_7393005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393005).length < 2 ^ (prefixWord ++ tailWord_7393005).sum := by decide
  have hdescent : baseEnd_7393005 < baseStart_7393005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393015 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_7393015 : Nat := 118140960795 + 7393015 * 2 ^ 59
def prefixEnd_7393015 : Nat := 4983230072969 + 3 ^ 40 * 7393015 * 2
def baseEnd_7393015 : Nat := 3796170180899497528512649

theorem tailTrace_7393015 : CollatzResearch.WordTrace tailWord_7393015 prefixEnd_7393015 3796170180899497528512649 := by
  unfold tailWord_7393015
  simp only [CollatzResearch.WordTrace]
  refine ⟨269645409311376756284284499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179763606207584504189522999 269645409311376756284284499)
  ·
    refine ⟨404468113967065134426426749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269645409311376756284284499 404468113967065134426426749)
    ·
      refine ⟨151675542737649425409910031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404468113967065134426426749 151675542737649425409910031)
      ·
        refine ⟨227513314106474138114865047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151675542737649425409910031 227513314106474138114865047)
        ·
          refine ⟨341269971159711207172297571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227513314106474138114865047 341269971159711207172297571)
          ·
            refine ⟨511904956739566810758446357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341269971159711207172297571 511904956739566810758446357)
            ·
              refine ⟨23995544847167194254302173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 511904956739566810758446357 23995544847167194254302173)
              ·
                refine ⟨8998329317687697845363315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23995544847167194254302173 8998329317687697845363315)
                ·
                  refine ⟨13497493976531546768044973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998329317687697845363315 13497493976531546768044973)
                  ·
                    refine ⟨5061560241199330038016865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13497493976531546768044973 5061560241199330038016865)
                    ·
                      refine ⟨3796170180899497528512649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061560241199330038016865 3796170180899497528512649)
                      ·
                        rfl

theorem cell23_7393015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_7393015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393015 prefixEnd_7393015 := by exact prefixLift 7393015
  have htrace : WordTrace (prefixWord ++ tailWord_7393015) baseStart_7393015 baseEnd_7393015 := by
    simpa [prefixWord, tailWord_7393015, baseEnd_7393015] using wordTrace_append hprefix tailTrace_7393015
  have hstable : (prefixWord ++ tailWord_7393015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393015).length < 2 ^ (prefixWord ++ tailWord_7393015).sum := by decide
  have hdescent : baseEnd_7393015 < baseStart_7393015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393021 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_7393021 : Nat := 118140960795 + 7393021 * 2 ^ 59
def prefixEnd_7393021 : Nat := 4983230072969 + 3 ^ 40 * 7393021 * 2
def baseEnd_7393021 : Nat := 1265391087261141501679207

theorem tailTrace_7393021 : CollatzResearch.WordTrace tailWord_7393021 prefixEnd_7393021 1265391087261141501679207 := by
  unfold tailWord_7393021
  simp only [CollatzResearch.WordTrace]
  refine ⟨269645628149355019309002917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179763752099570012872668611 269645628149355019309002917)
  ·
    refine ⟨50558555278004066120438047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269645628149355019309002917 50558555278004066120438047)
    ·
      refine ⟨75837832917006099180657071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50558555278004066120438047 75837832917006099180657071)
      ·
        refine ⟨113756749375509148770985607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75837832917006099180657071 113756749375509148770985607)
        ·
          refine ⟨170635124063263723156478411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113756749375509148770985607 170635124063263723156478411)
          ·
            refine ⟨255952686094895584734717617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170635124063263723156478411 255952686094895584734717617)
            ·
              refine ⟨191964514571171688551038213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255952686094895584734717617 191964514571171688551038213)
              ·
                refine ⟨35993346482094691603319665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191964514571171688551038213 35993346482094691603319665)
                ·
                  refine ⟨26995009861571018702489749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35993346482094691603319665 26995009861571018702489749)
                  ·
                    refine ⟨1265391087261141501679207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26995009861571018702489749 1265391087261141501679207)
                    ·
                      rfl

theorem cell23_7393021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_7393021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393021 prefixEnd_7393021 := by exact prefixLift 7393021
  have htrace : WordTrace (prefixWord ++ tailWord_7393021) baseStart_7393021 baseEnd_7393021 := by
    simpa [prefixWord, tailWord_7393021, baseEnd_7393021] using wordTrace_append hprefix tailTrace_7393021
  have hstable : (prefixWord ++ tailWord_7393021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393021).length < 2 ^ (prefixWord ++ tailWord_7393021).sum := by decide
  have hdescent : baseEnd_7393021 < baseStart_7393021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393041 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_7393041 : Nat := 118140960795 + 7393041 * 2 ^ 59
def prefixEnd_7393041 : Nat := 4983230072969 + 3 ^ 40 * 7393041 * 2
def baseEnd_7393041 : Nat := 3796183531396514426787529

theorem tailTrace_7393041 : CollatzResearch.WordTrace tailWord_7393041 prefixEnd_7393041 3796183531396514426787529 := by
  unfold tailWord_7393041
  simp only [CollatzResearch.WordTrace]
  refine ⟨269646357609282562724730977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179764238406188375149820651 269646357609282562724730977)
  ·
    refine ⟨202234768206961922043548233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269646357609282562724730977 202234768206961922043548233)
    ·
      refine ⟨151676076155221441532661175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202234768206961922043548233 151676076155221441532661175)
      ·
        refine ⟨227514114232832162298991763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151676076155221441532661175 227514114232832162298991763)
        ·
          refine ⟨341271171349248243448487645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227514114232832162298991763 341271171349248243448487645)
          ·
            refine ⟨127976689255968091293182867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341271171349248243448487645 127976689255968091293182867)
            ·
              refine ⟨191965033883952136939774301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127976689255968091293182867 191965033883952136939774301)
              ·
                refine ⟨71986887706482051352415363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191965033883952136939774301 71986887706482051352415363)
                ·
                  refine ⟨107980331559723077028623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71986887706482051352415363 107980331559723077028623045)
                  ·
                    refine ⟨20246312167448076942866821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107980331559723077028623045 20246312167448076942866821)
                    ·
                      refine ⟨3796183531396514426787529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20246312167448076942866821 3796183531396514426787529)
                      ·
                        rfl

theorem cell23_7393041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_7393041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393041 prefixEnd_7393041 := by exact prefixLift 7393041
  have htrace : WordTrace (prefixWord ++ tailWord_7393041) baseStart_7393041 baseEnd_7393041 := by
    simpa [prefixWord, tailWord_7393041, baseEnd_7393041] using wordTrace_append hprefix tailTrace_7393041
  have hstable : (prefixWord ++ tailWord_7393041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393041).length < 2 ^ (prefixWord ++ tailWord_7393041).sum := by decide
  have hdescent : baseEnd_7393041 < baseStart_7393041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393145 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_7393145 : Nat := 118140960795 + 7393145 * 2 ^ 59
def prefixEnd_7393145 : Nat := 4983230072969 + 3 ^ 40 * 7393145 * 2
def baseEnd_7393145 : Nat := 1265412311128194006629017

theorem tailTrace_7393145 : CollatzResearch.WordTrace tailWord_7393145 prefixEnd_7393145 1265412311128194006629017 := by
  unfold tailWord_7393145
  simp only [CollatzResearch.WordTrace]
  refine ⟨269650150800905788486516889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179766767200603858991011259 269650150800905788486516889)
  ·
    refine ⟨202237613100679341364887667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269650150800905788486516889 202237613100679341364887667)
    ·
      refine ⟨303356419651019012047331501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202237613100679341364887667 303356419651019012047331501)
      ·
        refine ⟨113758657369132129517749313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303356419651019012047331501 113758657369132129517749313)
        ·
          refine ⟨85318993026849097138311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113758657369132129517749313 85318993026849097138311985)
          ·
            refine ⟨63989244770136822853733989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85318993026849097138311985 63989244770136822853733989)
            ·
              refine ⟨11997983394400654285075123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63989244770136822853733989 11997983394400654285075123)
              ·
                refine ⟨17996975091600981427612685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997983394400654285075123 17996975091600981427612685)
                ·
                  refine ⟨6748865659350368035354757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17996975091600981427612685 6748865659350368035354757)
                  ·
                    refine ⟨1265412311128194006629017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748865659350368035354757 1265412311128194006629017)
                    ·
                      rfl

theorem cell23_7393145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_7393145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393145 prefixEnd_7393145 := by exact prefixLift 7393145
  have htrace : WordTrace (prefixWord ++ tailWord_7393145) baseStart_7393145 baseEnd_7393145 := by
    simpa [prefixWord, tailWord_7393145, baseEnd_7393145] using wordTrace_append hprefix tailTrace_7393145
  have hstable : (prefixWord ++ tailWord_7393145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393145).length < 2 ^ (prefixWord ++ tailWord_7393145).sum := by decide
  have hdescent : baseEnd_7393145 < baseStart_7393145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393252 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_7393252 : Nat := 118140960795 + 7393252 * 2 ^ 59
def prefixEnd_7393252 : Nat := 4983230072969 + 3 ^ 40 * 7393252 * 2
def baseEnd_7393252 : Nat := 1265430625271537700416353

theorem tailTrace_7393252 : CollatzResearch.WordTrace tailWord_7393252 prefixEnd_7393252 1265430625271537700416353 := by
  unfold tailWord_7393252
  simp only [CollatzResearch.WordTrace]
  refine ⟨134827026705759072880331005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179769368941012097173774673 134827026705759072880331005)
  ·
    refine ⟨50560135014659652330124127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134827026705759072880331005 50560135014659652330124127)
    ·
      refine ⟨75840202521989478495186191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50560135014659652330124127 75840202521989478495186191)
      ·
        refine ⟨113760303782984217742779287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75840202521989478495186191 113760303782984217742779287)
        ·
          refine ⟨170640455674476326614168931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113760303782984217742779287 170640455674476326614168931)
          ·
            refine ⟨255960683511714489921253397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170640455674476326614168931 255960683511714489921253397)
            ·
              refine ⟨11998157039611616715058753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255960683511714489921253397 11998157039611616715058753)
              ·
                refine ⟨8998617779708712536294065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998157039611616715058753 8998617779708712536294065)
                ·
                  refine ⟨6748963334781534402220549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998617779708712536294065 6748963334781534402220549)
                  ·
                    refine ⟨1265430625271537700416353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748963334781534402220549 1265430625271537700416353)
                    ·
                      rfl

theorem cell23_7393252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_7393252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393252 prefixEnd_7393252 := by exact prefixLift 7393252
  have htrace : WordTrace (prefixWord ++ tailWord_7393252) baseStart_7393252 baseEnd_7393252 := by
    simpa [prefixWord, tailWord_7393252, baseEnd_7393252] using wordTrace_append hprefix tailTrace_7393252
  have hstable : (prefixWord ++ tailWord_7393252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393252).length < 2 ^ (prefixWord ++ tailWord_7393252).sum := by decide
  have hdescent : baseEnd_7393252 < baseStart_7393252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393262 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_7393262 : Nat := 118140960795 + 7393262 * 2 ^ 59
def prefixEnd_7393262 : Nat := 4983230072969 + 3 ^ 40 * 7393262 * 2
def baseEnd_7393262 : Nat := 3796297010621158062124013

theorem tailTrace_7393262 : CollatzResearch.WordTrace tailWord_7393262 prefixEnd_7393262 3796297010621158062124013 := by
  unfold tailWord_7393262
  simp only [CollatzResearch.WordTrace]
  refine ⟨33706802267685239683565755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179769612094321278312350693 33706802267685239683565755)
  ·
    refine ⟨50560203401527859525348633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33706802267685239683565755 50560203401527859525348633)
    ·
      refine ⟨37920152551145894644011475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50560203401527859525348633 37920152551145894644011475)
      ·
        refine ⟨56880228826718841966017213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37920152551145894644011475 56880228826718841966017213)
        ·
          refine ⟨21330085810019565737256455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56880228826718841966017213 21330085810019565737256455)
          ·
            refine ⟨31995128715029348605884683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330085810019565737256455 31995128715029348605884683)
            ·
              refine ⟨47992693072544022908827025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31995128715029348605884683 47992693072544022908827025)
              ·
                refine ⟨35994519804408017181620269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47992693072544022908827025 35994519804408017181620269)
                ·
                  refine ⟨13497944926653006443107601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35994519804408017181620269 13497944926653006443107601)
                  ·
                    refine ⟨10123458694989754832330701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13497944926653006443107601 10123458694989754832330701)
                    ·
                      refine ⟨3796297010621158062124013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123458694989754832330701 3796297010621158062124013)
                      ·
                        rfl

theorem cell23_7393262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_7393262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393262 prefixEnd_7393262 := by exact prefixLift 7393262
  have htrace : WordTrace (prefixWord ++ tailWord_7393262) baseStart_7393262 baseEnd_7393262 := by
    simpa [prefixWord, tailWord_7393262, baseEnd_7393262] using wordTrace_append hprefix tailTrace_7393262
  have hstable : (prefixWord ++ tailWord_7393262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393262).length < 2 ^ (prefixWord ++ tailWord_7393262).sum := by decide
  have hdescent : baseEnd_7393262 < baseStart_7393262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393275 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3]
def baseStart_7393275 : Nat := 118140960795 + 7393275 * 2 ^ 59
def prefixEnd_7393275 : Nat := 4983230072969 + 3 ^ 40 * 7393275 * 2
def baseEnd_7393275 : Nat := 3796303685869666511261453

theorem tailTrace_7393275 : CollatzResearch.WordTrace tailWord_7393275 prefixEnd_7393275 3796303685869666511261453 := by
  unfold tailWord_7393275
  simp only [CollatzResearch.WordTrace]
  refine ⟨269654892290434820688749279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179769928193623213792499519 269654892290434820688749279)
  ·
    refine ⟨404482338435652231033123919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269654892290434820688749279 404482338435652231033123919)
    ·
      refine ⟨606723507653478346549685879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404482338435652231033123919 606723507653478346549685879)
      ·
        refine ⟨910085261480217519824528819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606723507653478346549685879 910085261480217519824528819)
        ·
          refine ⟨1365127892220326279736793229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910085261480217519824528819 1365127892220326279736793229)
          ·
            refine ⟨511922959582622354901297461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365127892220326279736793229 511922959582622354901297461)
            ·
              refine ⟨47992777460870845771996637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 511922959582622354901297461 47992777460870845771996637)
              ·
                refine ⟨17997291547826567164498739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47992777460870845771996637 17997291547826567164498739)
                ·
                  refine ⟨26995937321739850746748109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17997291547826567164498739 26995937321739850746748109)
                  ·
                    refine ⟨10123476495652444030030541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26995937321739850746748109 10123476495652444030030541)
                    ·
                      refine ⟨3796303685869666511261453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123476495652444030030541 3796303685869666511261453)
                      ·
                        rfl

theorem cell23_7393275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].length) (baseStart_7393275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393275 prefixEnd_7393275 := by exact prefixLift 7393275
  have htrace : WordTrace (prefixWord ++ tailWord_7393275) baseStart_7393275 baseEnd_7393275 := by
    simpa [prefixWord, tailWord_7393275, baseEnd_7393275] using wordTrace_append hprefix tailTrace_7393275
  have hstable : (prefixWord ++ tailWord_7393275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393275).length < 2 ^ (prefixWord ++ tailWord_7393275).sum := by decide
  have hdescent : baseEnd_7393275 < baseStart_7393275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393292 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_7393292 : Nat := 118140960795 + 7393292 * 2 ^ 59
def prefixEnd_7393292 : Nat := 4983230072969 + 3 ^ 40 * 7393292 * 2
def baseEnd_7393292 : Nat := 3796312415040792944748875

theorem tailTrace_7393292 : CollatzResearch.WordTrace tailWord_7393292 prefixEnd_7393292 3796312415040792944748875 := by
  unfold tailWord_7393292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134827756165686616296059065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179770341554248821728078753 134827756165686616296059065)
  ·
    refine ⟨101120817124264962222044299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134827756165686616296059065 101120817124264962222044299)
    ·
      refine ⟨151681225686397443333066449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101120817124264962222044299 151681225686397443333066449)
      ·
        refine ⟨113760919264798082499799837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151681225686397443333066449 113760919264798082499799837)
        ·
          refine ⟨42660344724299280937424939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113760919264798082499799837 42660344724299280937424939)
          ·
            refine ⟨63990517086448921406137409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42660344724299280937424939 63990517086448921406137409)
            ·
              refine ⟨47992887814836691054603057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63990517086448921406137409 47992887814836691054603057)
              ·
                refine ⟨35994665861127518290952293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47992887814836691054603057 35994665861127518290952293)
                ·
                  refine ⟨6748999848961409679553555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35994665861127518290952293 6748999848961409679553555)
                  ·
                    refine ⟨10123499773442114519330333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748999848961409679553555 10123499773442114519330333)
                    ·
                      refine ⟨3796312415040792944748875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123499773442114519330333 3796312415040792944748875)
                      ·
                        rfl

theorem cell23_7393292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_7393292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393292 prefixEnd_7393292 := by exact prefixLift 7393292
  have htrace : WordTrace (prefixWord ++ tailWord_7393292) baseStart_7393292 baseEnd_7393292 := by
    simpa [prefixWord, tailWord_7393292, baseEnd_7393292] using wordTrace_append hprefix tailTrace_7393292
  have hstable : (prefixWord ++ tailWord_7393292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393292).length < 2 ^ (prefixWord ++ tailWord_7393292).sum := by decide
  have hdescent : baseEnd_7393292 < baseStart_7393292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393293 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7393293 : Nat := 118140960795 + 7393293 * 2 ^ 59
def prefixEnd_7393293 : Nat := 4983230072969 + 3 ^ 40 * 7393293 * 2
def baseEnd_7393293 : Nat := 3796312928521447440836371

theorem tailTrace_7393293 : CollatzResearch.WordTrace tailWord_7393293 prefixEnd_7393293 3796312928521447440836371 := by
  unfold tailWord_7393293
  simp only [CollatzResearch.WordTrace]
  refine ⟨269655548804369609762904533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179770365869579739841936355 269655548804369609762904533)
  ·
    refine ⟨6320051925102412728818075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 269655548804369609762904533 6320051925102412728818075)
    ·
      refine ⟨9480077887653619093227113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320051925102412728818075 9480077887653619093227113)
      ·
        refine ⟨7110058415740214319920335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9480077887653619093227113 7110058415740214319920335)
        ·
          refine ⟨10665087623610321479880503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110058415740214319920335 10665087623610321479880503)
          ·
            refine ⟨15997631435415482219820755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665087623610321479880503 15997631435415482219820755)
            ·
              refine ⟨23996447153123223329731133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997631435415482219820755 23996447153123223329731133)
              ·
                refine ⟨8998667682421208748649175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23996447153123223329731133 8998667682421208748649175)
                ·
                  refine ⟨13498001523631813122973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998667682421208748649175 13498001523631813122973763)
                  ·
                    refine ⟨20247002285447719684460645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13498001523631813122973763 20247002285447719684460645)
                    ·
                      refine ⟨3796312928521447440836371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20247002285447719684460645 3796312928521447440836371)
                      ·
                        rfl

theorem cell23_7393293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7393293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393293 prefixEnd_7393293 := by exact prefixLift 7393293
  have htrace : WordTrace (prefixWord ++ tailWord_7393293) baseStart_7393293 baseEnd_7393293 := by
    simpa [prefixWord, tailWord_7393293, baseEnd_7393293] using wordTrace_append hprefix tailTrace_7393293
  have hstable : (prefixWord ++ tailWord_7393293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393293).length < 2 ^ (prefixWord ++ tailWord_7393293).sum := by decide
  have hdescent : baseEnd_7393293 < baseStart_7393293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393309 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_7393309 : Nat := 118140960795 + 7393309 * 2 ^ 59
def prefixEnd_7393309 : Nat := 4983230072969 + 3 ^ 40 * 7393309 * 2
def baseEnd_7393309 : Nat := 3796321144211919378236297

theorem tailTrace_7393309 : CollatzResearch.WordTrace tailWord_7393309 prefixEnd_7393309 3796321144211919378236297 := by
  unfold tailWord_7393309
  simp only [CollatzResearch.WordTrace]
  refine ⟨269656132372311644495486981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179770754914874429663657987 269656132372311644495486981)
  ·
    refine ⟨50560524819808433342903809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269656132372311644495486981 50560524819808433342903809)
    ·
      refine ⟨37920393614856325007177857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50560524819808433342903809 37920393614856325007177857)
      ·
        refine ⟨28440295211142243755383393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37920393614856325007177857 28440295211142243755383393)
        ·
          refine ⟨21330221408356682816537545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28440295211142243755383393 21330221408356682816537545)
          ·
            refine ⟨15997666056267512112403159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21330221408356682816537545 15997666056267512112403159)
            ·
              refine ⟨23996499084401268168604739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997666056267512112403159 23996499084401268168604739)
              ·
                refine ⟨35994748626601902252907109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23996499084401268168604739 35994748626601902252907109)
                ·
                  refine ⟨6749015367487856672420083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35994748626601902252907109 6749015367487856672420083)
                  ·
                    refine ⟨10123523051231785008630125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749015367487856672420083 10123523051231785008630125)
                    ·
                      refine ⟨3796321144211919378236297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123523051231785008630125 3796321144211919378236297)
                      ·
                        rfl

theorem cell23_7393309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_7393309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393309 prefixEnd_7393309 := by exact prefixLift 7393309
  have htrace : WordTrace (prefixWord ++ tailWord_7393309) baseStart_7393309 baseEnd_7393309 := by
    simpa [prefixWord, tailWord_7393309, baseEnd_7393309] using wordTrace_append hprefix tailTrace_7393309
  have hstable : (prefixWord ++ tailWord_7393309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393309).length < 2 ^ (prefixWord ++ tailWord_7393309).sum := by decide
  have hdescent : baseEnd_7393309 < baseStart_7393309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393335 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_7393335 : Nat := 118140960795 + 7393335 * 2 ^ 59
def prefixEnd_7393335 : Nat := 4983230072969 + 3 ^ 40 * 7393335 * 2
def baseEnd_7393335 : Nat := 3796334494708936276511177

theorem tailTrace_7393335 : CollatzResearch.WordTrace tailWord_7393335 prefixEnd_7393335 3796334494708936276511177 := by
  unfold tailWord_7393335
  simp only [CollatzResearch.WordTrace]
  refine ⟨269657080670217450935933459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179771387113478300623955639 269657080670217450935933459)
  ·
    refine ⟨404485621005326176403900189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269657080670217450935933459 404485621005326176403900189)
    ·
      refine ⟨151682107876997316151462571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404485621005326176403900189 151682107876997316151462571)
      ·
        refine ⟨227523161815495974227193857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151682107876997316151462571 227523161815495974227193857)
        ·
          refine ⟨170642371361621980670395393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227523161815495974227193857 170642371361621980670395393)
          ·
            refine ⟨127981778521216485502796545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170642371361621980670395393 127981778521216485502796545)
            ·
              refine ⟨95986333890912364127097409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127981778521216485502796545 95986333890912364127097409)
              ·
                refine ⟨71989750418184273095323057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95986333890912364127097409 71989750418184273095323057)
                ·
                  refine ⟨53992312813638204821492293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71989750418184273095323057 53992312813638204821492293)
                  ·
                    refine ⟨10123558652557163404029805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53992312813638204821492293 10123558652557163404029805)
                    ·
                      refine ⟨3796334494708936276511177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123558652557163404029805 3796334494708936276511177)
                      ·
                        rfl

theorem cell23_7393335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_7393335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393335 prefixEnd_7393335 := by exact prefixLift 7393335
  have htrace : WordTrace (prefixWord ++ tailWord_7393335) baseStart_7393335 baseEnd_7393335 := by
    simpa [prefixWord, tailWord_7393335, baseEnd_7393335] using wordTrace_append hprefix tailTrace_7393335
  have hstable : (prefixWord ++ tailWord_7393335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393335).length < 2 ^ (prefixWord ++ tailWord_7393335).sum := by decide
  have hdescent : baseEnd_7393335 < baseStart_7393335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393336 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_7393336 : Nat := 118140960795 + 7393336 * 2 ^ 59
def prefixEnd_7393336 : Nat := 4983230072969 + 3 ^ 40 * 7393336 * 2
def baseEnd_7393336 : Nat := 3796335008189590772598673

theorem tailTrace_7393336 : CollatzResearch.WordTrace tailWord_7393336 prefixEnd_7393336 3796335008189590772598673 := by
  unfold tailWord_7393336
  simp only [CollatzResearch.WordTrace]
  refine ⟨134828558571606914053359931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179771411428809218737813241 134828558571606914053359931)
  ·
    refine ⟨202242837857410371080039897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134828558571606914053359931 202242837857410371080039897)
    ·
      refine ⟨151682128393057778310029923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202242837857410371080039897 151682128393057778310029923)
      ·
        refine ⟨227523192589586667465044885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151682128393057778310029923 227523192589586667465044885)
        ·
          refine ⟨10665149652636875037423979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227523192589586667465044885 10665149652636875037423979)
          ·
            refine ⟨15997724478955312556135969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665149652636875037423979 15997724478955312556135969)
            ·
              refine ⟨11998293359216484417101977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15997724478955312556135969 11998293359216484417101977)
              ·
                refine ⟨8998720019412363312826483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998293359216484417101977 8998720019412363312826483)
                ·
                  refine ⟨13498080029118544969239725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998720019412363312826483 13498080029118544969239725)
                  ·
                    refine ⟨5061780010919454363464897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13498080029118544969239725 5061780010919454363464897)
                    ·
                      refine ⟨3796335008189590772598673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061780010919454363464897 3796335008189590772598673)
                      ·
                        rfl

theorem cell23_7393336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_7393336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393336 prefixEnd_7393336 := by exact prefixLift 7393336
  have htrace : WordTrace (prefixWord ++ tailWord_7393336) baseStart_7393336 baseEnd_7393336 := by
    simpa [prefixWord, tailWord_7393336, baseEnd_7393336] using wordTrace_append hprefix tailTrace_7393336
  have hstable : (prefixWord ++ tailWord_7393336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393336).length < 2 ^ (prefixWord ++ tailWord_7393336).sum := by decide
  have hdescent : baseEnd_7393336 < baseStart_7393336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393372 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 7]
def baseStart_7393372 : Nat := 118140960795 + 7393372 * 2 ^ 59
def prefixEnd_7393372 : Nat := 4983230072969 + 3 ^ 40 * 7393372 * 2
def baseEnd_7393372 : Nat := 421817054832572514638723

theorem tailTrace_7393372 : CollatzResearch.WordTrace tailWord_7393372 prefixEnd_7393372 421817054832572514638723 := by
  unfold tailWord_7393372
  simp only [CollatzResearch.WordTrace]
  refine ⟨134829215085541703127515185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179772286780722270836686913 134829215085541703127515185)
  ·
    refine ⟨101121911314156277345636389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134829215085541703127515185 101121911314156277345636389)
    ·
      refine ⟨18960358371404302002306823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101121911314156277345636389 18960358371404302002306823)
      ·
        refine ⟨28440537557106453003460235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18960358371404302002306823 28440537557106453003460235)
        ·
          refine ⟨42660806335659679505190353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28440537557106453003460235 42660806335659679505190353)
          ·
            refine ⟨31995604751744759628892765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42660806335659679505190353 31995604751744759628892765)
            ·
              refine ⟨11998351781904284860834787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31995604751744759628892765 11998351781904284860834787)
              ·
                refine ⟨17997527672856427291252181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11998351781904284860834787 17997527672856427291252181)
                ·
                  refine ⟨421817054832572514638723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17997527672856427291252181 421817054832572514638723)
                  ·
                    rfl

theorem cell23_7393372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_7393372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393372 prefixEnd_7393372 := by exact prefixLift 7393372
  have htrace : WordTrace (prefixWord ++ tailWord_7393372) baseStart_7393372 baseEnd_7393372 := by
    simpa [prefixWord, tailWord_7393372, baseEnd_7393372] using wordTrace_append hprefix tailTrace_7393372
  have hstable : (prefixWord ++ tailWord_7393372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393372).length < 2 ^ (prefixWord ++ tailWord_7393372).sum := by decide
  have hdescent : baseEnd_7393372 < baseStart_7393372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393385 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_7393385 : Nat := 118140960795 + 7393385 * 2 ^ 59
def prefixEnd_7393385 : Nat := 4983230072969 + 3 ^ 40 * 7393385 * 2
def baseEnd_7393385 : Nat := 1265453389580553693628649

theorem tailTrace_7393385 : CollatzResearch.WordTrace tailWord_7393385 prefixEnd_7393385 1265453389580553693628649 := by
  unfold tailWord_7393385
  simp only [CollatzResearch.WordTrace]
  refine ⟨269658904320036309475253609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179772602880024206316835739 269658904320036309475253609)
  ·
    refine ⟨202244178240027232106440207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269658904320036309475253609 202244178240027232106440207)
    ·
      refine ⟨303366267360040848159660311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202244178240027232106440207 303366267360040848159660311)
      ·
        refine ⟨455049401040061272239490467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303366267360040848159660311 455049401040061272239490467)
        ·
          refine ⟨682574101560091908359235701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455049401040061272239490467 682574101560091908359235701)
          ·
            refine ⟨63991322021258616408678347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 682574101560091908359235701 63991322021258616408678347)
            ·
              refine ⟨95986983031887924613017521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63991322021258616408678347 95986983031887924613017521)
              ·
                refine ⟨71990237273915943459763141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95986983031887924613017521 71990237273915943459763141)
                ·
                  refine ⟨13498169488859239398705589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71990237273915943459763141 13498169488859239398705589)
                  ·
                    refine ⟨1265453389580553693628649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13498169488859239398705589 1265453389580553693628649)
                    ·
                      rfl

theorem cell23_7393385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_7393385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393385 prefixEnd_7393385 := by exact prefixLift 7393385
  have htrace : WordTrace (prefixWord ++ tailWord_7393385) baseStart_7393385 baseEnd_7393385 := by
    simpa [prefixWord, tailWord_7393385, baseEnd_7393385] using wordTrace_append hprefix tailTrace_7393385
  have hstable : (prefixWord ++ tailWord_7393385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393385).length < 2 ^ (prefixWord ++ tailWord_7393385).sum := by decide
  have hdescent : baseEnd_7393385 < baseStart_7393385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393430 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7393430 : Nat := 118140960795 + 7393430 * 2 ^ 59
def prefixEnd_7393430 : Nat := 4983230072969 + 3 ^ 40 * 7393430 * 2
def baseEnd_7393430 : Nat := 3796383275371113404823241

theorem tailTrace_7393430 : CollatzResearch.WordTrace tailWord_7393430 prefixEnd_7393430 3796383275371113404823241 := by
  unfold tailWord_7393430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853784100304580135040109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179773697069915521440427829 16853784100304580135040109)
  ·
    refine ⟨6320169037614217550640041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16853784100304580135040109 6320169037614217550640041)
    ·
      refine ⟨4740126778210663162980031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6320169037614217550640041 4740126778210663162980031)
      ·
        refine ⟨7110190167315994744470047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740126778210663162980031 7110190167315994744470047)
        ·
          refine ⟨10665285250973992116705071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110190167315994744470047 10665285250973992116705071)
          ·
            refine ⟨15997927876460988175057607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665285250973992116705071 15997927876460988175057607)
            ·
              refine ⟨23996891814691482262586411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997927876460988175057607 23996891814691482262586411)
              ·
                refine ⟨35995337722037223393879617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23996891814691482262586411 35995337722037223393879617)
                ·
                  refine ⟨26996503291527917545409713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35995337722037223393879617 26996503291527917545409713)
                  ·
                    refine ⟨20247377468645938159057285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26996503291527917545409713 20247377468645938159057285)
                    ·
                      refine ⟨3796383275371113404823241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20247377468645938159057285 3796383275371113404823241)
                      ·
                        rfl

theorem cell23_7393430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7393430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393430 prefixEnd_7393430 := by exact prefixLift 7393430
  have htrace : WordTrace (prefixWord ++ tailWord_7393430) baseStart_7393430 baseEnd_7393430 := by
    simpa [prefixWord, tailWord_7393430, baseEnd_7393430] using wordTrace_append hprefix tailTrace_7393430
  have hstable : (prefixWord ++ tailWord_7393430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393430).length < 2 ^ (prefixWord ++ tailWord_7393430).sum := by decide
  have hdescent : baseEnd_7393430 < baseStart_7393430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393439 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7393439 : Nat := 118140960795 + 7393439 * 2 ^ 59
def prefixEnd_7393439 : Nat := 4983230072969 + 3 ^ 40 * 7393439 * 2
def baseEnd_7393439 : Nat := 3796387896697003869610699

theorem tailTrace_7393439 : CollatzResearch.WordTrace tailWord_7393439 prefixEnd_7393439 3796387896697003869610699 := by
  unfold tailWord_7393439
  simp only [CollatzResearch.WordTrace]
  refine ⟨269660873861840676697719371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179773915907893784465146247 269660873861840676697719371)
  ·
    refine ⟨404491310792761015046579057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269660873861840676697719371 404491310792761015046579057)
    ·
      refine ⟨303368483094570761284934293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404491310792761015046579057 303368483094570761284934293)
      ·
        refine ⟨14220397645058004435231295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303368483094570761284934293 14220397645058004435231295)
        ·
          refine ⟨21330596467587006652846943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14220397645058004435231295 21330596467587006652846943)
          ·
            refine ⟨31995894701380509979270415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330596467587006652846943 31995894701380509979270415)
            ·
              refine ⟨47993842052070764968905623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31995894701380509979270415 47993842052070764968905623)
              ·
                refine ⟨71990763078106147453358435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47993842052070764968905623 71990763078106147453358435)
                ·
                  refine ⟨107986144617159221180037653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71990763078106147453358435 107986144617159221180037653)
                  ·
                    refine ⟨5061850528929338492814265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107986144617159221180037653 5061850528929338492814265)
                    ·
                      refine ⟨3796387896697003869610699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061850528929338492814265 3796387896697003869610699)
                      ·
                        rfl

theorem cell23_7393439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7393439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393439 prefixEnd_7393439 := by exact prefixLift 7393439
  have htrace : WordTrace (prefixWord ++ tailWord_7393439) baseStart_7393439 baseEnd_7393439 := by
    simpa [prefixWord, tailWord_7393439, baseEnd_7393439] using wordTrace_append hprefix tailTrace_7393439
  have hstable : (prefixWord ++ tailWord_7393439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393439).length < 2 ^ (prefixWord ++ tailWord_7393439).sum := by decide
  have hdescent : baseEnd_7393439 < baseStart_7393439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393489 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_7393489 : Nat := 118140960795 + 7393489 * 2 ^ 59
def prefixEnd_7393489 : Nat := 4983230072969 + 3 ^ 40 * 7393489 * 2
def baseEnd_7393489 : Nat := 3796413570729728673985469

theorem tailTrace_7393489 : CollatzResearch.WordTrace tailWord_7393489 prefixEnd_7393489 3796413570729728673985469 := by
  unfold tailWord_7393489
  simp only [CollatzResearch.WordTrace]
  refine ⟨269662697511659535237039521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179775131674439690158026347 269662697511659535237039521)
  ·
    refine ⟨202247023133744651427779641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269662697511659535237039521 202247023133744651427779641)
    ·
      refine ⟨151685267350308488570834731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202247023133744651427779641 151685267350308488570834731)
      ·
        refine ⟨227527901025462732856252097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151685267350308488570834731 227527901025462732856252097)
        ·
          refine ⟨170645925769097049642189073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227527901025462732856252097 170645925769097049642189073)
          ·
            refine ⟨127984444326822787231641805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170645925769097049642189073 127984444326822787231641805)
            ·
              refine ⟨47994166622558545211865677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127984444326822787231641805 47994166622558545211865677)
              ·
                refine ⟨17997812483459454454449629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47994166622558545211865677 17997812483459454454449629)
                ·
                  refine ⟨6749179681297295420418611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17997812483459454454449629 6749179681297295420418611)
                  ·
                    refine ⟨10123769521945943130627917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749179681297295420418611 10123769521945943130627917)
                    ·
                      refine ⟨3796413570729728673985469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123769521945943130627917 3796413570729728673985469)
                      ·
                        rfl

theorem cell23_7393489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_7393489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393489 prefixEnd_7393489 := by exact prefixLift 7393489
  have htrace : WordTrace (prefixWord ++ tailWord_7393489) baseStart_7393489 baseEnd_7393489 := by
    simpa [prefixWord, tailWord_7393489, baseEnd_7393489] using wordTrace_append hprefix tailTrace_7393489
  have hstable : (prefixWord ++ tailWord_7393489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393489).length < 2 ^ (prefixWord ++ tailWord_7393489).sum := by decide
  have hdescent : baseEnd_7393489 < baseStart_7393489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393509 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_7393509 : Nat := 118140960795 + 7393509 * 2 ^ 59
def prefixEnd_7393509 : Nat := 4983230072969 + 3 ^ 40 * 7393509 * 2
def baseEnd_7393509 : Nat := 1265474613447606198578459

theorem tailTrace_7393509 : CollatzResearch.WordTrace tailWord_7393509 prefixEnd_7393509 1265474613447606198578459 := by
  unfold tailWord_7393509
  simp only [CollatzResearch.WordTrace]
  refine ⟨269663426971587078652767581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179775617981058052435178387 269663426971587078652767581)
  ·
    refine ⟨101123785114345154494787843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269663426971587078652767581 101123785114345154494787843)
    ·
      refine ⟨151685677671517731742181765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101123785114345154494787843 151685677671517731742181765)
      ·
        refine ⟨28441064563409574701659081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151685677671517731742181765 28441064563409574701659081)
        ·
          refine ⟨21330798422557181026244311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28441064563409574701659081 21330798422557181026244311)
          ·
            refine ⟨31996197633835771539366467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330798422557181026244311 31996197633835771539366467)
            ·
              refine ⟨47994296450753657309049701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31996197633835771539366467 47994296450753657309049701)
              ·
                refine ⟨8998930584516310745446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47994296450753657309049701 8998930584516310745446819)
                ·
                  refine ⟨13498395876774466118170229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998930584516310745446819 13498395876774466118170229)
                  ·
                    refine ⟨1265474613447606198578459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13498395876774466118170229 1265474613447606198578459)
                    ·
                      rfl

theorem cell23_7393509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_7393509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393509 prefixEnd_7393509 := by exact prefixLift 7393509
  have htrace : WordTrace (prefixWord ++ tailWord_7393509) baseStart_7393509 baseEnd_7393509 := by
    simpa [prefixWord, tailWord_7393509, baseEnd_7393509] using wordTrace_append hprefix tailTrace_7393509
  have hstable : (prefixWord ++ tailWord_7393509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393509).length < 2 ^ (prefixWord ++ tailWord_7393509).sum := by decide
  have hdescent : baseEnd_7393509 < baseStart_7393509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393539 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 2, 4]
def baseStart_7393539 : Nat := 118140960795 + 7393539 * 2 ^ 59
def prefixEnd_7393539 : Nat := 4983230072969 + 3 ^ 40 * 7393539 * 2
def baseEnd_7393539 : Nat := 1265479748254151159453413

theorem tailTrace_7393539 : CollatzResearch.WordTrace tailWord_7393539 prefixEnd_7393539 1265479748254151159453413 := by
  unfold tailWord_7393539
  simp only [CollatzResearch.WordTrace]
  refine ⟨269664521161478393776359671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179776347440985595850906447 269664521161478393776359671)
  ·
    refine ⟨404496781742217590664539507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269664521161478393776359671 404496781742217590664539507)
    ·
      refine ⟨606745172613326385996809261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404496781742217590664539507 606745172613326385996809261)
      ·
        refine ⟨227529439729997394748803473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606745172613326385996809261 227529439729997394748803473)
        ·
          refine ⟨170647079797498046061602605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227529439729997394748803473 170647079797498046061602605)
          ·
            refine ⟨63992654924061767273100977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170647079797498046061602605 63992654924061767273100977)
            ·
              refine ⟨47994491193046325454825733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63992654924061767273100977 47994491193046325454825733)
              ·
                refine ⟨8998967098696186022779825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47994491193046325454825733 8998967098696186022779825)
                ·
                  refine ⟨6749225324022139517084869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998967098696186022779825 6749225324022139517084869)
                  ·
                    refine ⟨1265479748254151159453413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749225324022139517084869 1265479748254151159453413)
                    ·
                      rfl

theorem cell23_7393539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 4].length) (baseStart_7393539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393539 prefixEnd_7393539 := by exact prefixLift 7393539
  have htrace : WordTrace (prefixWord ++ tailWord_7393539) baseStart_7393539 baseEnd_7393539 := by
    simpa [prefixWord, tailWord_7393539, baseEnd_7393539] using wordTrace_append hprefix tailTrace_7393539
  have hstable : (prefixWord ++ tailWord_7393539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393539).length < 2 ^ (prefixWord ++ tailWord_7393539).sum := by decide
  have hdescent : baseEnd_7393539 < baseStart_7393539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393540 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7393540 : Nat := 118140960795 + 7393540 * 2 ^ 59
def prefixEnd_7393540 : Nat := 4983230072969 + 3 ^ 40 * 7393540 * 2
def baseEnd_7393540 : Nat := 3796439758243107974447735

theorem tailTrace_7393540 : CollatzResearch.WordTrace tailWord_7393540 prefixEnd_7393540 3796439758243107974447735 := by
  unfold tailWord_7393540
  simp only [CollatzResearch.WordTrace]
  refine ⟨134832278817237385473573037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179776371756316513964764049 134832278817237385473573037)
  ·
    refine ⟨50562104556464019552589889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134832278817237385473573037 50562104556464019552589889)
    ·
      refine ⟨37921578417348014664442417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50562104556464019552589889 37921578417348014664442417)
      ·
        refine ⟨28441183813011010998331813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37921578417348014664442417 28441183813011010998331813)
        ·
          refine ⟨5332721964939564562187215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28441183813011010998331813 5332721964939564562187215)
          ·
            refine ⟨7999082947409346843280823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332721964939564562187215 7999082947409346843280823)
            ·
              refine ⟨11998624421114020264921235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999082947409346843280823 11998624421114020264921235)
              ·
                refine ⟨17997936631671030397381853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11998624421114020264921235 17997936631671030397381853)
                ·
                  refine ⟨6749226236876636399018195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17997936631671030397381853 6749226236876636399018195)
                  ·
                    refine ⟨10123839355314954598527293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749226236876636399018195 10123839355314954598527293)
                    ·
                      refine ⟨3796439758243107974447735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10123839355314954598527293 3796439758243107974447735)
                      ·
                        rfl

theorem cell23_7393540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7393540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393540 prefixEnd_7393540 := by exact prefixLift 7393540
  have htrace : WordTrace (prefixWord ++ tailWord_7393540) baseStart_7393540 baseEnd_7393540 := by
    simpa [prefixWord, tailWord_7393540, baseEnd_7393540] using wordTrace_append hprefix tailTrace_7393540
  have hstable : (prefixWord ++ tailWord_7393540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393540).length < 2 ^ (prefixWord ++ tailWord_7393540).sum := by decide
  have hdescent : baseEnd_7393540 < baseStart_7393540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393576 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7393576 : Nat := 118140960795 + 7393576 * 2 ^ 59
def prefixEnd_7393576 : Nat := 4983230072969 + 3 ^ 40 * 7393576 * 2
def baseEnd_7393576 : Nat := 3796458243546669833597569

theorem tailTrace_7393576 : CollatzResearch.WordTrace tailWord_7393576 prefixEnd_7393576 3796458243546669833597569 := by
  unfold tailWord_7393576
  simp only [CollatzResearch.WordTrace]
  refine ⟨134832935331172174547728291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179777247108229566063637721 134832935331172174547728291)
  ·
    refine ⟨202249402996758261821592437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134832935331172174547728291 202249402996758261821592437)
    ·
      refine ⟨18960881530946087045774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202249402996758261821592437 18960881530946087045774291)
      ·
        refine ⟨28441322296419130568661437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18960881530946087045774291 28441322296419130568661437)
        ·
          refine ⟨10665495861157173963248039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28441322296419130568661437 10665495861157173963248039)
          ·
            refine ⟨15998243791735760944872059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665495861157173963248039 15998243791735760944872059)
            ·
              refine ⟨23997365687603641417308089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998243791735760944872059 23997365687603641417308089)
              ·
                refine ⟨17998024265702731062981067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23997365687603641417308089 17998024265702731062981067)
                ·
                  refine ⟨26997036398554096594471601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17998024265702731062981067 26997036398554096594471601)
                  ·
                    refine ⟨20247777298915572445853701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26997036398554096594471601 20247777298915572445853701)
                    ·
                      refine ⟨3796458243546669833597569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20247777298915572445853701 3796458243546669833597569)
                      ·
                        rfl

theorem cell23_7393576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7393576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393576 prefixEnd_7393576 := by exact prefixLift 7393576
  have htrace : WordTrace (prefixWord ++ tailWord_7393576) baseStart_7393576 baseEnd_7393576 := by
    simpa [prefixWord, tailWord_7393576, baseEnd_7393576] using wordTrace_append hprefix tailTrace_7393576
  have hstable : (prefixWord ++ tailWord_7393576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393576).length < 2 ^ (prefixWord ++ tailWord_7393576).sum := by decide
  have hdescent : baseEnd_7393576 < baseStart_7393576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393592 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_7393592 : Nat := 118140960795 + 7393592 * 2 ^ 59
def prefixEnd_7393592 : Nat := 4983230072969 + 3 ^ 40 * 7393592 * 2
def baseEnd_7393592 : Nat := 3796466459237141770997495

theorem tailTrace_7393592 : CollatzResearch.WordTrace tailWord_7393592 prefixEnd_7393592 3796466459237141770997495 := by
  unfold tailWord_7393592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134833227115143191914019515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179777636153524255885359353 134833227115143191914019515)
  ·
    refine ⟨202249840672714787871029273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134833227115143191914019515 202249840672714787871029273)
    ·
      refine ⟨151687380504536090903271955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202249840672714787871029273 151687380504536090903271955)
      ·
        refine ⟨227531070756804136354907933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151687380504536090903271955 227531070756804136354907933)
        ·
          refine ⟨85324151533801551133090475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227531070756804136354907933 85324151533801551133090475)
          ·
            refine ⟨127986227300702326699635713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85324151533801551133090475 127986227300702326699635713)
            ·
              refine ⟨95989670475526745024726785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127986227300702326699635713 95989670475526745024726785)
              ·
                refine ⟨71992252856645058768545089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95989670475526745024726785 71992252856645058768545089)
                ·
                  refine ⟨53994189642483794076408817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71992252856645058768545089 53994189642483794076408817)
                  ·
                    refine ⟨40495642231862845557306613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53994189642483794076408817 40495642231862845557306613)
                    ·
                      refine ⟨3796466459237141770997495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40495642231862845557306613 3796466459237141770997495)
                      ·
                        rfl

theorem cell23_7393592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_7393592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393592 prefixEnd_7393592 := by exact prefixLift 7393592
  have htrace : WordTrace (prefixWord ++ tailWord_7393592) baseStart_7393592 baseEnd_7393592 := by
    simpa [prefixWord, tailWord_7393592, baseEnd_7393592] using wordTrace_append hprefix tailTrace_7393592
  have hstable : (prefixWord ++ tailWord_7393592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393592).length < 2 ^ (prefixWord ++ tailWord_7393592).sum := by decide
  have hdescent : baseEnd_7393592 < baseStart_7393592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393636 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_7393636 : Nat := 118140960795 + 7393636 * 2 ^ 59
def prefixEnd_7393636 : Nat := 4983230072969 + 3 ^ 40 * 7393636 * 2
def baseEnd_7393636 : Nat := 3796489052385939598847293

theorem tailTrace_7393636 : CollatzResearch.WordTrace tailWord_7393636 prefixEnd_7393636 3796489052385939598847293 := by
  unfold tailWord_7393636
  simp only [CollatzResearch.WordTrace]
  refine ⟨134834029521063489671320381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179778706028084652895093841 134834029521063489671320381)
  ·
    refine ⟨50562761070398808626745143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134834029521063489671320381 50562761070398808626745143)
    ·
      refine ⟨75844141605598212940117715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50562761070398808626745143 75844141605598212940117715)
      ·
        refine ⟨113766212408397319410176573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75844141605598212940117715 113766212408397319410176573)
        ·
          refine ⟨42662329653148994778816215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113766212408397319410176573 42662329653148994778816215)
          ·
            refine ⟨63993494479723492168224323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42662329653148994778816215 63993494479723492168224323)
            ·
              refine ⟨95990241719585238252336485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63993494479723492168224323 95990241719585238252336485)
              ·
                refine ⟨17998170322422232172313091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95990241719585238252336485 17998170322422232172313091)
                ·
                  refine ⟨26997255483633348258469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17998170322422232172313091 26997255483633348258469637)
                  ·
                    refine ⟨5061985403181252798463057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26997255483633348258469637 5061985403181252798463057)
                    ·
                      refine ⟨3796489052385939598847293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061985403181252798463057 3796489052385939598847293)
                      ·
                        rfl

theorem cell23_7393636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_7393636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393636 prefixEnd_7393636 := by exact prefixLift 7393636
  have htrace : WordTrace (prefixWord ++ tailWord_7393636) baseStart_7393636 baseEnd_7393636 := by
    simpa [prefixWord, tailWord_7393636, baseEnd_7393636] using wordTrace_append hprefix tailTrace_7393636
  have hstable : (prefixWord ++ tailWord_7393636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393636).length < 2 ^ (prefixWord ++ tailWord_7393636).sum := by decide
  have hdescent : baseEnd_7393636 < baseStart_7393636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393640 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7393640 : Nat := 118140960795 + 7393640 * 2 ^ 59
def prefixEnd_7393640 : Nat := 4983230072969 + 3 ^ 40 * 7393640 * 2
def baseEnd_7393640 : Nat := 3796491106308557583197275

theorem tailTrace_7393640 : CollatzResearch.WordTrace tailWord_7393640 prefixEnd_7393640 3796491106308557583197275 := by
  unfold tailWord_7393640
  simp only [CollatzResearch.WordTrace]
  refine ⟨134834102467056244012893187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179778803289408325350524249 134834102467056244012893187)
  ·
    refine ⟨202251153700584366019339781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134834102467056244012893187 202251153700584366019339781)
    ·
      refine ⟨37922091318859568628626209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202251153700584366019339781 37922091318859568628626209)
      ·
        refine ⟨28441568489144676471469657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37922091318859568628626209 28441568489144676471469657)
        ·
          refine ⟨21331176366858507353602243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28441568489144676471469657 21331176366858507353602243)
          ·
            refine ⟨31996764550287761030403365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21331176366858507353602243 31996764550287761030403365)
            ·
              refine ⟨5999393353178955193200631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31996764550287761030403365 5999393353178955193200631)
              ·
                refine ⟨8999090029768432789800947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999393353178955193200631 8999090029768432789800947)
                ·
                  refine ⟨13498635044652649184701421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8999090029768432789800947 13498635044652649184701421)
                  ·
                    refine ⟨5061988141744743444263033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13498635044652649184701421 5061988141744743444263033)
                    ·
                      refine ⟨3796491106308557583197275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061988141744743444263033 3796491106308557583197275)
                      ·
                        rfl

theorem cell23_7393640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7393640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393640 prefixEnd_7393640 := by exact prefixLift 7393640
  have htrace : WordTrace (prefixWord ++ tailWord_7393640) baseStart_7393640 baseEnd_7393640 := by
    simpa [prefixWord, tailWord_7393640, baseEnd_7393640] using wordTrace_append hprefix tailTrace_7393640
  have hstable : (prefixWord ++ tailWord_7393640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393640).length < 2 ^ (prefixWord ++ tailWord_7393640).sum := by decide
  have hdescent : baseEnd_7393640 < baseStart_7393640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393659 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 7]
def baseStart_7393659 : Nat := 118140960795 + 7393659 * 2 ^ 59
def prefixEnd_7393659 : Nat := 4983230072969 + 3 ^ 40 * 7393659 * 2
def baseEnd_7393659 : Nat := 421833429160110334317743

theorem tailTrace_7393659 : CollatzResearch.WordTrace tailWord_7393659 prefixEnd_7393659 421833429160110334317743 := by
  unfold tailWord_7393659
  simp only [CollatzResearch.WordTrace]
  refine ⟨269668897921043654270728031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179779265280695769513818687 269668897921043654270728031)
  ·
    refine ⟨404503346881565481406092047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269668897921043654270728031 404503346881565481406092047)
    ·
      refine ⟨606755020322348222109138071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404503346881565481406092047 606755020322348222109138071)
      ·
        refine ⟨910132530483522333163707107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606755020322348222109138071 910132530483522333163707107)
        ·
          refine ⟨1365198795725283499745560661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910132530483522333163707107 1365198795725283499745560661)
          ·
            refine ⟨15998423387405666012643289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1365198795725283499745560661 15998423387405666012643289)
            ·
              refine ⟨11998817540554249509482467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15998423387405666012643289 11998817540554249509482467)
              ·
                refine ⟨17998226310831374264223701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11998817540554249509482467 17998226310831374264223701)
                ·
                  refine ⟨421833429160110334317743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17998226310831374264223701 421833429160110334317743)
                  ·
                    rfl

theorem cell23_7393659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 7].length) (baseStart_7393659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393659 prefixEnd_7393659 := by exact prefixLift 7393659
  have htrace : WordTrace (prefixWord ++ tailWord_7393659) baseStart_7393659 baseEnd_7393659 := by
    simpa [prefixWord, tailWord_7393659, baseEnd_7393659] using wordTrace_append hprefix tailTrace_7393659
  have hstable : (prefixWord ++ tailWord_7393659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393659).length < 2 ^ (prefixWord ++ tailWord_7393659).sum := by decide
  have hdescent : baseEnd_7393659 < baseStart_7393659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393689 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_7393689 : Nat := 118140960795 + 7393689 * 2 ^ 59
def prefixEnd_7393689 : Nat := 4983230072969 + 3 ^ 40 * 7393689 * 2
def baseEnd_7393689 : Nat := 1265505422286875963828183

theorem tailTrace_7393689 : CollatzResearch.WordTrace tailWord_7393689 prefixEnd_7393689 1265505422286875963828183 := by
  unfold tailWord_7393689
  simp only [CollatzResearch.WordTrace]
  refine ⟨269669992110934969394320121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179779994740623312929546747 269669992110934969394320121)
  ·
    refine ⟨202252494083201227045740091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269669992110934969394320121 202252494083201227045740091)
    ·
      refine ⟨303378741124801840568610137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202252494083201227045740091 303378741124801840568610137)
      ·
        refine ⟨227534055843601380426457603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303378741124801840568610137 227534055843601380426457603)
        ·
          refine ⟨341301083765402070639686405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227534055843601380426457603 341301083765402070639686405)
          ·
            refine ⟨63993953206012888244941201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341301083765402070639686405 63993953206012888244941201)
            ·
              refine ⟨47995464904509666183705901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63993953206012888244941201 47995464904509666183705901)
              ·
                refine ⟨17998299339191124818889713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47995464904509666183705901 17998299339191124818889713)
                ·
                  refine ⟨13498724504393343614167285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17998299339191124818889713 13498724504393343614167285)
                  ·
                    refine ⟨1265505422286875963828183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13498724504393343614167285 1265505422286875963828183)
                    ·
                      rfl

theorem cell23_7393689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_7393689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393689 prefixEnd_7393689 := by exact prefixLift 7393689
  have htrace : WordTrace (prefixWord ++ tailWord_7393689) baseStart_7393689 baseEnd_7393689 := by
    simpa [prefixWord, tailWord_7393689, baseEnd_7393689] using wordTrace_append hprefix tailTrace_7393689
  have hstable : (prefixWord ++ tailWord_7393689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393689).length < 2 ^ (prefixWord ++ tailWord_7393689).sum := by decide
  have hdescent : baseEnd_7393689 < baseStart_7393689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393753 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 1, 4]
def baseStart_7393753 : Nat := 118140960795 + 7393753 * 2 ^ 59
def prefixEnd_7393753 : Nat := 4983230072969 + 3 ^ 40 * 7393753 * 2
def baseEnd_7393753 : Nat := 1265516376540838547028085

theorem tailTrace_7393753 : CollatzResearch.WordTrace tailWord_7393753 prefixEnd_7393753 1265516376540838547028085 := by
  unfold tailWord_7393753
  simp only [CollatzResearch.WordTrace]
  refine ⟨269672326382703108324649913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179781550921802072216433275 269672326382703108324649913)
  ·
    refine ⟨202254244787027331243487435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269672326382703108324649913 202254244787027331243487435)
    ·
      refine ⟨303381367180540996865231153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202254244787027331243487435 303381367180540996865231153)
      ·
        refine ⟨227536025385405747648923365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303381367180540996865231153 227536025385405747648923365)
        ·
          refine ⟨42663004759763577684173131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227536025385405747648923365 42663004759763577684173131)
          ·
            refine ⟨63994507139645366526259697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42663004759763577684173131 63994507139645366526259697)
            ·
              refine ⟨47995880354734024894694773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63994507139645366526259697 47995880354734024894694773)
              ·
                refine ⟨4499613783256314833877635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47995880354734024894694773 4499613783256314833877635)
                ·
                  refine ⟨6749420674884472250816453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499613783256314833877635 6749420674884472250816453)
                  ·
                    refine ⟨1265516376540838547028085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749420674884472250816453 1265516376540838547028085)
                    ·
                      rfl

theorem cell23_7393753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_7393753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393753 prefixEnd_7393753 := by exact prefixLift 7393753
  have htrace : WordTrace (prefixWord ++ tailWord_7393753) baseStart_7393753 baseEnd_7393753 := by
    simpa [prefixWord, tailWord_7393753, baseEnd_7393753] using wordTrace_append hprefix tailTrace_7393753
  have hstable : (prefixWord ++ tailWord_7393753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393753).length < 2 ^ (prefixWord ++ tailWord_7393753).sum := by decide
  have hdescent : baseEnd_7393753 < baseStart_7393753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393770 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_7393770 : Nat := 118140960795 + 7393770 * 2 ^ 59
def prefixEnd_7393770 : Nat := 4983230072969 + 3 ^ 40 * 7393770 * 2
def baseEnd_7393770 : Nat := 1265519286264547358190559

theorem tailTrace_7393770 : CollatzResearch.WordTrace tailWord_7393770 prefixEnd_7393770 1265519286264547358190559 := by
  unfold tailWord_7393770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418236605910380057004691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179781964282427680152012509 67418236605910380057004691)
  ·
    refine ⟨101127354908865570085507037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67418236605910380057004691 101127354908865570085507037)
    ·
      refine ⟨37922758090824588782065139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101127354908865570085507037 37922758090824588782065139)
      ·
        refine ⟨56884137136236883173097709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37922758090824588782065139 56884137136236883173097709)
        ·
          refine ⟨21331551426088831189911641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56884137136236883173097709 21331551426088831189911641)
          ·
            refine ⟨15998663569566623392433731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331551426088831189911641 15998663569566623392433731)
            ·
              refine ⟨23997995354349935088650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998663569566623392433731 23997995354349935088650597)
              ·
                refine ⟨4499624128940612829121987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23997995354349935088650597 4499624128940612829121987)
                ·
                  refine ⟨6749436193410919243682981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499624128940612829121987 6749436193410919243682981)
                  ·
                    refine ⟨1265519286264547358190559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749436193410919243682981 1265519286264547358190559)
                    ·
                      rfl

theorem cell23_7393770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_7393770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393770 prefixEnd_7393770 := by exact prefixLift 7393770
  have htrace : WordTrace (prefixWord ++ tailWord_7393770) baseStart_7393770 baseEnd_7393770 := by
    simpa [prefixWord, tailWord_7393770, baseEnd_7393770] using wordTrace_append hprefix tailTrace_7393770
  have hstable : (prefixWord ++ tailWord_7393770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393770).length < 2 ^ (prefixWord ++ tailWord_7393770).sum := by decide
  have hdescent : baseEnd_7393770 < baseStart_7393770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393779 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 5, 5]
def baseStart_7393779 : Nat := 118140960795 + 7393779 * 2 ^ 59
def prefixEnd_7393779 : Nat := 4983230072969 + 3 ^ 40 * 7393779 * 2
def baseEnd_7393779 : Nat := 1265520826706510846453045

theorem tailTrace_7393779 : CollatzResearch.WordTrace tailWord_7393779 prefixEnd_7393779 1265520826706510846453045 := by
  unfold tailWord_7393779
  simp only [CollatzResearch.WordTrace]
  refine ⟨269673274680608914765096391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179782183120405943176730927 269673274680608914765096391)
  ·
    refine ⟨404509912020913372147644587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269673274680608914765096391 404509912020913372147644587)
    ·
      refine ⟨606764868031370058221466881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404509912020913372147644587 606764868031370058221466881)
      ·
        refine ⟨455073651023527543666100161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606764868031370058221466881 455073651023527543666100161)
        ·
          refine ⟨341305238267645657749575121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455073651023527543666100161 341305238267645657749575121)
          ·
            refine ⟨255978928700734243312181341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341305238267645657749575121 255978928700734243312181341)
            ·
              refine ⟨95992098262775341242068003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255978928700734243312181341 95992098262775341242068003)
              ·
                refine ⟨143988147394163011863102005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95992098262775341242068003 143988147394163011863102005)
                ·
                  refine ⟨13498888818202782362165813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143988147394163011863102005 13498888818202782362165813)
                  ·
                    refine ⟨1265520826706510846453045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13498888818202782362165813 1265520826706510846453045)
                    ·
                      rfl

theorem cell23_7393779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].length) (baseStart_7393779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393779 prefixEnd_7393779 := by exact prefixLift 7393779
  have htrace : WordTrace (prefixWord ++ tailWord_7393779) baseStart_7393779 baseEnd_7393779 := by
    simpa [prefixWord, tailWord_7393779, baseEnd_7393779] using wordTrace_append hprefix tailTrace_7393779
  have hstable : (prefixWord ++ tailWord_7393779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393779).length < 2 ^ (prefixWord ++ tailWord_7393779).sum := by decide
  have hdescent : baseEnd_7393779 < baseStart_7393779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393789 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7393789 : Nat := 118140960795 + 7393789 * 2 ^ 59
def prefixEnd_7393789 : Nat := 4983230072969 + 3 ^ 40 * 7393789 * 2
def baseEnd_7393789 : Nat := 3796567614926077500234089

theorem tailTrace_7393789 : CollatzResearch.WordTrace tailWord_7393789 prefixEnd_7393789 3796567614926077500234089 := by
  unfold tailWord_7393789
  simp only [CollatzResearch.WordTrace]
  refine ⟨269673639410572686472960421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179782426273715124315306947 269673639410572686472960421)
  ·
    refine ⟨50563807389482378713680079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269673639410572686472960421 50563807389482378713680079)
    ·
      refine ⟨75845711084223568070520119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50563807389482378713680079 75845711084223568070520119)
      ·
        refine ⟨113768566626335352105780179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75845711084223568070520119 113768566626335352105780179)
        ·
          refine ⟨170652849939503028158670269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113768566626335352105780179 170652849939503028158670269)
          ·
            refine ⟨63994818727313635559501351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170652849939503028158670269 63994818727313635559501351)
            ·
              refine ⟨95992228090970453339252027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63994818727313635559501351 95992228090970453339252027)
              ·
                refine ⟨143988342136455680008878041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95992228090970453339252027 143988342136455680008878041)
                ·
                  refine ⟨107991256602341760006658531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143988342136455680008878041 107991256602341760006658531)
                  ·
                    refine ⟨161986884903512640009987797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107991256602341760006658531 161986884903512640009987797)
                    ·
                      refine ⟨3796567614926077500234089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161986884903512640009987797 3796567614926077500234089)
                      ·
                        rfl

theorem cell23_7393789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7393789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393789 prefixEnd_7393789 := by exact prefixLift 7393789
  have htrace : WordTrace (prefixWord ++ tailWord_7393789) baseStart_7393789 baseEnd_7393789 := by
    simpa [prefixWord, tailWord_7393789, baseEnd_7393789] using wordTrace_append hprefix tailTrace_7393789
  have hstable : (prefixWord ++ tailWord_7393789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393789).length < 2 ^ (prefixWord ++ tailWord_7393789).sum := by decide
  have hdescent : baseEnd_7393789 < baseStart_7393789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393793 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_7393793 : Nat := 118140960795 + 7393793 * 2 ^ 59
def prefixEnd_7393793 : Nat := 4983230072969 + 3 ^ 40 * 7393793 * 2
def baseEnd_7393793 : Nat := 3796569668848695484584071

theorem tailTrace_7393793 : CollatzResearch.WordTrace tailWord_7393793 prefixEnd_7393793 3796569668848695484584071 := by
  unfold tailWord_7393793
  simp only [CollatzResearch.WordTrace]
  refine ⟨269673785302558195156106033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179782523535038796770737355 269673785302558195156106033)
  ·
    refine ⟨202255338976918646367079525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269673785302558195156106033 202255338976918646367079525)
    ·
      refine ⟨37922876058172246193827411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202255338976918646367079525 37922876058172246193827411)
      ·
        refine ⟨56884314087258369290741117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37922876058172246193827411 56884314087258369290741117)
        ·
          refine ⟨21331617782721888484027919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56884314087258369290741117 21331617782721888484027919)
          ·
            refine ⟨31997426674082832726041879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21331617782721888484027919 31997426674082832726041879)
            ·
              refine ⟨47996140011124249089062819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31997426674082832726041879 47996140011124249089062819)
              ·
                refine ⟨71994210016686373633594229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47996140011124249089062819 71994210016686373633594229)
                ·
                  refine ⟨6749457189064347528149459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71994210016686373633594229 6749457189064347528149459)
                  ·
                    refine ⟨10124185783596521292224189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749457189064347528149459 10124185783596521292224189)
                    ·
                      refine ⟨3796569668848695484584071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10124185783596521292224189 3796569668848695484584071)
                      ·
                        rfl

theorem cell23_7393793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_7393793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393793 prefixEnd_7393793 := by exact prefixLift 7393793
  have htrace : WordTrace (prefixWord ++ tailWord_7393793) baseStart_7393793 baseEnd_7393793 := by
    simpa [prefixWord, tailWord_7393793, baseEnd_7393793] using wordTrace_append hprefix tailTrace_7393793
  have hstable : (prefixWord ++ tailWord_7393793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393793).length < 2 ^ (prefixWord ++ tailWord_7393793).sum := by decide
  have hdescent : baseEnd_7393793 < baseStart_7393793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393803 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 5, 2]
def baseStart_7393803 : Nat := 118140960795 + 7393803 * 2 ^ 59
def prefixEnd_7393803 : Nat := 4983230072969 + 3 ^ 40 * 7393803 * 2
def baseEnd_7393803 : Nat := 3796574803655240445459025

theorem tailTrace_7393803 : CollatzResearch.WordTrace tailWord_7393803 prefixEnd_7393803 3796574803655240445459025 := by
  unfold tailWord_7393803
  simp only [CollatzResearch.WordTrace]
  refine ⟨269674150032521966863970063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179782766688347977909313375 269674150032521966863970063)
  ·
    refine ⟨404511225048782950295955095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269674150032521966863970063 404511225048782950295955095)
    ·
      refine ⟨606766837573174425443932643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404511225048782950295955095 606766837573174425443932643)
      ·
        refine ⟨910150256359761638165898965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606766837573174425443932643 910150256359761638165898965)
        ·
          refine ⟨21331646633431913394513257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 910150256359761638165898965 21331646633431913394513257)
          ·
            refine ⟨15998734975073935045884943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331646633431913394513257 15998734975073935045884943)
            ·
              refine ⟨23998102462610902568827415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998734975073935045884943 23998102462610902568827415)
              ·
                refine ⟨35997153693916353853241123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23998102462610902568827415 35997153693916353853241123)
                ·
                  refine ⟨53995730540874530779861685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35997153693916353853241123 53995730540874530779861685)
                  ·
                    refine ⟨5062099738206987260612033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53995730540874530779861685 5062099738206987260612033)
                    ·
                      refine ⟨3796574803655240445459025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062099738206987260612033 3796574803655240445459025)
                      ·
                        rfl

theorem cell23_7393803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5, 2].length) (baseStart_7393803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393803 prefixEnd_7393803 := by exact prefixLift 7393803
  have htrace : WordTrace (prefixWord ++ tailWord_7393803) baseStart_7393803 baseEnd_7393803 := by
    simpa [prefixWord, tailWord_7393803, baseEnd_7393803] using wordTrace_append hprefix tailTrace_7393803
  have hstable : (prefixWord ++ tailWord_7393803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393803).length < 2 ^ (prefixWord ++ tailWord_7393803).sum := by decide
  have hdescent : baseEnd_7393803 < baseStart_7393803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393809 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_7393809 : Nat := 118140960795 + 7393809 * 2 ^ 59
def prefixEnd_7393809 : Nat := 4983230072969 + 3 ^ 40 * 7393809 * 2
def baseEnd_7393809 : Nat := 1265525961513055807327999

theorem tailTrace_7393809 : CollatzResearch.WordTrace tailWord_7393809 prefixEnd_7393809 1265525961513055807327999 := by
  unfold tailWord_7393809
  simp only [CollatzResearch.WordTrace]
  refine ⟨269674368870500229888688481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179782912580333486592458987 269674368870500229888688481)
  ·
    refine ⟨202255776652875172416516361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269674368870500229888688481 202255776652875172416516361)
    ·
      refine ⟨151691832489656379312387271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202255776652875172416516361 151691832489656379312387271)
      ·
        refine ⟨227537748734484568968580907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151691832489656379312387271 227537748734484568968580907)
        ·
          refine ⟨341306623101726853452871361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227537748734484568968580907 341306623101726853452871361)
          ·
            refine ⟨255979967326295140089653521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341306623101726853452871361 255979967326295140089653521)
            ·
              refine ⟨191984975494721355067240141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255979967326295140089653521 191984975494721355067240141)
              ·
                refine ⟨71994365810520508150215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191984975494721355067240141 71994365810520508150215053)
                ·
                  refine ⟨26997887178945190556330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71994365810520508150215053 26997887178945190556330645)
                  ·
                    refine ⟨1265525961513055807327999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26997887178945190556330645 1265525961513055807327999)
                    ·
                      rfl

theorem cell23_7393809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_7393809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393809 prefixEnd_7393809 := by exact prefixLift 7393809
  have htrace : WordTrace (prefixWord ++ tailWord_7393809) baseStart_7393809 baseEnd_7393809 := by
    simpa [prefixWord, tailWord_7393809, baseEnd_7393809] using wordTrace_append hprefix tailTrace_7393809
  have hstable : (prefixWord ++ tailWord_7393809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393809).length < 2 ^ (prefixWord ++ tailWord_7393809).sum := by decide
  have hdescent : baseEnd_7393809 < baseStart_7393809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393819 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_7393819 : Nat := 118140960795 + 7393819 * 2 ^ 59
def prefixEnd_7393819 : Nat := 4983230072969 + 3 ^ 40 * 7393819 * 2
def baseEnd_7393819 : Nat := 3796583019345712382858951

theorem tailTrace_7393819 : CollatzResearch.WordTrace tailWord_7393819 prefixEnd_7393819 3796583019345712382858951 := by
  unfold tailWord_7393819
  simp only [CollatzResearch.WordTrace]
  refine ⟨269674733600464001596552511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179783155733642667731035007 269674733600464001596552511)
  ·
    refine ⟨404512100400696002394828767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269674733600464001596552511 404512100400696002394828767)
    ·
      refine ⟨606768150601044003592243151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404512100400696002394828767 606768150601044003592243151)
      ·
        refine ⟨910152225901566005388364727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606768150601044003592243151 910152225901566005388364727)
        ·
          refine ⟨1365228338852349008082547091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910152225901566005388364727 1365228338852349008082547091)
          ·
            refine ⟨2047842508278523512123820637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365228338852349008082547091 2047842508278523512123820637)
            ·
              refine ⟨767940940604446317046432739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2047842508278523512123820637 767940940604446317046432739)
              ·
                refine ⟨1151911410906669475569649109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767940940604446317046432739 1151911410906669475569649109)
                ·
                  refine ⟨26997923693125065833663651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1151911410906669475569649109 26997923693125065833663651)
                  ·
                    refine ⟨40496885539687598750495477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26997923693125065833663651 40496885539687598750495477)
                    ·
                      refine ⟨3796583019345712382858951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40496885539687598750495477 3796583019345712382858951)
                      ·
                        rfl

theorem cell23_7393819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_7393819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393819 prefixEnd_7393819 := by exact prefixLift 7393819
  have htrace : WordTrace (prefixWord ++ tailWord_7393819) baseStart_7393819 baseEnd_7393819 := by
    simpa [prefixWord, tailWord_7393819, baseEnd_7393819] using wordTrace_append hprefix tailTrace_7393819
  have hstable : (prefixWord ++ tailWord_7393819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393819).length < 2 ^ (prefixWord ++ tailWord_7393819).sum := by decide
  have hdescent : baseEnd_7393819 < baseStart_7393819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393836 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_7393836 : Nat := 118140960795 + 7393836 * 2 ^ 59
def prefixEnd_7393836 : Nat := 4983230072969 + 3 ^ 40 * 7393836 * 2
def baseEnd_7393836 : Nat := 3796591748516838816346373

theorem tailTrace_7393836 : CollatzResearch.WordTrace tailWord_7393836 prefixEnd_7393836 3796591748516838816346373 := by
  unfold tailWord_7393836
  simp only [CollatzResearch.WordTrace]
  refine ⟨134837676820701206749960681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179783569094268275666614241 134837676820701206749960681)
  ·
    refine ⟨101128257615525905062470511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134837676820701206749960681 101128257615525905062470511)
    ·
      refine ⟨151692386423288857593705767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101128257615525905062470511 151692386423288857593705767)
      ·
        refine ⟨227538579634933286390558651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151692386423288857593705767 227538579634933286390558651)
        ·
          refine ⟨341307869452399929585837977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227538579634933286390558651 341307869452399929585837977)
          ·
            refine ⟨255980902089299947189378483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341307869452399929585837977 255980902089299947189378483)
            ·
              refine ⟨383971353133949920784067725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255980902089299947189378483 383971353133949920784067725)
              ·
                refine ⟨143989257425231220294025397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383971353133949920784067725 143989257425231220294025397)
                ·
                  refine ⟨13498992883615426902564881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143989257425231220294025397 13498992883615426902564881)
                  ·
                    refine ⟨10124244662711570176923661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13498992883615426902564881 10124244662711570176923661)
                    ·
                      refine ⟨3796591748516838816346373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10124244662711570176923661 3796591748516838816346373)
                      ·
                        rfl

theorem cell23_7393836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_7393836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393836 prefixEnd_7393836 := by exact prefixLift 7393836
  have htrace : WordTrace (prefixWord ++ tailWord_7393836) baseStart_7393836 baseEnd_7393836 := by
    simpa [prefixWord, tailWord_7393836, baseEnd_7393836] using wordTrace_append hprefix tailTrace_7393836
  have hstable : (prefixWord ++ tailWord_7393836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393836).length < 2 ^ (prefixWord ++ tailWord_7393836).sum := by decide
  have hdescent : baseEnd_7393836 < baseStart_7393836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393850 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_7393850 : Nat := 118140960795 + 7393850 * 2 ^ 59
def prefixEnd_7393850 : Nat := 4983230072969 + 3 ^ 40 * 7393850 * 2
def baseEnd_7393850 : Nat := 3796598937246001761571309

theorem tailTrace_7393850 : CollatzResearch.WordTrace tailWord_7393850 prefixEnd_7393850 3796598937246001761571309 := by
  unfold tailWord_7393850
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418966065837923472732751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179783909508901129260620669 67418966065837923472732751)
  ·
    refine ⟨101128449098756885209099127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67418966065837923472732751 101128449098756885209099127)
    ·
      refine ⟨151692673648135327813648691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101128449098756885209099127 151692673648135327813648691)
      ·
        refine ⟨227539010472202991720473037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151692673648135327813648691 227539010472202991720473037)
        ·
          refine ⟨85327128927076121895177389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227539010472202991720473037 85327128927076121895177389)
          ·
            refine ⟨31997673347653545710691521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85327128927076121895177389 31997673347653545710691521)
            ·
              refine ⟨23998255010740159283018641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31997673347653545710691521 23998255010740159283018641)
              ·
                refine ⟨17998691258055119462263981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23998255010740159283018641 17998691258055119462263981)
                ·
                  refine ⟨6749509221770669798348993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17998691258055119462263981 6749509221770669798348993)
                  ·
                    refine ⟨5062131916328002348761745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749509221770669798348993 5062131916328002348761745)
                    ·
                      refine ⟨3796598937246001761571309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062131916328002348761745 3796598937246001761571309)
                      ·
                        rfl

theorem cell23_7393850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_7393850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393850 prefixEnd_7393850 := by exact prefixLift 7393850
  have htrace : WordTrace (prefixWord ++ tailWord_7393850) baseStart_7393850 baseEnd_7393850 := by
    simpa [prefixWord, tailWord_7393850, baseEnd_7393850] using wordTrace_append hprefix tailTrace_7393850
  have hstable : (prefixWord ++ tailWord_7393850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393850).length < 2 ^ (prefixWord ++ tailWord_7393850).sum := by decide
  have hdescent : baseEnd_7393850 < baseStart_7393850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393856 : List Nat := [2, 1, 1, 2, 2, 2, 6, 7]
def baseStart_7393856 : Nat := 118140960795 + 7393856 * 2 ^ 59
def prefixEnd_7393856 : Nat := 4983230072969 + 3 ^ 40 * 7393856 * 2
def baseEnd_7393856 : Nat := 140614889560367731040603

theorem tailTrace_7393856 : CollatzResearch.WordTrace tailWord_7393856 prefixEnd_7393856 140614889560367731040603 := by
  unfold tailWord_7393856
  simp only [CollatzResearch.WordTrace]
  refine ⟨134838041550664978457824711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179784055400886637943766281 134838041550664978457824711)
  ·
    refine ⟨202257062325997467686737067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134838041550664978457824711 202257062325997467686737067)
    ·
      refine ⟨303385593488996201530105601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202257062325997467686737067 303385593488996201530105601)
      ·
        refine ⟨227539195116747151147579201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303385593488996201530105601 227539195116747151147579201)
        ·
          refine ⟨170654396337560363360684401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227539195116747151147579201 170654396337560363360684401)
          ·
            refine ⟨127990797253170272520513301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170654396337560363360684401 127990797253170272520513301)
            ·
              refine ⟨5999568621242356524399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127990797253170272520513301 5999568621242356524399061)
              ·
                refine ⟨140614889560367731040603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5999568621242356524399061 140614889560367731040603)
                ·
                  rfl

theorem cell23_7393856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 7].length) (baseStart_7393856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393856 prefixEnd_7393856 := by exact prefixLift 7393856
  have htrace : WordTrace (prefixWord ++ tailWord_7393856) baseStart_7393856 baseEnd_7393856 := by
    simpa [prefixWord, tailWord_7393856, baseEnd_7393856] using wordTrace_append hprefix tailTrace_7393856
  have hstable : (prefixWord ++ tailWord_7393856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393856).length < 2 ^ (prefixWord ++ tailWord_7393856).sum := by decide
  have hdescent : baseEnd_7393856 < baseStart_7393856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_7393859 : Nat := 118140960795 + 7393859 * 2 ^ 59
def prefixEnd_7393859 : Nat := 4983230072969 + 3 ^ 40 * 7393859 * 2
def baseEnd_7393859 : Nat := 3796603558571892226358767

theorem tailTrace_7393859 : CollatzResearch.WordTrace tailWord_7393859 prefixEnd_7393859 3796603558571892226358767 := by
  unfold tailWord_7393859
  simp only [CollatzResearch.WordTrace]
  refine ⟨269676192520319088428008631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179784128346879392285339087 269676192520319088428008631)
  ·
    refine ⟨404514288780478632642012947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269676192520319088428008631 404514288780478632642012947)
    ·
      refine ⟨606771433170717948963019421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404514288780478632642012947 606771433170717948963019421)
      ·
        refine ⟨227539287439019230861132283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606771433170717948963019421 227539287439019230861132283)
        ·
          refine ⟨341308931158528846291698425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227539287439019230861132283 341308931158528846291698425)
          ·
            refine ⟨255981698368896634718773819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341308931158528846291698425 255981698368896634718773819)
            ·
              refine ⟨383972547553344952078160729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255981698368896634718773819 383972547553344952078160729)
              ·
                refine ⟨287979410665008714058620547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383972547553344952078160729 287979410665008714058620547)
                ·
                  refine ⟨431969115997513071087930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287979410665008714058620547 431969115997513071087930821)
                  ·
                    refine ⟨80994209249533700828987029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431969115997513071087930821 80994209249533700828987029)
                    ·
                      refine ⟨3796603558571892226358767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80994209249533700828987029 3796603558571892226358767)
                      ·
                        rfl

theorem cell23_7393859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_7393859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393859 prefixEnd_7393859 := by exact prefixLift 7393859
  have htrace : WordTrace (prefixWord ++ tailWord_7393859) baseStart_7393859 baseEnd_7393859 := by
    simpa [prefixWord, tailWord_7393859, baseEnd_7393859] using wordTrace_append hprefix tailTrace_7393859
  have hstable : (prefixWord ++ tailWord_7393859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393859).length < 2 ^ (prefixWord ++ tailWord_7393859).sum := by decide
  have hdescent : baseEnd_7393859 < baseStart_7393859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393867 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 1, 2, 2]
def baseStart_7393867 : Nat := 118140960795 + 7393867 * 2 ^ 59
def prefixEnd_7393867 : Nat := 4983230072969 + 3 ^ 40 * 7393867 * 2
def baseEnd_7393867 : Nat := 3796607666417128195058731

theorem tailTrace_7393867 : CollatzResearch.WordTrace tailWord_7393867 prefixEnd_7393867 3796607666417128195058731 := by
  unfold tailWord_7393867
  simp only [CollatzResearch.WordTrace]
  refine ⟨269676484304290105794299855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179784322869526737196199903 269676484304290105794299855)
  ·
    refine ⟨404514726456435158691449783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269676484304290105794299855 404514726456435158691449783)
    ·
      refine ⟨606772089684652738037174675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404514726456435158691449783 606772089684652738037174675)
      ·
        refine ⟨910158134526979107055762013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606772089684652738037174675 910158134526979107055762013)
        ·
          refine ⟨341309300447617165145910755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910158134526979107055762013 341309300447617165145910755)
          ·
            refine ⟨511963950671425747718866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341309300447617165145910755 511963950671425747718866133)
            ·
              refine ⟨11999155093861540962160925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 511963950671425747718866133 11999155093861540962160925)
              ·
                refine ⟨4499683160198077860810347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11999155093861540962160925 4499683160198077860810347)
                ·
                  refine ⟨6749524740297116791215521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499683160198077860810347 6749524740297116791215521)
                  ·
                    refine ⟨5062143555222837593411641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749524740297116791215521 5062143555222837593411641)
                    ·
                      refine ⟨3796607666417128195058731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062143555222837593411641 3796607666417128195058731)
                      ·
                        rfl

theorem cell23_7393867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 2, 2].length) (baseStart_7393867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393867 prefixEnd_7393867 := by exact prefixLift 7393867
  have htrace : WordTrace (prefixWord ++ tailWord_7393867) baseStart_7393867 baseEnd_7393867 := by
    simpa [prefixWord, tailWord_7393867, baseEnd_7393867] using wordTrace_append hprefix tailTrace_7393867
  have hstable : (prefixWord ++ tailWord_7393867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393867).length < 2 ^ (prefixWord ++ tailWord_7393867).sum := by decide
  have hdescent : baseEnd_7393867 < baseStart_7393867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393884 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7393884 : Nat := 118140960795 + 7393884 * 2 ^ 59
def prefixEnd_7393884 : Nat := 4983230072969 + 3 ^ 40 * 7393884 * 2
def baseEnd_7393884 : Nat := 3796616395588254628546153

theorem tailTrace_7393884 : CollatzResearch.WordTrace tailWord_7393884 prefixEnd_7393884 3796616395588254628546153 := by
  unfold tailWord_7393884
  simp only [CollatzResearch.WordTrace]
  refine ⟨134838552172614258848834353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179784736230152345131779137 134838552172614258848834353)
  ·
    refine ⟨101128914129460694136625765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134838552172614258848834353 101128914129460694136625765)
    ·
      refine ⟨18961671399273880150617331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101128914129460694136625765 18961671399273880150617331)
      ·
        refine ⟨28442507098910820225925997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18961671399273880150617331 28442507098910820225925997)
        ·
          refine ⟨10665940162091557584722249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28442507098910820225925997 10665940162091557584722249)
          ·
            refine ⟨7999455121568668188541687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10665940162091557584722249 7999455121568668188541687)
            ·
              refine ⟨11999182682353002282812531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999455121568668188541687 11999182682353002282812531)
              ·
                refine ⟨17998774023529503424218797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11999182682353002282812531 17998774023529503424218797)
                ·
                  refine ⟨6749540258823563784082049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17998774023529503424218797 6749540258823563784082049)
                  ·
                    refine ⟨5062155194117672838061537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749540258823563784082049 5062155194117672838061537)
                    ·
                      refine ⟨3796616395588254628546153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062155194117672838061537 3796616395588254628546153)
                      ·
                        rfl

theorem cell23_7393884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7393884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393884 prefixEnd_7393884 := by exact prefixLift 7393884
  have htrace : WordTrace (prefixWord ++ tailWord_7393884) baseStart_7393884 baseEnd_7393884 := by
    simpa [prefixWord, tailWord_7393884, baseEnd_7393884] using wordTrace_append hprefix tailTrace_7393884
  have hstable : (prefixWord ++ tailWord_7393884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393884).length < 2 ^ (prefixWord ++ tailWord_7393884).sum := by decide
  have hdescent : baseEnd_7393884 < baseStart_7393884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393890 : List Nat := [3, 3, 2, 3, 1, 1, 2, 8]
def baseStart_7393890 : Nat := 118140960795 + 7393890 * 2 ^ 59
def prefixEnd_7393890 : Nat := 4983230072969 + 3 ^ 40 * 7393890 * 2
def baseEnd_7393890 : Nat := 140615536165636355743375

theorem tailTrace_7393890 : CollatzResearch.WordTrace tailWord_7393890 prefixEnd_7393890 140615536165636355743375 := by
  unfold tailWord_7393890
  simp only [CollatzResearch.WordTrace]
  refine ⟨67419330795801695180596781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179784882122137853814924749 67419330795801695180596781)
  ·
    refine ⟨25282249048425635692723793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67419330795801695180596781 25282249048425635692723793)
    ·
      refine ⟨18961686786319226769542845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25282249048425635692723793 18961686786319226769542845)
      ·
        refine ⟨7110632544869710038578567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18961686786319226769542845 7110632544869710038578567)
        ·
          refine ⟨10665948817304565057867851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110632544869710038578567 10665948817304565057867851)
          ·
            refine ⟨15998923225956847586801777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665948817304565057867851 15998923225956847586801777)
            ·
              refine ⟨11999192419467635690101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15998923225956847586801777 11999192419467635690101333)
              ·
                refine ⟨140615536165636355743375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11999192419467635690101333 140615536165636355743375)
                ·
                  rfl

theorem cell23_7393890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_7393890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393890 prefixEnd_7393890 := by exact prefixLift 7393890
  have htrace : WordTrace (prefixWord ++ tailWord_7393890) baseStart_7393890 baseEnd_7393890 := by
    simpa [prefixWord, tailWord_7393890, baseEnd_7393890] using wordTrace_append hprefix tailTrace_7393890
  have hstable : (prefixWord ++ tailWord_7393890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393890).length < 2 ^ (prefixWord ++ tailWord_7393890).sum := by decide
  have hdescent : baseEnd_7393890 < baseStart_7393890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393923 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 4, 2]
def baseStart_7393923 : Nat := 118140960795 + 7393923 * 2 ^ 59
def prefixEnd_7393923 : Nat := 4983230072969 + 3 ^ 40 * 7393923 * 2
def baseEnd_7393923 : Nat := 3796636421333779975958473

theorem tailTrace_7393923 : CollatzResearch.WordTrace tailWord_7393923 prefixEnd_7393923 3796636421333779975958473 := by
  unfold tailWord_7393923
  simp only [CollatzResearch.WordTrace]
  refine ⟨269678526792087227358338423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179785684528058151572225615 269678526792087227358338423)
  ·
    refine ⟨404517790188130841037507635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269678526792087227358338423 404517790188130841037507635)
    ·
      refine ⟨606776685282196261556261453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404517790188130841037507635 606776685282196261556261453)
      ·
        refine ⟨227541256980823598083598045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606776685282196261556261453 227541256980823598083598045)
        ·
          refine ⟨85327971367808849281349267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227541256980823598083598045 85327971367808849281349267)
          ·
            refine ⟨127991957051713273922023901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85327971367808849281349267 127991957051713273922023901)
            ·
              refine ⟨47996983894392477720758963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127991957051713273922023901 47996983894392477720758963)
              ·
                refine ⟨71995475841588716581138445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47996983894392477720758963 71995475841588716581138445)
                ·
                  refine ⟨26998303440595768717926917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71995475841588716581138445 26998303440595768717926917)
                  ·
                    refine ⟨5062181895111706634611297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26998303440595768717926917 5062181895111706634611297)
                    ·
                      refine ⟨3796636421333779975958473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062181895111706634611297 3796636421333779975958473)
                      ·
                        rfl

theorem cell23_7393923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_7393923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393923 prefixEnd_7393923 := by exact prefixLift 7393923
  have htrace : WordTrace (prefixWord ++ tailWord_7393923) baseStart_7393923 baseEnd_7393923 := by
    simpa [prefixWord, tailWord_7393923, baseEnd_7393923] using wordTrace_append hprefix tailTrace_7393923
  have hstable : (prefixWord ++ tailWord_7393923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393923).length < 2 ^ (prefixWord ++ tailWord_7393923).sum := by decide
  have hdescent : baseEnd_7393923 < baseStart_7393923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393927 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_7393927 : Nat := 118140960795 + 7393927 * 2 ^ 59
def prefixEnd_7393927 : Nat := 4983230072969 + 3 ^ 40 * 7393927 * 2
def baseEnd_7393927 : Nat := 3796638475256397960308455

theorem tailTrace_7393927 : CollatzResearch.WordTrace tailWord_7393927 prefixEnd_7393927 3796638475256397960308455 := by
  unfold tailWord_7393927
  simp only [CollatzResearch.WordTrace]
  refine ⟨269678672684072736041484035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179785781789381824027656023 269678672684072736041484035)
  ·
    refine ⟨404518009026109104062226053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269678672684072736041484035 404518009026109104062226053)
    ·
      refine ⟨75847126692395457011667385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404518009026109104062226053 75847126692395457011667385)
      ·
        refine ⟨56885345019296592758750539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75847126692395457011667385 56885345019296592758750539)
        ·
          refine ⟨85328017528944889138125809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56885345019296592758750539 85328017528944889138125809)
          ·
            refine ⟨63996013146708666853594357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85328017528944889138125809 63996013146708666853594357)
            ·
              refine ⟨5999626232503937517524471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63996013146708666853594357 5999626232503937517524471)
              ·
                refine ⟨8999439348755906276286707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999626232503937517524471 8999439348755906276286707)
                ·
                  refine ⟨13499159023133859414430061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8999439348755906276286707 13499159023133859414430061)
                  ·
                    refine ⟨5062184633675197280411273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13499159023133859414430061 5062184633675197280411273)
                    ·
                      refine ⟨3796638475256397960308455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062184633675197280411273 3796638475256397960308455)
                      ·
                        rfl

theorem cell23_7393927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_7393927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393927 prefixEnd_7393927 := by exact prefixLift 7393927
  have htrace : WordTrace (prefixWord ++ tailWord_7393927) baseStart_7393927 baseEnd_7393927 := by
    simpa [prefixWord, tailWord_7393927, baseEnd_7393927] using wordTrace_append hprefix tailTrace_7393927
  have hstable : (prefixWord ++ tailWord_7393927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393927).length < 2 ^ (prefixWord ++ tailWord_7393927).sum := by decide
  have hdescent : baseEnd_7393927 < baseStart_7393927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393980 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 5]
def baseStart_7393980 : Nat := 118140960795 + 7393980 * 2 ^ 59
def prefixEnd_7393980 : Nat := 4983230072969 + 3 ^ 40 * 7393980 * 2
def baseEnd_7393980 : Nat := 421851743303454028105079

theorem tailTrace_7393980 : CollatzResearch.WordTrace tailWord_7393980 prefixEnd_7393980 421851743303454028105079 := by
  unfold tailWord_7393980
  simp only [CollatzResearch.WordTrace]
  refine ⟨134840302876440363046581697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179787070501920484062108929 134840302876440363046581697)
  ·
    refine ⟨101130227157330272284936273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134840302876440363046581697 101130227157330272284936273)
    ·
      refine ⟨75847670367997704213702205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101130227157330272284936273 75847670367997704213702205)
      ·
        refine ⟨28442876387999139080138327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75847670367997704213702205 28442876387999139080138327)
        ·
          refine ⟨42664314581998708620207491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28442876387999139080138327 42664314581998708620207491)
          ·
            refine ⟨63996471872998062930311237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42664314581998708620207491 63996471872998062930311237)
            ·
              refine ⟨11999338476187136799433357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63996471872998062930311237 11999338476187136799433357)
              ·
                refine ⟨4499751928570176299787509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11999338476187136799433357 4499751928570176299787509)
                ·
                  refine ⟨421851743303454028105079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4499751928570176299787509 421851743303454028105079)
                  ·
                    rfl

theorem cell23_7393980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_7393980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393980 prefixEnd_7393980 := by exact prefixLift 7393980
  have htrace : WordTrace (prefixWord ++ tailWord_7393980) baseStart_7393980 baseEnd_7393980 := by
    simpa [prefixWord, tailWord_7393980, baseEnd_7393980] using wordTrace_append hprefix tailTrace_7393980
  have hstable : (prefixWord ++ tailWord_7393980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393980).length < 2 ^ (prefixWord ++ tailWord_7393980).sum := by decide
  have hdescent : baseEnd_7393980 < baseStart_7393980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7393997 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 7]
def baseStart_7393997 : Nat := 118140960795 + 7393997 * 2 ^ 59
def prefixEnd_7393997 : Nat := 4983230072969 + 3 ^ 40 * 7393997 * 2
def baseEnd_7393997 : Nat := 421852713211356965159237

theorem tailTrace_7393997 : CollatzResearch.WordTrace tailWord_7393997 prefixEnd_7393997 421852713211356965159237 := by
  unfold tailWord_7393997
  simp only [CollatzResearch.WordTrace]
  refine ⟨269681225793819137996532245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179787483862546091997688163 269681225793819137996532245)
  ·
    refine ⟨12641307459085272093587449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269681225793819137996532245 12641307459085272093587449)
    ·
      refine ⟨9480980594313954070190587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12641307459085272093587449 9480980594313954070190587)
      ·
        refine ⟨14221470891470931105285881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480980594313954070190587 14221470891470931105285881)
        ·
          refine ⟨10666103168603198328964411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14221470891470931105285881 10666103168603198328964411)
          ·
            refine ⟨15999154752904797493446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666103168603198328964411 15999154752904797493446617)
            ·
              refine ⟨11999366064678598120084963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15999154752904797493446617 11999366064678598120084963)
              ·
                refine ⟨17999049097017897180127445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11999366064678598120084963 17999049097017897180127445)
                ·
                  refine ⟨421852713211356965159237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17999049097017897180127445 421852713211356965159237)
                  ·
                    rfl

theorem cell23_7393997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_7393997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7393997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7393997 prefixEnd_7393997 := by exact prefixLift 7393997
  have htrace : WordTrace (prefixWord ++ tailWord_7393997) baseStart_7393997 baseEnd_7393997 := by
    simpa [prefixWord, tailWord_7393997, baseEnd_7393997] using wordTrace_append hprefix tailTrace_7393997
  have hstable : (prefixWord ++ tailWord_7393997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7393997).length < 2 ^ (prefixWord ++ tailWord_7393997).sum := by decide
  have hdescent : baseEnd_7393997 < baseStart_7393997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7393997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394033 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_7394033 : Nat := 118140960795 + 7394033 * 2 ^ 59
def prefixEnd_7394033 : Nat := 4983230072969 + 3 ^ 40 * 7394033 * 2
def baseEnd_7394033 : Nat := 3796692904205774545582967

theorem tailTrace_7394033 : CollatzResearch.WordTrace tailWord_7394033 prefixEnd_7394033 3796692904205774545582967 := by
  unfold tailWord_7394033
  simp only [CollatzResearch.WordTrace]
  refine ⟨269682538821688716144842753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179788359214459144096561835 269682538821688716144842753)
  ·
    refine ⟨202261904116266537108632065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269682538821688716144842753 202261904116266537108632065)
    ·
      refine ⟨151696428087199902831474049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202261904116266537108632065 151696428087199902831474049)
      ·
        refine ⟨113772321065399927123605537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151696428087199902831474049 113772321065399927123605537)
        ·
          refine ⟨85329240799049945342704153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113772321065399927123605537 85329240799049945342704153)
          ·
            refine ⟨63996930599287459007028115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85329240799049945342704153 63996930599287459007028115)
            ·
              refine ⟨95995395898931188510542173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63996930599287459007028115 95995395898931188510542173)
              ·
                refine ⟨35998273462099195691453315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95995395898931188510542173 35998273462099195691453315)
                ·
                  refine ⟨53997410193148793537179973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35998273462099195691453315 53997410193148793537179973)
                  ·
                    refine ⟨10124514411215398788221245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53997410193148793537179973 10124514411215398788221245)
                    ·
                      refine ⟨3796692904205774545582967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10124514411215398788221245 3796692904205774545582967)
                      ·
                        rfl

theorem cell23_7394033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_7394033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394033 prefixEnd_7394033 := by exact prefixLift 7394033
  have htrace : WordTrace (prefixWord ++ tailWord_7394033) baseStart_7394033 baseEnd_7394033 := by
    simpa [prefixWord, tailWord_7394033, baseEnd_7394033] using wordTrace_append hprefix tailTrace_7394033
  have hstable : (prefixWord ++ tailWord_7394033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394033).length < 2 ^ (prefixWord ++ tailWord_7394033).sum := by decide
  have hdescent : baseEnd_7394033 < baseStart_7394033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394130 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_7394130 : Nat := 118140960795 + 7394130 * 2 ^ 59
def prefixEnd_7394130 : Nat := 4983230072969 + 3 ^ 40 * 7394130 * 2
def baseEnd_7394130 : Nat := 1265580903943086888690007

theorem tailTrace_7394130 : CollatzResearch.WordTrace tailWord_7394130 prefixEnd_7394130 1265580903943086888690007 := by
  unfold tailWord_7394130
  simp only [CollatzResearch.WordTrace]
  refine ⟨67421519175584325427780961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179790717801558201140749229 67421519175584325427780961)
  ·
    refine ⟨50566139381688244070835721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67421519175584325427780961 50566139381688244070835721)
    ·
      refine ⟨37924604536266183053126791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50566139381688244070835721 37924604536266183053126791)
      ·
        refine ⟨56886906804399274579690187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37924604536266183053126791 56886906804399274579690187)
        ·
          refine ⟨85330360206598911869535281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56886906804399274579690187 85330360206598911869535281)
          ·
            refine ⟨63997770154949183902151461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85330360206598911869535281 63997770154949183902151461)
            ·
              refine ⟨11999581904052971981653399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63997770154949183902151461 11999581904052971981653399)
              ·
                refine ⟨17999372856079457972480099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11999581904052971981653399 17999372856079457972480099)
                ·
                  refine ⟨26999059284119186958720149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17999372856079457972480099 26999059284119186958720149)
                  ·
                    refine ⟨1265580903943086888690007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26999059284119186958720149 1265580903943086888690007)
                    ·
                      rfl

theorem cell23_7394130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_7394130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394130 prefixEnd_7394130 := by exact prefixLift 7394130
  have htrace : WordTrace (prefixWord ++ tailWord_7394130) baseStart_7394130 baseEnd_7394130 := by
    simpa [prefixWord, tailWord_7394130, baseEnd_7394130] using wordTrace_append hprefix tailTrace_7394130
  have hstable : (prefixWord ++ tailWord_7394130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394130).length < 2 ^ (prefixWord ++ tailWord_7394130).sum := by decide
  have hdescent : baseEnd_7394130 < baseStart_7394130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394137 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 5, 2, 2]
def baseStart_7394137 : Nat := 118140960795 + 7394137 * 2 ^ 59
def prefixEnd_7394137 : Nat := 4983230072969 + 3 ^ 40 * 7394137 * 2
def baseEnd_7394137 : Nat := 3796746306193842138682489

theorem tailTrace_7394137 : CollatzResearch.WordTrace tailWord_7394137 prefixEnd_7394137 3796746306193842138682489 := by
  unfold tailWord_7394137
  simp only [CollatzResearch.WordTrace]
  refine ⟨269686332013311941906628665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179790888008874627937752443 269686332013311941906628665)
  ·
    refine ⟨202264749009983956429971499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269686332013311941906628665 202264749009983956429971499)
    ·
      refine ⟨303397123514975934644957249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202264749009983956429971499 303397123514975934644957249)
      ·
        refine ⟨227547842636231950983717937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303397123514975934644957249 227547842636231950983717937)
        ·
          refine ⟨170660881977173963237788453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227547842636231950983717937 170660881977173963237788453)
          ·
            refine ⟨31998915370720118107085335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170660881977173963237788453 31998915370720118107085335)
            ·
              refine ⟨47998373056080177160628003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31998915370720118107085335 47998373056080177160628003)
              ·
                refine ⟨71997559584120265740942005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47998373056080177160628003 71997559584120265740942005)
                ·
                  refine ⟨6749771211011274913213313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71997559584120265740942005 6749771211011274913213313)
                  ·
                    refine ⟨5062328408258456184909985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749771211011274913213313 5062328408258456184909985)
                    ·
                      refine ⟨3796746306193842138682489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062328408258456184909985 3796746306193842138682489)
                      ·
                        rfl

theorem cell23_7394137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_7394137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394137 prefixEnd_7394137 := by exact prefixLift 7394137
  have htrace : WordTrace (prefixWord ++ tailWord_7394137) baseStart_7394137 baseEnd_7394137 := by
    simpa [prefixWord, tailWord_7394137, baseEnd_7394137] using wordTrace_append hprefix tailTrace_7394137
  have hstable : (prefixWord ++ tailWord_7394137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394137).length < 2 ^ (prefixWord ++ tailWord_7394137).sum := by decide
  have hdescent : baseEnd_7394137 < baseStart_7394137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394173 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_7394173 : Nat := 118140960795 + 7394173 * 2 ^ 59
def prefixEnd_7394173 : Nat := 4983230072969 + 3 ^ 40 * 7394173 * 2
def baseEnd_7394173 : Nat := 1265588263832467999277441

theorem tailTrace_7394173 : CollatzResearch.WordTrace tailWord_7394173 prefixEnd_7394173 1265588263832467999277441 := by
  unfold tailWord_7394173
  simp only [CollatzResearch.WordTrace]
  refine ⟨269687645041181520054939173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179791763360787680036626115 269687645041181520054939173)
  ·
    refine ⟨50566433445221535010301095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269687645041181520054939173 50566433445221535010301095)
    ·
      refine ⟨75849650167832302515451643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50566433445221535010301095 75849650167832302515451643)
      ·
        refine ⟨113774475251748453773177465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75849650167832302515451643 113774475251748453773177465)
        ·
          refine ⟨85330856438811340329883099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113774475251748453773177465 85330856438811340329883099)
          ·
            refine ⟨127996284658217010494824649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85330856438811340329883099 127996284658217010494824649)
            ·
              refine ⟨95997213493662757871118487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127996284658217010494824649 95997213493662757871118487)
              ·
                refine ⟨143995820240494136806677731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95997213493662757871118487 143995820240494136806677731)
                ·
                  refine ⟨215993730360741205210016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143995820240494136806677731 215993730360741205210016597)
                  ·
                    refine ⟨1265588263832467999277441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215993730360741205210016597 1265588263832467999277441)
                    ·
                      rfl

theorem cell23_7394173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_7394173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394173 prefixEnd_7394173 := by exact prefixLift 7394173
  have htrace : WordTrace (prefixWord ++ tailWord_7394173) baseStart_7394173 baseEnd_7394173 := by
    simpa [prefixWord, tailWord_7394173, baseEnd_7394173] using wordTrace_append hprefix tailTrace_7394173
  have hstable : (prefixWord ++ tailWord_7394173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394173).length < 2 ^ (prefixWord ++ tailWord_7394173).sum := by decide
  have hdescent : baseEnd_7394173 < baseStart_7394173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394174 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7394174 : Nat := 118140960795 + 7394174 * 2 ^ 59
def prefixEnd_7394174 : Nat := 4983230072969 + 3 ^ 40 * 7394174 * 2
def baseEnd_7394174 : Nat := 3796765304978058493919819

theorem tailTrace_7394174 : CollatzResearch.WordTrace tailWord_7394174 prefixEnd_7394174 3796765304978058493919819 := by
  unfold tailWord_7394174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33710960189272237153215697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179791787676118598150483717 33710960189272237153215697)
  ·
    refine ⟨25283220141954177864911773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33710960189272237153215697 25283220141954177864911773)
    ·
      refine ⟨9481207553232816699341915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25283220141954177864911773 9481207553232816699341915)
      ·
        refine ⟨14221811329849225049012873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9481207553232816699341915 14221811329849225049012873)
        ·
          refine ⟨10666358497386918786759655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14221811329849225049012873 10666358497386918786759655)
          ·
            refine ⟨15999537746080378180139483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666358497386918786759655 15999537746080378180139483)
            ·
              refine ⟨23999306619120567270209225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15999537746080378180139483 23999306619120567270209225)
              ·
                refine ⟨17999479964340425452656919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23999306619120567270209225 17999479964340425452656919)
                ·
                  refine ⟨26999219946510638178985379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17999479964340425452656919 26999219946510638178985379)
                  ·
                    refine ⟨40498829919765957268478069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26999219946510638178985379 40498829919765957268478069)
                    ·
                      refine ⟨3796765304978058493919819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40498829919765957268478069 3796765304978058493919819)
                      ·
                        rfl

theorem cell23_7394174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7394174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394174 prefixEnd_7394174 := by exact prefixLift 7394174
  have htrace : WordTrace (prefixWord ++ tailWord_7394174) baseStart_7394174 baseEnd_7394174 := by
    simpa [prefixWord, tailWord_7394174, baseEnd_7394174] using wordTrace_append hprefix tailTrace_7394174
  have hstable : (prefixWord ++ tailWord_7394174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394174).length < 2 ^ (prefixWord ++ tailWord_7394174).sum := by decide
  have hdescent : baseEnd_7394174 < baseStart_7394174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394187 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 3]
def baseStart_7394187 : Nat := 118140960795 + 7394187 * 2 ^ 59
def prefixEnd_7394187 : Nat := 4983230072969 + 3 ^ 40 * 7394187 * 2
def baseEnd_7394187 : Nat := 3796771980226566943057259

theorem tailTrace_7394187 : CollatzResearch.WordTrace tailWord_7394187 prefixEnd_7394187 3796771980226566943057259 := by
  unfold tailWord_7394187
  simp only [CollatzResearch.WordTrace]
  refine ⟨269688155663130800445948815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179792103775420533630632543 269688155663130800445948815)
  ·
    refine ⟨404532233494696200668923223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269688155663130800445948815 404532233494696200668923223)
    ·
      refine ⟨606798350242044301003384835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404532233494696200668923223 606798350242044301003384835)
      ·
        refine ⟨910197525363066451505077253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606798350242044301003384835 910197525363066451505077253)
        ·
          refine ⟨170662036005574959657201985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910197525363066451505077253 170662036005574959657201985)
          ·
            refine ⟨127996527004181219742901489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170662036005574959657201985 127996527004181219742901489)
            ·
              refine ⟨95997395253135914807176117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127996527004181219742901489 95997395253135914807176117)
              ·
                refine ⟨8999755804981492013172761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95997395253135914807176117 8999755804981492013172761)
                ·
                  refine ⟨6749816853736119009879571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8999755804981492013172761 6749816853736119009879571)
                  ·
                    refine ⟨10124725280604178514819357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749816853736119009879571 10124725280604178514819357)
                    ·
                      refine ⟨3796771980226566943057259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10124725280604178514819357 3796771980226566943057259)
                      ·
                        rfl

theorem cell23_7394187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 3].length) (baseStart_7394187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394187 prefixEnd_7394187 := by exact prefixLift 7394187
  have htrace : WordTrace (prefixWord ++ tailWord_7394187) baseStart_7394187 baseEnd_7394187 := by
    simpa [prefixWord, tailWord_7394187, baseEnd_7394187] using wordTrace_append hprefix tailTrace_7394187
  have hstable : (prefixWord ++ tailWord_7394187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394187).length < 2 ^ (prefixWord ++ tailWord_7394187).sum := by decide
  have hdescent : baseEnd_7394187 < baseStart_7394187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394194 : List Nat := [3, 2, 3, 2, 2, 2, 2, 7]
def baseStart_7394194 : Nat := 118140960795 + 7394194 * 2 ^ 59
def prefixEnd_7394194 : Nat := 4983230072969 + 3 ^ 40 * 7394194 * 2
def baseEnd_7394194 : Nat := 140621317577449941321101

theorem tailTrace_7394194 : CollatzResearch.WordTrace tailWord_7394194 prefixEnd_7394194 140621317577449941321101 := by
  unfold tailWord_7394194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67422102743526360160363409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179792273982736960427635757 67422102743526360160363409)
  ·
    refine ⟨50566577057644770120272557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67422102743526360160363409 50566577057644770120272557)
    ·
      refine ⟨18962466396616788795102209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50566577057644770120272557 18962466396616788795102209)
      ·
        refine ⟨14221849797462591596326657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18962466396616788795102209 14221849797462591596326657)
        ·
          refine ⟨10666387348096943697244993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14221849797462591596326657 10666387348096943697244993)
          ·
            refine ⟨7999790511072707772933745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666387348096943697244993 7999790511072707772933745)
            ·
              refine ⟨5999842883304530829700309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7999790511072707772933745 5999842883304530829700309)
              ·
                refine ⟨140621317577449941321101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5999842883304530829700309 140621317577449941321101)
                ·
                  rfl

theorem cell23_7394194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_7394194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394194 prefixEnd_7394194 := by exact prefixLift 7394194
  have htrace : WordTrace (prefixWord ++ tailWord_7394194) baseStart_7394194 baseEnd_7394194 := by
    simpa [prefixWord, tailWord_7394194, baseEnd_7394194] using wordTrace_append hprefix tailTrace_7394194
  have hstable : (prefixWord ++ tailWord_7394194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394194).length < 2 ^ (prefixWord ++ tailWord_7394194).sum := by decide
  have hdescent : baseEnd_7394194 < baseStart_7394194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394223 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_7394223 : Nat := 118140960795 + 7394223 * 2 ^ 59
def prefixEnd_7394223 : Nat := 4983230072969 + 3 ^ 40 * 7394223 * 2
def baseEnd_7394223 : Nat := 3796790465530128802207093

theorem tailTrace_7394223 : CollatzResearch.WordTrace tailWord_7394223 prefixEnd_7394223 3796790465530128802207093 := by
  unfold tailWord_7394223
  simp only [CollatzResearch.WordTrace]
  refine ⟨269689468691000378594259323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179792979127333585729506215 269689468691000378594259323)
  ·
    refine ⟨404534203036500567891388985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269689468691000378594259323 404534203036500567891388985)
    ·
      refine ⟨303400652277375425918541739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404534203036500567891388985 303400652277375425918541739)
      ·
        refine ⟨455100978416063138877812609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303400652277375425918541739 455100978416063138877812609)
        ·
          refine ⟨341325733812047354158359457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455100978416063138877812609 341325733812047354158359457)
          ·
            refine ⟨255994300359035515618769593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341325733812047354158359457 255994300359035515618769593)
            ·
              refine ⟨191995725269276636714077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255994300359035515618769593 191995725269276636714077195)
              ·
                refine ⟨287993587903914955071115793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191995725269276636714077195 287993587903914955071115793)
                ·
                  refine ⟨215995190927936216303336845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287993587903914955071115793 215995190927936216303336845)
                  ·
                    refine ⟨80998196597976081113751317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215995190927936216303336845 80998196597976081113751317)
                    ·
                      refine ⟨3796790465530128802207093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80998196597976081113751317 3796790465530128802207093)
                      ·
                        rfl

theorem cell23_7394223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_7394223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394223 prefixEnd_7394223 := by exact prefixLift 7394223
  have htrace : WordTrace (prefixWord ++ tailWord_7394223) baseStart_7394223 baseEnd_7394223 := by
    simpa [prefixWord, tailWord_7394223, baseEnd_7394223] using wordTrace_append hprefix tailTrace_7394223
  have hstable : (prefixWord ++ tailWord_7394223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394223).length < 2 ^ (prefixWord ++ tailWord_7394223).sum := by decide
  have hdescent : baseEnd_7394223 < baseStart_7394223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_7394243 : Nat := 118140960795 + 7394243 * 2 ^ 59
def prefixEnd_7394243 : Nat := 4983230072969 + 3 ^ 40 * 7394243 * 2
def baseEnd_7394243 : Nat := 3796800735143218723957001

theorem tailTrace_7394243 : CollatzResearch.WordTrace tailWord_7394243 prefixEnd_7394243 3796800735143218723957001 := by
  unfold tailWord_7394243
  simp only [CollatzResearch.WordTrace]
  refine ⟨269690198150927922009987383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179793465433951948006658255 269690198150927922009987383)
  ·
    refine ⟨404535297226391883014981075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269690198150927922009987383 404535297226391883014981075)
    ·
      refine ⟨606802945839587824522471613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404535297226391883014981075 606802945839587824522471613)
      ·
        refine ⟨227551104689845434195926855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606802945839587824522471613 227551104689845434195926855)
        ·
          refine ⟨341326657034768151293890283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227551104689845434195926855 341326657034768151293890283)
          ·
            refine ⟨511989985552152226940835425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341326657034768151293890283 511989985552152226940835425)
            ·
              refine ⟨383992489164114170205626569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511989985552152226940835425 383992489164114170205626569)
              ·
                refine ⟨287994366873085627654219927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383992489164114170205626569 287994366873085627654219927)
                ·
                  refine ⟨431991550309628441481329891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287994366873085627654219927 431991550309628441481329891)
                  ·
                    refine ⟨647987325464442662221994837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431991550309628441481329891 647987325464442662221994837)
                    ·
                      refine ⟨3796800735143218723957001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 647987325464442662221994837 3796800735143218723957001)
                      ·
                        rfl

theorem cell23_7394243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_7394243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394243 prefixEnd_7394243 := by exact prefixLift 7394243
  have htrace : WordTrace (prefixWord ++ tailWord_7394243) baseStart_7394243 baseEnd_7394243 := by
    simpa [prefixWord, tailWord_7394243, baseEnd_7394243] using wordTrace_append hprefix tailTrace_7394243
  have hstable : (prefixWord ++ tailWord_7394243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394243).length < 2 ^ (prefixWord ++ tailWord_7394243).sum := by decide
  have hdescent : baseEnd_7394243 < baseStart_7394243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394248 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_7394248 : Nat := 118140960795 + 7394248 * 2 ^ 59
def prefixEnd_7394248 : Nat := 4983230072969 + 3 ^ 40 * 7394248 * 2
def baseEnd_7394248 : Nat := 3796803302546491204394479

theorem tailTrace_7394248 : CollatzResearch.WordTrace tailWord_7394248 prefixEnd_7394248 3796803302546491204394479 := by
  unfold tailWord_7394248
  simp only [CollatzResearch.WordTrace]
  refine ⟨134845190257954903931959699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179793587010606538575946265 134845190257954903931959699)
  ·
    refine ⟨202267785386932355897939549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134845190257954903931959699 202267785386932355897939549)
    ·
      refine ⟨75850419520099633461727331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202267785386932355897939549 75850419520099633461727331)
      ·
        refine ⟨113775629280149450192590997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75850419520099633461727331 113775629280149450192590997)
        ·
          refine ⟨5333232622507005477777703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113775629280149450192590997 5333232622507005477777703)
          ·
            refine ⟨7999848933760508216666555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333232622507005477777703 7999848933760508216666555)
            ·
              refine ⟨11999773400640762324999833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999848933760508216666555 11999773400640762324999833)
              ·
                refine ⟨8999830050480571743749875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11999773400640762324999833 8999830050480571743749875)
                ·
                  refine ⟨13499745075720857615624813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8999830050480571743749875 13499745075720857615624813)
                  ·
                    refine ⟨5062404403395321605859305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13499745075720857615624813 5062404403395321605859305)
                    ·
                      refine ⟨3796803302546491204394479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062404403395321605859305 3796803302546491204394479)
                      ·
                        rfl

theorem cell23_7394248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_7394248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394248 prefixEnd_7394248 := by exact prefixLift 7394248
  have htrace : WordTrace (prefixWord ++ tailWord_7394248) baseStart_7394248 baseEnd_7394248 := by
    simpa [prefixWord, tailWord_7394248, baseEnd_7394248] using wordTrace_append hprefix tailTrace_7394248
  have hstable : (prefixWord ++ tailWord_7394248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394248).length < 2 ^ (prefixWord ++ tailWord_7394248).sum := by decide
  have hdescent : baseEnd_7394248 < baseStart_7394248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394287 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 5, 2]
def baseStart_7394287 : Nat := 118140960795 + 7394287 * 2 ^ 59
def prefixEnd_7394287 : Nat := 4983230072969 + 3 ^ 40 * 7394287 * 2
def baseEnd_7394287 : Nat := 3796823328292016551806799

theorem tailTrace_7394287 : CollatzResearch.WordTrace tailWord_7394287 prefixEnd_7394287 3796823328292016551806799 := by
  unfold tailWord_7394287
  simp only [CollatzResearch.WordTrace]
  refine ⟨269691802962768517524589115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179794535308512345016392743 269691802962768517524589115)
  ·
    refine ⟨404537704444152776286883673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269691802962768517524589115 404537704444152776286883673)
    ·
      refine ⟨303403278333114582215162755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404537704444152776286883673 303403278333114582215162755)
      ·
        refine ⟨455104917499671873322744133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303403278333114582215162755 455104917499671873322744133)
        ·
          refine ⟨85332172031188476248014525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455104917499671873322744133 85332172031188476248014525)
          ·
            refine ⟨31999564511695678593005447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85332172031188476248014525 31999564511695678593005447)
            ·
              refine ⟨47999346767543517889508171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31999564511695678593005447 47999346767543517889508171)
              ·
                refine ⟨71999020151315276834262257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47999346767543517889508171 71999020151315276834262257)
                ·
                  refine ⟨53999265113486457625696693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71999020151315276834262257 53999265113486457625696693)
                  ·
                    refine ⟨5062431104389355402409065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53999265113486457625696693 5062431104389355402409065)
                    ·
                      refine ⟨3796823328292016551806799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062431104389355402409065 3796823328292016551806799)
                      ·
                        rfl

theorem cell23_7394287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5, 2].length) (baseStart_7394287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394287 prefixEnd_7394287 := by exact prefixLift 7394287
  have htrace : WordTrace (prefixWord ++ tailWord_7394287) baseStart_7394287 baseEnd_7394287 := by
    simpa [prefixWord, tailWord_7394287, baseEnd_7394287] using wordTrace_append hprefix tailTrace_7394287
  have hstable : (prefixWord ++ tailWord_7394287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394287).length < 2 ^ (prefixWord ++ tailWord_7394287).sum := by decide
  have hdescent : baseEnd_7394287 < baseStart_7394287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394294 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7394294 : Nat := 118140960795 + 7394294 * 2 ^ 59
def prefixEnd_7394294 : Nat := 4983230072969 + 3 ^ 40 * 7394294 * 2
def baseEnd_7394294 : Nat := 3796826922656598024419267

theorem tailTrace_7394294 : CollatzResearch.WordTrace tailWord_7394294 prefixEnd_7394294 3796826922656598024419267 := by
  unfold tailWord_7394294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855753642108947357505871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179794705515828771813395957 16855753642108947357505871)
  ·
    refine ⟨25283630463163421036258807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16855753642108947357505871 25283630463163421036258807)
    ·
      refine ⟨37925445694745131554388211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25283630463163421036258807 37925445694745131554388211)
      ·
        refine ⟨56888168542117697331582317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37925445694745131554388211 56888168542117697331582317)
        ·
          refine ⟨21333063203294136499343369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56888168542117697331582317 21333063203294136499343369)
          ·
            refine ⟨15999797402470602374507527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21333063203294136499343369 15999797402470602374507527)
            ·
              refine ⟨23999696103705903561761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15999797402470602374507527 23999696103705903561761291)
              ·
                refine ⟨35999544155558855342641937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23999696103705903561761291 35999544155558855342641937)
                ·
                  refine ⟨26999658116669141506981453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35999544155558855342641937 26999658116669141506981453)
                  ·
                    refine ⟨10124871793750928065118045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26999658116669141506981453 10124871793750928065118045)
                    ·
                      refine ⟨3796826922656598024419267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10124871793750928065118045 3796826922656598024419267)
                      ·
                        rfl

theorem cell23_7394294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7394294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394294 prefixEnd_7394294 := by exact prefixLift 7394294
  have htrace : WordTrace (prefixWord ++ tailWord_7394294) baseStart_7394294 baseEnd_7394294 := by
    simpa [prefixWord, tailWord_7394294, baseEnd_7394294] using wordTrace_append hprefix tailTrace_7394294
  have hstable : (prefixWord ++ tailWord_7394294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394294).length < 2 ^ (prefixWord ++ tailWord_7394294).sum := by decide
  have hdescent : baseEnd_7394294 < baseStart_7394294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394314 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_7394314 : Nat := 118140960795 + 7394314 * 2 ^ 59
def prefixEnd_7394314 : Nat := 4983230072969 + 3 ^ 40 * 7394314 * 2
def baseEnd_7394314 : Nat := 1265612397423229315389725

theorem tailTrace_7394314 : CollatzResearch.WordTrace tailWord_7394314 prefixEnd_7394314 1265612397423229315389725 := by
  unfold tailWord_7394314
  simp only [CollatzResearch.WordTrace]
  refine ⟨67423196933417675283955499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179795191822447134090547997 67423196933417675283955499)
  ·
    refine ⟨101134795400126512925933249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67423196933417675283955499 101134795400126512925933249)
    ·
      refine ⟨75851096550094884694449937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101134795400126512925933249 75851096550094884694449937)
      ·
        refine ⟨56888322412571163520837453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75851096550094884694449937 56888322412571163520837453)
        ·
          refine ⟨21333120904714186320314045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56888322412571163520837453 21333120904714186320314045)
          ·
            refine ⟨7999920339267819870117767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21333120904714186320314045 7999920339267819870117767)
            ·
              refine ⟨11999880508901729805176651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999920339267819870117767 11999880508901729805176651)
              ·
                refine ⟨17999820763352594707764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11999880508901729805176651 17999820763352594707764977)
                ·
                  refine ⟨13499865572514446030823733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17999820763352594707764977 13499865572514446030823733)
                  ·
                    refine ⟨1265612397423229315389725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13499865572514446030823733 1265612397423229315389725)
                    ·
                      rfl

theorem cell23_7394314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_7394314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394314 prefixEnd_7394314 := by exact prefixLift 7394314
  have htrace : WordTrace (prefixWord ++ tailWord_7394314) baseStart_7394314 baseEnd_7394314 := by
    simpa [prefixWord, tailWord_7394314, baseEnd_7394314] using wordTrace_append hprefix tailTrace_7394314
  have hstable : (prefixWord ++ tailWord_7394314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394314).length < 2 ^ (prefixWord ++ tailWord_7394314).sum := by decide
  have hdescent : baseEnd_7394314 < baseStart_7394314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394330 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_7394330 : Nat := 118140960795 + 7394330 * 2 ^ 59
def prefixEnd_7394330 : Nat := 4983230072969 + 3 ^ 40 * 7394330 * 2
def baseEnd_7394330 : Nat := 3796845407960159883569101

theorem tailTrace_7394330 : CollatzResearch.WordTrace tailWord_7394330 prefixEnd_7394330 3796845407960159883569101 := by
  unfold tailWord_7394330
  simp only [CollatzResearch.WordTrace]
  refine ⟨67423342825403183967101111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179795580867741823912269629 67423342825403183967101111)
  ·
    refine ⟨101135014238104775950651667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67423342825403183967101111 101135014238104775950651667)
    ·
      refine ⟨151702521357157163925977501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101135014238104775950651667 151702521357157163925977501)
      ·
        refine ⟨56888445508933936472241563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151702521357157163925977501 56888445508933936472241563)
        ·
          refine ⟨85332668263400904708362345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56888445508933936472241563 85332668263400904708362345)
          ·
            refine ⟨63999501197550678531271759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85332668263400904708362345 63999501197550678531271759)
            ·
              refine ⟨95999251796326017796907639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63999501197550678531271759 95999251796326017796907639)
              ·
                refine ⟨143998877694489026695361459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95999251796326017796907639 143998877694489026695361459)
                ·
                  refine ⟨215998316541733540043042189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143998877694489026695361459 215998316541733540043042189)
                  ·
                    refine ⟨80999368703150077516140821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215998316541733540043042189 80999368703150077516140821)
                    ·
                      refine ⟨3796845407960159883569101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80999368703150077516140821 3796845407960159883569101)
                      ·
                        rfl

theorem cell23_7394330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_7394330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394330 prefixEnd_7394330 := by exact prefixLift 7394330
  have htrace : WordTrace (prefixWord ++ tailWord_7394330) baseStart_7394330 baseEnd_7394330 := by
    simpa [prefixWord, tailWord_7394330, baseEnd_7394330] using wordTrace_append hprefix tailTrace_7394330
  have hstable : (prefixWord ++ tailWord_7394330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394330).length < 2 ^ (prefixWord ++ tailWord_7394330).sum := by decide
  have hdescent : baseEnd_7394330 < baseStart_7394330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394374 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7394374 : Nat := 118140960795 + 7394374 * 2 ^ 59
def prefixEnd_7394374 : Nat := 4983230072969 + 3 ^ 40 * 7394374 * 2
def baseEnd_7394374 : Nat := 421874222345439745713211

theorem tailTrace_7394374 : CollatzResearch.WordTrace tailWord_7394374 prefixEnd_7394374 421874222345439745713211 := by
  unfold tailWord_7394374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427968003545416605718943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179796650742302220922004117 8427968003545416605718943)
  ·
    refine ⟨12641952005318124908578415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8427968003545416605718943 12641952005318124908578415)
    ·
      refine ⟨18962928007977187362867623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641952005318124908578415 18962928007977187362867623)
      ·
        refine ⟨28444392011965781044301435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18962928007977187362867623 28444392011965781044301435)
        ·
          refine ⟨42666588017948671566452153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28444392011965781044301435 42666588017948671566452153)
          ·
            refine ⟨31999941013461503674839115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42666588017948671566452153 31999941013461503674839115)
            ·
              refine ⟨47999911520192255512258673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31999941013461503674839115 47999911520192255512258673)
              ·
                refine ⟨35999933640144191634194005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47999911520192255512258673 35999933640144191634194005)
                ·
                  refine ⟨421874222345439745713211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35999933640144191634194005 421874222345439745713211)
                  ·
                    rfl

theorem cell23_7394374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7394374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394374 prefixEnd_7394374 := by exact prefixLift 7394374
  have htrace : WordTrace (prefixWord ++ tailWord_7394374) baseStart_7394374 baseEnd_7394374 := by
    simpa [prefixWord, tailWord_7394374, baseEnd_7394374] using wordTrace_append hprefix tailTrace_7394374
  have hstable : (prefixWord ++ tailWord_7394374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394374).length < 2 ^ (prefixWord ++ tailWord_7394374).sum := by decide
  have hdescent : baseEnd_7394374 < baseStart_7394374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394401 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_7394401 : Nat := 118140960795 + 7394401 * 2 ^ 59
def prefixEnd_7394401 : Nat := 4983230072969 + 3 ^ 40 * 7394401 * 2
def baseEnd_7394401 : Nat := 3796881865086629105781275

theorem tailTrace_7394401 : CollatzResearch.WordTrace tailWord_7394401 prefixEnd_7394401 3796881865086629105781275 := by
  unfold tailWord_7394401
  simp only [CollatzResearch.WordTrace]
  refine ⟨269695960884355514994239057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179797307256237009996159371 269695960884355514994239057)
  ·
    refine ⟨202271970663266636245679293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269695960884355514994239057 202271970663266636245679293)
    ·
      refine ⟨75851988998724988592129735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202271970663266636245679293 75851988998724988592129735)
      ·
        refine ⟨113777983498087482888194603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75851988998724988592129735 113777983498087482888194603)
        ·
          refine ⟨170666975247131224332291905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113777983498087482888194603 170666975247131224332291905)
          ·
            refine ⟨128000231435348418249218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170666975247131224332291905 128000231435348418249218929)
            ·
              refine ⟨96000173576511313686914197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128000231435348418249218929 96000173576511313686914197)
              ·
                refine ⟨4500008136398967829074103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96000173576511313686914197 4500008136398967829074103)
                ·
                  refine ⟨6750012204598451743611155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500008136398967829074103 6750012204598451743611155)
                  ·
                    refine ⟨10125018306897677615416733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750012204598451743611155 10125018306897677615416733)
                    ·
                      refine ⟨3796881865086629105781275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125018306897677615416733 3796881865086629105781275)
                      ·
                        rfl

theorem cell23_7394401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_7394401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394401 prefixEnd_7394401 := by exact prefixLift 7394401
  have htrace : WordTrace (prefixWord ++ tailWord_7394401) baseStart_7394401 baseEnd_7394401 := by
    simpa [prefixWord, tailWord_7394401, baseEnd_7394401] using wordTrace_append hprefix tailTrace_7394401
  have hstable : (prefixWord ++ tailWord_7394401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394401).length < 2 ^ (prefixWord ++ tailWord_7394401).sum := by decide
  have hdescent : baseEnd_7394401 < baseStart_7394401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394408 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 6]
def baseStart_7394408 : Nat := 118140960795 + 7394408 * 2 ^ 59
def prefixEnd_7394408 : Nat := 4983230072969 + 3 ^ 40 * 7394408 * 2
def baseEnd_7394408 : Nat := 421876162161245619821527

theorem tailTrace_7394408 : CollatzResearch.WordTrace tailWord_7394408 prefixEnd_7394408 421876162161245619821527 := by
  unfold tailWord_7394408
  simp only [CollatzResearch.WordTrace]
  refine ⟨134848108097665077594871939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179797477463553436793162585 134848108097665077594871939)
  ·
    refine ⟨202272162146497616392307909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134848108097665077594871939 202272162146497616392307909)
    ·
      refine ⟨37926030402468303073557733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202272162146497616392307909 37926030402468303073557733)
      ·
        refine ⟨7111130700462806826292075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37926030402468303073557733 7111130700462806826292075)
        ·
          refine ⟨10666696050694210239438113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111130700462806826292075 10666696050694210239438113)
          ·
            refine ⟨8000022038020657679578585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666696050694210239438113 8000022038020657679578585)
            ·
              refine ⟨6000016528515493259683939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000022038020657679578585 6000016528515493259683939)
              ·
                refine ⟨9000024792773239889525909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000016528515493259683939 9000024792773239889525909)
                ·
                  refine ⟨421876162161245619821527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9000024792773239889525909 421876162161245619821527)
                  ·
                    rfl

theorem cell23_7394408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_7394408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394408 prefixEnd_7394408 := by exact prefixLift 7394408
  have htrace : WordTrace (prefixWord ++ tailWord_7394408) baseStart_7394408 baseEnd_7394408 := by
    simpa [prefixWord, tailWord_7394408, baseEnd_7394408] using wordTrace_append hprefix tailTrace_7394408
  have hstable : (prefixWord ++ tailWord_7394408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394408).length < 2 ^ (prefixWord ++ tailWord_7394408).sum := by decide
  have hdescent : baseEnd_7394408 < baseStart_7394408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394417 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_7394417 : Nat := 118140960795 + 7394417 * 2 ^ 59
def prefixEnd_7394417 : Nat := 4983230072969 + 3 ^ 40 * 7394417 * 2
def baseEnd_7394417 : Nat := 1265630026925700347727067

theorem tailTrace_7394417 : CollatzResearch.WordTrace tailWord_7394417 prefixEnd_7394417 1265630026925700347727067 := by
  unfold tailWord_7394417
  simp only [CollatzResearch.WordTrace]
  refine ⟨269696544452297549726821505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179797696301531699817881003 269696544452297549726821505)
  ·
    refine ⟨202272408339223162295116129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269696544452297549726821505 202272408339223162295116129)
    ·
      refine ⟨151704306254417371721337097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202272408339223162295116129 151704306254417371721337097)
      ·
        refine ⟨113778229690813028791002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151704306254417371721337097 113778229690813028791002823)
        ·
          refine ⟨170667344536219543186504235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113778229690813028791002823 170667344536219543186504235)
          ·
            refine ⟨256001016804329314779756353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170667344536219543186504235 256001016804329314779756353)
            ·
              refine ⟨192000762603246986084817265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256001016804329314779756353 192000762603246986084817265)
              ·
                refine ⟨144000571952435239563612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192000762603246986084817265 144000571952435239563612949)
                ·
                  refine ⟨6750026810270401854544357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144000571952435239563612949 6750026810270401854544357)
                  ·
                    refine ⟨1265630026925700347727067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750026810270401854544357 1265630026925700347727067)
                    ·
                      rfl

theorem cell23_7394417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_7394417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394417 prefixEnd_7394417 := by exact prefixLift 7394417
  have htrace : WordTrace (prefixWord ++ tailWord_7394417) baseStart_7394417 baseEnd_7394417 := by
    simpa [prefixWord, tailWord_7394417, baseEnd_7394417] using wordTrace_append hprefix tailTrace_7394417
  have hstable : (prefixWord ++ tailWord_7394417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394417).length < 2 ^ (prefixWord ++ tailWord_7394417).sum := by decide
  have hdescent : baseEnd_7394417 < baseStart_7394417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394421 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7394421 : Nat := 118140960795 + 7394421 * 2 ^ 59
def prefixEnd_7394421 : Nat := 4983230072969 + 3 ^ 40 * 7394421 * 2
def baseEnd_7394421 : Nat := 1265630711566573009177061

theorem tailTrace_7394421 : CollatzResearch.WordTrace tailWord_7394421 prefixEnd_7394421 1265630711566573009177061 := by
  unfold tailWord_7394421
  simp only [CollatzResearch.WordTrace]
  refine ⟨269696690344283058409967117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179797793562855372273311411 269696690344283058409967117)
  ·
    refine ⟨101136258879106146903737669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269696690344283058409967117 101136258879106146903737669)
    ·
      refine ⟨18963048539832402544450813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101136258879106146903737669 18963048539832402544450813)
      ·
        refine ⟨7111143202437150954169055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18963048539832402544450813 7111143202437150954169055)
        ·
          refine ⟨10666714803655726431253583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111143202437150954169055 10666714803655726431253583)
          ·
            refine ⟨16000072205483589646880375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666714803655726431253583 16000072205483589646880375)
            ·
              refine ⟨24000108308225384470320563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16000072205483589646880375 24000108308225384470320563)
              ·
                refine ⟨36000162462338076705480845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24000108308225384470320563 36000162462338076705480845)
                ·
                  refine ⟨13500060923376778764555317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36000162462338076705480845 13500060923376778764555317)
                  ·
                    refine ⟨1265630711566573009177061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13500060923376778764555317 1265630711566573009177061)
                    ·
                      rfl

theorem cell23_7394421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7394421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394421 prefixEnd_7394421 := by exact prefixLift 7394421
  have htrace : WordTrace (prefixWord ++ tailWord_7394421) baseStart_7394421 baseEnd_7394421 := by
    simpa [prefixWord, tailWord_7394421, baseEnd_7394421] using wordTrace_append hprefix tailTrace_7394421
  have hstable : (prefixWord ++ tailWord_7394421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394421).length < 2 ^ (prefixWord ++ tailWord_7394421).sum := by decide
  have hdescent : baseEnd_7394421 < baseStart_7394421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394424 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_7394424 : Nat := 118140960795 + 7394424 * 2 ^ 59
def prefixEnd_7394424 : Nat := 4983230072969 + 3 ^ 40 * 7394424 * 2
def baseEnd_7394424 : Nat := 3796893675141682515793669

theorem tailTrace_7394424 : CollatzResearch.WordTrace tailWord_7394424 prefixEnd_7394424 3796893675141682515793669 := by
  unfold tailWord_7394424
  simp only [CollatzResearch.WordTrace]
  refine ⟨134848399881636094961163163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179797866508848126614884217 134848399881636094961163163)
  ·
    refine ⟨202272599822454142441744745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134848399881636094961163163 202272599822454142441744745)
    ·
      refine ⟨151704449866840606831308559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202272599822454142441744745 151704449866840606831308559)
      ·
        refine ⟨227556674800260910246962839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151704449866840606831308559 227556674800260910246962839)
        ·
          refine ⟨341335012200391365370444259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227556674800260910246962839 341335012200391365370444259)
          ·
            refine ⟨512002518300587048055666389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341335012200391365370444259 512002518300587048055666389)
            ·
              refine ⟨12000059022670008938804681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 512002518300587048055666389 12000059022670008938804681)
              ·
                refine ⟨9000044267002506704103511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12000059022670008938804681 9000044267002506704103511)
                ·
                  refine ⟨13500066400503760056155267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000044267002506704103511 13500066400503760056155267)
                  ·
                    refine ⟨20250099600755640084232901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13500066400503760056155267 20250099600755640084232901)
                    ·
                      refine ⟨3796893675141682515793669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20250099600755640084232901 3796893675141682515793669)
                      ·
                        rfl

theorem cell23_7394424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_7394424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394424 prefixEnd_7394424 := by exact prefixLift 7394424
  have htrace : WordTrace (prefixWord ++ tailWord_7394424) baseStart_7394424 baseEnd_7394424 := by
    simpa [prefixWord, tailWord_7394424, baseEnd_7394424] using wordTrace_append hprefix tailTrace_7394424
  have hstable : (prefixWord ++ tailWord_7394424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394424).length < 2 ^ (prefixWord ++ tailWord_7394424).sum := by decide
  have hdescent : baseEnd_7394424 < baseStart_7394424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394441 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 1, 1, 4]
def baseStart_7394441 : Nat := 118140960795 + 7394441 * 2 ^ 59
def prefixEnd_7394441 : Nat := 4983230072969 + 3 ^ 40 * 7394441 * 2
def baseEnd_7394441 : Nat := 3796902404312808949281091

theorem tailTrace_7394441 : CollatzResearch.WordTrace tailWord_7394441 prefixEnd_7394441 3796902404312808949281091 := by
  unfold tailWord_7394441
  simp only [CollatzResearch.WordTrace]
  refine ⟨269697419804210601825695177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179798279869473734550463451 269697419804210601825695177)
  ·
    refine ⟨202273064853157951369271383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269697419804210601825695177 202273064853157951369271383)
    ·
      refine ⟨303409597279736927053907075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202273064853157951369271383 303409597279736927053907075)
      ·
        refine ⟨455114395919605390580860613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303409597279736927053907075 455114395919605390580860613)
        ·
          refine ⟨85333949234926010733911365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455114395919605390580860613 85333949234926010733911365)
          ·
            refine ⟨16000115481548627012608381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85333949234926010733911365 16000115481548627012608381)
            ·
              refine ⟨6000043305580735129728143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16000115481548627012608381 6000043305580735129728143)
              ·
                refine ⟨9000064958371102694592215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000043305580735129728143 9000064958371102694592215)
                ·
                  refine ⟨13500097437556654041888323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000064958371102694592215 13500097437556654041888323)
                  ·
                    refine ⟨20250146156334981062832485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13500097437556654041888323 20250146156334981062832485)
                    ·
                      refine ⟨3796902404312808949281091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20250146156334981062832485 3796902404312808949281091)
                      ·
                        rfl

theorem cell23_7394441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 1, 4].length) (baseStart_7394441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394441 prefixEnd_7394441 := by exact prefixLift 7394441
  have htrace : WordTrace (prefixWord ++ tailWord_7394441) baseStart_7394441 baseEnd_7394441 := by
    simpa [prefixWord, tailWord_7394441, baseEnd_7394441] using wordTrace_append hprefix tailTrace_7394441
  have hstable : (prefixWord ++ tailWord_7394441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394441).length < 2 ^ (prefixWord ++ tailWord_7394441).sum := by decide
  have hdescent : baseEnd_7394441 < baseStart_7394441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394444 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_7394444 : Nat := 118140960795 + 7394444 * 2 ^ 59
def prefixEnd_7394444 : Nat := 4983230072969 + 3 ^ 40 * 7394444 * 2
def baseEnd_7394444 : Nat := 3796903944754772437543577

theorem tailTrace_7394444 : CollatzResearch.WordTrace tailWord_7394444 prefixEnd_7394444 3796903944754772437543577 := by
  unfold tailWord_7394444
  simp only [CollatzResearch.WordTrace]
  refine ⟨134848764611599866669027193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179798352815466488892036257 134848764611599866669027193)
  ·
    refine ⟨101136573458699900001770395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134848764611599866669027193 101136573458699900001770395)
    ·
      refine ⟨151704860188049850002655593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101136573458699900001770395 151704860188049850002655593)
      ·
        refine ⟨113778645141037387501991695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151704860188049850002655593 113778645141037387501991695)
        ·
          refine ⟨170667967711556081252987543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113778645141037387501991695 170667967711556081252987543)
          ·
            refine ⟨256001951567334121879481315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170667967711556081252987543 256001951567334121879481315)
            ·
              refine ⟨384002927351001182819221973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256001951567334121879481315 384002927351001182819221973)
              ·
                refine ⟨9000068609789090222325515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 384002927351001182819221973 9000068609789090222325515)
                ·
                  refine ⟨13500102914683635333488273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000068609789090222325515 13500102914683635333488273)
                  ·
                    refine ⟨10125077186012726500116205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13500102914683635333488273 10125077186012726500116205)
                    ·
                      refine ⟨3796903944754772437543577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125077186012726500116205 3796903944754772437543577)
                      ·
                        rfl

theorem cell23_7394444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_7394444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394444 prefixEnd_7394444 := by exact prefixLift 7394444
  have htrace : WordTrace (prefixWord ++ tailWord_7394444) baseStart_7394444 baseEnd_7394444 := by
    simpa [prefixWord, tailWord_7394444, baseEnd_7394444] using wordTrace_append hprefix tailTrace_7394444
  have hstable : (prefixWord ++ tailWord_7394444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394444).length < 2 ^ (prefixWord ++ tailWord_7394444).sum := by decide
  have hdescent : baseEnd_7394444 < baseStart_7394444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394471 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7394471 : Nat := 118140960795 + 7394471 * 2 ^ 59
def prefixEnd_7394471 : Nat := 4983230072969 + 3 ^ 40 * 7394471 * 2
def baseEnd_7394471 : Nat := 3796917808732443831905953

theorem tailTrace_7394471 : CollatzResearch.WordTrace tailWord_7394471 prefixEnd_7394471 3796917808732443831905953 := by
  unfold tailWord_7394471
  simp only [CollatzResearch.WordTrace]
  refine ⟨269698513994101916949287267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179799009329401277966191511 269698513994101916949287267)
  ·
    refine ⟨404547770991152875423930901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269698513994101916949287267 404547770991152875423930901)
    ·
      refine ⟨18963176765210291035496761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 404547770991152875423930901 18963176765210291035496761)
      ·
        refine ⟨14222382573907718276622571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18963176765210291035496761 14222382573907718276622571)
        ·
          refine ⟨21333573860861577414933857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14222382573907718276622571 21333573860861577414933857)
          ·
            refine ⟨16000180395646183061200393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21333573860861577414933857 16000180395646183061200393)
            ·
              refine ⟨12000135296734637295900295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16000180395646183061200393 12000135296734637295900295)
              ·
                refine ⟨18000202945101955943850443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000135296734637295900295 18000202945101955943850443)
                ·
                  refine ⟨27000304417652933915775665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18000202945101955943850443 27000304417652933915775665)
                  ·
                    refine ⟨20250228313239700436831749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27000304417652933915775665 20250228313239700436831749)
                    ·
                      refine ⟨3796917808732443831905953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20250228313239700436831749 3796917808732443831905953)
                      ·
                        rfl

theorem cell23_7394471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7394471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394471 prefixEnd_7394471 := by exact prefixLift 7394471
  have htrace : WordTrace (prefixWord ++ tailWord_7394471) baseStart_7394471 baseEnd_7394471 := by
    simpa [prefixWord, tailWord_7394471, baseEnd_7394471] using wordTrace_append hprefix tailTrace_7394471
  have hstable : (prefixWord ++ tailWord_7394471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394471).length < 2 ^ (prefixWord ++ tailWord_7394471).sum := by decide
  have hdescent : baseEnd_7394471 < baseStart_7394471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394487 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_7394487 : Nat := 118140960795 + 7394487 * 2 ^ 59
def prefixEnd_7394487 : Nat := 4983230072969 + 3 ^ 40 * 7394487 * 2
def baseEnd_7394487 : Nat := 3796926024422915769305879

theorem tailTrace_7394487 : CollatzResearch.WordTrace tailWord_7394487 prefixEnd_7394487 3796926024422915769305879 := by
  unfold tailWord_7394487
  simp only [CollatzResearch.WordTrace]
  refine ⟨269699097562043951681869715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179799398374695967787913143 269699097562043951681869715)
  ·
    refine ⟨404548646343065927522804573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269699097562043951681869715 404548646343065927522804573)
    ·
      refine ⟨151705742378649722821051715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404548646343065927522804573 151705742378649722821051715)
      ·
        refine ⟨227558613567974584231577573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151705742378649722821051715 227558613567974584231577573)
        ·
          refine ⟨42667240043995234543420795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227558613567974584231577573 42667240043995234543420795)
          ·
            refine ⟨64000860065992851815131193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42667240043995234543420795 64000860065992851815131193)
            ·
              refine ⟨48000645049494638861348395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64000860065992851815131193 48000645049494638861348395)
              ·
                refine ⟨72000967574241958292022593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48000645049494638861348395 72000967574241958292022593)
                ·
                  refine ⟨54000725680681468719016945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72000967574241958292022593 54000725680681468719016945)
                  ·
                    refine ⟨40500544260511101539262709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54000725680681468719016945 40500544260511101539262709)
                    ·
                      refine ⟨3796926024422915769305879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40500544260511101539262709 3796926024422915769305879)
                      ·
                        rfl

theorem cell23_7394487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_7394487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394487 prefixEnd_7394487 := by exact prefixLift 7394487
  have htrace : WordTrace (prefixWord ++ tailWord_7394487) baseStart_7394487 baseEnd_7394487 := by
    simpa [prefixWord, tailWord_7394487, baseEnd_7394487] using wordTrace_append hprefix tailTrace_7394487
  have hstable : (prefixWord ++ tailWord_7394487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394487).length < 2 ^ (prefixWord ++ tailWord_7394487).sum := by decide
  have hdescent : baseEnd_7394487 < baseStart_7394487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394525 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7394525 : Nat := 118140960795 + 7394525 * 2 ^ 59
def prefixEnd_7394525 : Nat := 4983230072969 + 3 ^ 40 * 7394525 * 2
def baseEnd_7394525 : Nat := 3796945536687786620630705

theorem tailTrace_7394525 : CollatzResearch.WordTrace tailWord_7394525 prefixEnd_7394525 3796945536687786620630705 := by
  unfold tailWord_7394525
  simp only [CollatzResearch.WordTrace]
  refine ⟨269700483535906284171753029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179800322357270856114502019 269700483535906284171753029)
  ·
    refine ⟨50568840662982428282203693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269700483535906284171753029 50568840662982428282203693)
    ·
      refine ⟨18963315248618410605826385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50568840662982428282203693 18963315248618410605826385)
      ·
        refine ⟨14222486436463807954369789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18963315248618410605826385 14222486436463807954369789)
        ·
          refine ⟨5333432413673927982888671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14222486436463807954369789 5333432413673927982888671)
          ·
            refine ⟨8000148620510891974333007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333432413673927982888671 8000148620510891974333007)
            ·
              refine ⟨12000222930766337961499511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000148620510891974333007 12000222930766337961499511)
              ·
                refine ⟨18000334396149506942249267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000222930766337961499511 18000334396149506942249267)
                ·
                  refine ⟨27000501594224260413373901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18000334396149506942249267 27000501594224260413373901)
                  ·
                    refine ⟨10125188097834097655015213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27000501594224260413373901 10125188097834097655015213)
                    ·
                      refine ⟨3796945536687786620630705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125188097834097655015213 3796945536687786620630705)
                      ·
                        rfl

theorem cell23_7394525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7394525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394525 prefixEnd_7394525 := by exact prefixLift 7394525
  have htrace : WordTrace (prefixWord ++ tailWord_7394525) baseStart_7394525 baseEnd_7394525 := by
    simpa [prefixWord, tailWord_7394525, baseEnd_7394525] using wordTrace_append hprefix tailTrace_7394525
  have hstable : (prefixWord ++ tailWord_7394525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394525).length < 2 ^ (prefixWord ++ tailWord_7394525).sum := by decide
  have hdescent : baseEnd_7394525 < baseStart_7394525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394535 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7394535 : Nat := 118140960795 + 7394535 * 2 ^ 59
def prefixEnd_7394535 : Nat := 4983230072969 + 3 ^ 40 * 7394535 * 2
def baseEnd_7394535 : Nat := 3796950671494331581505659

theorem tailTrace_7394535 : CollatzResearch.WordTrace tailWord_7394535 prefixEnd_7394535 3796950671494331581505659 := by
  unfold tailWord_7394535
  simp only [CollatzResearch.WordTrace]
  refine ⟨269700848265870055879617059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179800565510580037253078039 269700848265870055879617059)
  ·
    refine ⟨404551272398805083819425589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269700848265870055879617059 404551272398805083819425589)
    ·
      refine ⟨37926681787387976608071149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 404551272398805083819425589 37926681787387976608071149)
      ·
        refine ⟨14222505670270491228026681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37926681787387976608071149 14222505670270491228026681)
        ·
          refine ⟨10666879252702868421020011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14222505670270491228026681 10666879252702868421020011)
          ·
            refine ⟨16000318879054302631530017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666879252702868421020011 16000318879054302631530017)
            ·
              refine ⟨12000239159290726973647513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16000318879054302631530017 12000239159290726973647513)
              ·
                refine ⟨9000179369468045230235635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12000239159290726973647513 9000179369468045230235635)
                ·
                  refine ⟨13500269054202067845353453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000179369468045230235635 13500269054202067845353453)
                  ·
                    refine ⟨5062600895325775442007545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13500269054202067845353453 5062600895325775442007545)
                    ·
                      refine ⟨3796950671494331581505659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062600895325775442007545 3796950671494331581505659)
                      ·
                        rfl

theorem cell23_7394535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7394535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394535 prefixEnd_7394535 := by exact prefixLift 7394535
  have htrace : WordTrace (prefixWord ++ tailWord_7394535) baseStart_7394535 baseEnd_7394535 := by
    simpa [prefixWord, tailWord_7394535, baseEnd_7394535] using wordTrace_append hprefix tailTrace_7394535
  have hstable : (prefixWord ++ tailWord_7394535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394535).length < 2 ^ (prefixWord ++ tailWord_7394535).sum := by decide
  have hdescent : baseEnd_7394535 < baseStart_7394535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394557 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7394557 : Nat := 118140960795 + 7394557 * 2 ^ 59
def prefixEnd_7394557 : Nat := 4983230072969 + 3 ^ 40 * 7394557 * 2
def baseEnd_7394557 : Nat := 3796961968068730495430557

theorem tailTrace_7394557 : CollatzResearch.WordTrace tailWord_7394557 prefixEnd_7394557 3796961968068730495430557 := by
  unfold tailWord_7394557
  simp only [CollatzResearch.WordTrace]
  refine ⟨269701650671790353636917925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179801100447860235757945283 269701650671790353636917925)
  ·
    refine ⟨50569059500960691306922111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269701650671790353636917925 50569059500960691306922111)
    ·
      refine ⟨75853589251441036960383167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50569059500960691306922111 75853589251441036960383167)
      ·
        refine ⟨113780383877161555440574751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75853589251441036960383167 113780383877161555440574751)
        ·
          refine ⟨170670575815742333160862127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113780383877161555440574751 170670575815742333160862127)
          ·
            refine ⟨256005863723613499741293191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170670575815742333160862127 256005863723613499741293191)
            ·
              refine ⟨384008795585420249611939787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256005863723613499741293191 384008795585420249611939787)
              ·
                refine ⟨576013193378130374417909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384008795585420249611939787 576013193378130374417909681)
                ·
                  refine ⟨432009895033597780813432261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576013193378130374417909681 432009895033597780813432261)
                  ·
                    refine ⟨81001855318799583902518549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432009895033597780813432261 81001855318799583902518549)
                    ·
                      refine ⟨3796961968068730495430557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81001855318799583902518549 3796961968068730495430557)
                      ·
                        rfl

theorem cell23_7394557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7394557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394557 prefixEnd_7394557 := by exact prefixLift 7394557
  have htrace : WordTrace (prefixWord ++ tailWord_7394557) baseStart_7394557 baseEnd_7394557 := by
    simpa [prefixWord, tailWord_7394557, baseEnd_7394557] using wordTrace_append hprefix tailTrace_7394557
  have hstable : (prefixWord ++ tailWord_7394557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394557).length < 2 ^ (prefixWord ++ tailWord_7394557).sum := by decide
  have hdescent : baseEnd_7394557 < baseStart_7394557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394671 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_7394671 : Nat := 118140960795 + 7394671 * 2 ^ 59
def prefixEnd_7394671 : Nat := 4983230072969 + 3 ^ 40 * 7394671 * 2
def baseEnd_7394671 : Nat := 3797020504863343049405033

theorem tailTrace_7394671 : CollatzResearch.WordTrace tailWord_7394671 prefixEnd_7394671 3797020504863343049405033 := by
  unfold tailWord_7394671
  simp only [CollatzResearch.WordTrace]
  refine ⟨269705808593377351106567867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179803872395584900737711911 269705808593377351106567867)
  ·
    refine ⟨404558712890066026659851801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269705808593377351106567867 404558712890066026659851801)
    ·
      refine ⟨303419034667549519994888851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404558712890066026659851801 303419034667549519994888851)
      ·
        refine ⟨455128552001324279992333277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303419034667549519994888851 455128552001324279992333277)
        ·
          refine ⟨170673207000496604997124979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455128552001324279992333277 170673207000496604997124979)
          ·
            refine ⟨256009810500744907495687469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170673207000496604997124979 256009810500744907495687469)
            ·
              refine ⟨96003678937779340310882801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256009810500744907495687469 96003678937779340310882801)
              ·
                refine ⟨72002759203334505233162101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96003678937779340310882801 72002759203334505233162101)
                ·
                  refine ⟨6750258675312609865608947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72002759203334505233162101 6750258675312609865608947)
                  ·
                    refine ⟨10125388012968914798413421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750258675312609865608947 10125388012968914798413421)
                    ·
                      refine ⟨3797020504863343049405033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125388012968914798413421 3797020504863343049405033)
                      ·
                        rfl

theorem cell23_7394671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_7394671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394671 prefixEnd_7394671 := by exact prefixLift 7394671
  have htrace : WordTrace (prefixWord ++ tailWord_7394671) baseStart_7394671 baseEnd_7394671 := by
    simpa [prefixWord, tailWord_7394671, baseEnd_7394671] using wordTrace_append hprefix tailTrace_7394671
  have hstable : (prefixWord ++ tailWord_7394671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394671).length < 2 ^ (prefixWord ++ tailWord_7394671).sum := by decide
  have hdescent : baseEnd_7394671 < baseStart_7394671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394708 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7394708 : Nat := 118140960795 + 7394708 * 2 ^ 59
def prefixEnd_7394708 : Nat := 4983230072969 + 3 ^ 40 * 7394708 * 2
def baseEnd_7394708 : Nat := 1265679834549186468214121

theorem tailTrace_7394708 : CollatzResearch.WordTrace tailWord_7394708 prefixEnd_7394708 1265679834549186468214121 := by
  unfold tailWord_7394708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134853579047121653212832389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179804772062828870950443185 134853579047121653212832389)
  ·
    refine ⟨25285046071335309977406073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134853579047121653212832389 25285046071335309977406073)
    ·
      refine ⟨18963784553501482483054555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25285046071335309977406073 18963784553501482483054555)
      ·
        refine ⟨28445676830252223724581833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18963784553501482483054555 28445676830252223724581833)
        ·
          refine ⟨21334257622689167793436375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28445676830252223724581833 21334257622689167793436375)
          ·
            refine ⟨32001386434033751690154563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21334257622689167793436375 32001386434033751690154563)
            ·
              refine ⟨48002079651050627535231845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32001386434033751690154563 48002079651050627535231845)
              ·
                refine ⟨9000389934571992662855971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48002079651050627535231845 9000389934571992662855971)
                ·
                  refine ⟨13500584901857988994283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000389934571992662855971 13500584901857988994283957)
                  ·
                    refine ⟨1265679834549186468214121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13500584901857988994283957 1265679834549186468214121)
                    ·
                      rfl

theorem cell23_7394708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7394708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394708 prefixEnd_7394708 := by exact prefixLift 7394708
  have htrace : WordTrace (prefixWord ++ tailWord_7394708) baseStart_7394708 baseEnd_7394708 := by
    simpa [prefixWord, tailWord_7394708, baseEnd_7394708] using wordTrace_append hprefix tailTrace_7394708
  have hstable : (prefixWord ++ tailWord_7394708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394708).length < 2 ^ (prefixWord ++ tailWord_7394708).sum := by decide
  have hdescent : baseEnd_7394708 < baseStart_7394708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394711 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_7394711 : Nat := 118140960795 + 7394711 * 2 ^ 59
def prefixEnd_7394711 : Nat := 4983230072969 + 3 ^ 40 * 7394711 * 2
def baseEnd_7394711 : Nat := 3797041044089522892904849

theorem tailTrace_7394711 : CollatzResearch.WordTrace tailWord_7394711 prefixEnd_7394711 3797041044089522892904849 := by
  unfold tailWord_7394711
  simp only [CollatzResearch.WordTrace]
  refine ⟨269707267513232437938023987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179804845008821625292015991 269707267513232437938023987)
  ·
    refine ⟨404560901269848656907035981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269707267513232437938023987 404560901269848656907035981)
    ·
      refine ⟨151710337976193246340138493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404560901269848656907035981 151710337976193246340138493)
      ·
        refine ⟨56891376741072467377551935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151710337976193246340138493 56891376741072467377551935)
        ·
          refine ⟨85337065111608701066327903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56891376741072467377551935 85337065111608701066327903)
          ·
            refine ⟨128005597667413051599491855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85337065111608701066327903 128005597667413051599491855)
            ·
              refine ⟨192008396501119577399237783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128005597667413051599491855 192008396501119577399237783)
              ·
                refine ⟨288012594751679366098856675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192008396501119577399237783 288012594751679366098856675)
                ·
                  refine ⟨432018892127519049148285013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288012594751679366098856675 432018892127519049148285013)
                  ·
                    refine ⟨5062721392119363857206465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 432018892127519049148285013 5062721392119363857206465)
                    ·
                      refine ⟨3797041044089522892904849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062721392119363857206465 3797041044089522892904849)
                      ·
                        rfl

theorem cell23_7394711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_7394711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394711 prefixEnd_7394711 := by exact prefixLift 7394711
  have htrace : WordTrace (prefixWord ++ tailWord_7394711) baseStart_7394711 baseEnd_7394711 := by
    simpa [prefixWord, tailWord_7394711, baseEnd_7394711] using wordTrace_append hprefix tailTrace_7394711
  have hstable : (prefixWord ++ tailWord_7394711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394711).length < 2 ^ (prefixWord ++ tailWord_7394711).sum := by decide
  have hdescent : baseEnd_7394711 < baseStart_7394711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394722 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_7394722 : Nat := 118140960795 + 7394722 * 2 ^ 59
def prefixEnd_7394722 : Nat := 4983230072969 + 3 ^ 40 * 7394722 * 2
def baseEnd_7394722 : Nat := 3797046692376722349867299

theorem tailTrace_7394722 : CollatzResearch.WordTrace tailWord_7394722 prefixEnd_7394722 3797046692376722349867299 := by
  unfold tailWord_7394722
  simp only [CollatzResearch.WordTrace]
  refine ⟨67426917179048146704168605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179805112477461724544449613 67426917179048146704168605)
  ·
    refine ⟨25285093942143055014063227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67426917179048146704168605 25285093942143055014063227)
    ·
      refine ⟨37927640913214582521094841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25285093942143055014063227 37927640913214582521094841)
      ·
        refine ⟨28445730684910936890821131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37927640913214582521094841 28445730684910936890821131)
        ·
          refine ⟨42668596027366405336231697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28445730684910936890821131 42668596027366405336231697)
          ·
            refine ⟨32001447020524804002173773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42668596027366405336231697 32001447020524804002173773)
            ·
              refine ⟨12000542632696801500815165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32001447020524804002173773 12000542632696801500815165)
              ·
                refine ⟨4500203487261300562805687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12000542632696801500815165 4500203487261300562805687)
                ·
                  refine ⟨6750305230891950844208531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500203487261300562805687 6750305230891950844208531)
                  ·
                    refine ⟨10125457846337926266312797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750305230891950844208531 10125457846337926266312797)
                    ·
                      refine ⟨3797046692376722349867299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125457846337926266312797 3797046692376722349867299)
                      ·
                        rfl

theorem cell23_7394722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_7394722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394722 prefixEnd_7394722 := by exact prefixLift 7394722
  have htrace : WordTrace (prefixWord ++ tailWord_7394722) baseStart_7394722 baseEnd_7394722 := by
    simpa [prefixWord, tailWord_7394722, baseEnd_7394722] using wordTrace_append hprefix tailTrace_7394722
  have hstable : (prefixWord ++ tailWord_7394722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394722).length < 2 ^ (prefixWord ++ tailWord_7394722).sum := by decide
  have hdescent : baseEnd_7394722 < baseStart_7394722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394741 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7394741 : Nat := 118140960795 + 7394741 * 2 ^ 59
def prefixEnd_7394741 : Nat := 4983230072969 + 3 ^ 40 * 7394741 * 2
def baseEnd_7394741 : Nat := 3797056448509157775529711

theorem tailTrace_7394741 : CollatzResearch.WordTrace tailWord_7394741 prefixEnd_7394741 3797056448509157775529711 := by
  unfold tailWord_7394741
  simp only [CollatzResearch.WordTrace]
  refine ⟨269708361703123753061616077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179805574468749168707744051 269708361703123753061616077)
  ·
    refine ⟨101140635638671407398106029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269708361703123753061616077 101140635638671407398106029)
    ·
      refine ⟨37927738364501777774289761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101140635638671407398106029 37927738364501777774289761)
      ·
        refine ⟨28445803773376333330717321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37927738364501777774289761 28445803773376333330717321)
        ·
          refine ⟨21334352830032249998037991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28445803773376333330717321 21334352830032249998037991)
          ·
            refine ⟨32001529245048374997056987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21334352830032249998037991 32001529245048374997056987)
            ·
              refine ⟨48002293867572562495585481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32001529245048374997056987 48002293867572562495585481)
              ·
                refine ⟨36001720400679421871689111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48002293867572562495585481 36001720400679421871689111)
                ·
                  refine ⟨54002580601019132807533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36001720400679421871689111 54002580601019132807533667)
                  ·
                    refine ⟨81003870901528699211300501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54002580601019132807533667 81003870901528699211300501)
                    ·
                      refine ⟨3797056448509157775529711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81003870901528699211300501 3797056448509157775529711)
                      ·
                        rfl

theorem cell23_7394741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7394741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394741 prefixEnd_7394741 := by exact prefixLift 7394741
  have htrace : WordTrace (prefixWord ++ tailWord_7394741) baseStart_7394741 baseEnd_7394741 := by
    simpa [prefixWord, tailWord_7394741, baseEnd_7394741] using wordTrace_append hprefix tailTrace_7394741
  have hstable : (prefixWord ++ tailWord_7394741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394741).length < 2 ^ (prefixWord ++ tailWord_7394741).sum := by decide
  have hdescent : baseEnd_7394741 < baseStart_7394741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394761 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_7394761 : Nat := 118140960795 + 7394761 * 2 ^ 59
def prefixEnd_7394761 : Nat := 4983230072969 + 3 ^ 40 * 7394761 * 2
def baseEnd_7394761 : Nat := 3797066718122247697279619

theorem tailTrace_7394761 : CollatzResearch.WordTrace tailWord_7394761 prefixEnd_7394761 3797066718122247697279619 := by
  unfold tailWord_7394761
  simp only [CollatzResearch.WordTrace]
  refine ⟨269709091163051296477344137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179806060775367530984896091 269709091163051296477344137)
  ·
    refine ⟨202281818372288472358008103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269709091163051296477344137 202281818372288472358008103)
    ·
      refine ⟨303422727558432708537012155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202281818372288472358008103 303422727558432708537012155)
      ·
        refine ⟨455134091337649062805518233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303422727558432708537012155 455134091337649062805518233)
        ·
          refine ⟨341350568503236797104138675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455134091337649062805518233 341350568503236797104138675)
          ·
            refine ⟨512025852754855195656208013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341350568503236797104138675 512025852754855195656208013)
            ·
              refine ⟨192009694783070698371078005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512025852754855195656208013 192009694783070698371078005)
              ·
                refine ⟨18000908885912877972288563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192009694783070698371078005 18000908885912877972288563)
                ·
                  refine ⟨27001363328869316958432845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18000908885912877972288563 27001363328869316958432845)
                  ·
                    refine ⟨10125511248325993859412317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27001363328869316958432845 10125511248325993859412317)
                    ·
                      refine ⟨3797066718122247697279619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125511248325993859412317 3797066718122247697279619)
                      ·
                        rfl

theorem cell23_7394761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_7394761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394761 prefixEnd_7394761 := by exact prefixLift 7394761
  have htrace : WordTrace (prefixWord ++ tailWord_7394761) baseStart_7394761 baseEnd_7394761 := by
    simpa [prefixWord, tailWord_7394761, baseEnd_7394761] using wordTrace_append hprefix tailTrace_7394761
  have hstable : (prefixWord ++ tailWord_7394761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394761).length < 2 ^ (prefixWord ++ tailWord_7394761).sum := by decide
  have hdescent : baseEnd_7394761 < baseStart_7394761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394778 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_7394778 : Nat := 118140960795 + 7394778 * 2 ^ 59
def prefixEnd_7394778 : Nat := 4983230072969 + 3 ^ 40 * 7394778 * 2
def baseEnd_7394778 : Nat := 3797075447293374130767041

theorem tailTrace_7394778 : CollatzResearch.WordTrace tailWord_7394778 prefixEnd_7394778 3797075447293374130767041 := by
  unfold tailWord_7394778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67427427800997427095178247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179806474135993138920475325 67427427800997427095178247)
  ·
    refine ⟨101141141701496140642767371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67427427800997427095178247 101141141701496140642767371)
    ·
      refine ⟨151711712552244210964151057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101141141701496140642767371 151711712552244210964151057)
      ·
        refine ⟨113783784414183158223113293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151711712552244210964151057 113783784414183158223113293)
        ·
          refine ⟨42668919155318684333667485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113783784414183158223113293 42668919155318684333667485)
          ·
            refine ⟨16000844683244506625125307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42668919155318684333667485 16000844683244506625125307)
            ·
              refine ⟨24001267024866759937687961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16000844683244506625125307 24001267024866759937687961)
              ·
                refine ⟨18000950268650069953265971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24001267024866759937687961 18000950268650069953265971)
                ·
                  refine ⟨27001425402975104929898957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18000950268650069953265971 27001425402975104929898957)
                  ·
                    refine ⟨10125534526115664348712109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27001425402975104929898957 10125534526115664348712109)
                    ·
                      refine ⟨3797075447293374130767041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125534526115664348712109 3797075447293374130767041)
                      ·
                        rfl

theorem cell23_7394778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_7394778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394778 prefixEnd_7394778 := by exact prefixLift 7394778
  have htrace : WordTrace (prefixWord ++ tailWord_7394778) baseStart_7394778 baseEnd_7394778 := by
    simpa [prefixWord, tailWord_7394778, baseEnd_7394778] using wordTrace_append hprefix tailTrace_7394778
  have hstable : (prefixWord ++ tailWord_7394778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394778).length < 2 ^ (prefixWord ++ tailWord_7394778).sum := by decide
  have hdescent : baseEnd_7394778 < baseStart_7394778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394801 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7394801 : Nat := 118140960795 + 7394801 * 2 ^ 59
def prefixEnd_7394801 : Nat := 4983230072969 + 3 ^ 40 * 7394801 * 2
def baseEnd_7394801 : Nat := 3797087257348427540779435

theorem tailTrace_7394801 : CollatzResearch.WordTrace tailWord_7394801 prefixEnd_7394801 3797087257348427540779435 := by
  unfold tailWord_7394801
  simp only [CollatzResearch.WordTrace]
  refine ⟨269710550082906383308800257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179807033388604255539200171 269710550082906383308800257)
  ·
    refine ⟨202282912562179787481600193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269710550082906383308800257 202282912562179787481600193)
    ·
      refine ⟨151712184421634840611200145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202282912562179787481600193 151712184421634840611200145)
      ·
        refine ⟨113784138316226130458400109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151712184421634840611200145 113784138316226130458400109)
        ·
          refine ⟨42669051868584798921900041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113784138316226130458400109 42669051868584798921900041)
          ·
            refine ⟨32001788901438599191425031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42669051868584798921900041 32001788901438599191425031)
            ·
              refine ⟨48002683352157898787137547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32001788901438599191425031 48002683352157898787137547)
              ·
                refine ⟨72004025028236848180706321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48002683352157898787137547 72004025028236848180706321)
                ·
                  refine ⟨54003018771177636135529741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72004025028236848180706321 54003018771177636135529741)
                  ·
                    refine ⟨20251132039191613550823653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54003018771177636135529741 20251132039191613550823653)
                    ·
                      refine ⟨3797087257348427540779435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20251132039191613550823653 3797087257348427540779435)
                      ·
                        rfl

theorem cell23_7394801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7394801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394801 prefixEnd_7394801 := by exact prefixLift 7394801
  have htrace : WordTrace (prefixWord ++ tailWord_7394801) baseStart_7394801 baseEnd_7394801 := by
    simpa [prefixWord, tailWord_7394801, baseEnd_7394801] using wordTrace_append hprefix tailTrace_7394801
  have hstable : (prefixWord ++ tailWord_7394801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394801).length < 2 ^ (prefixWord ++ tailWord_7394801).sum := by decide
  have hdescent : baseEnd_7394801 < baseStart_7394801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394821 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_7394821 : Nat := 118140960795 + 7394821 * 2 ^ 59
def prefixEnd_7394821 : Nat := 4983230072969 + 3 ^ 40 * 7394821 * 2
def baseEnd_7394821 : Nat := 3797097526961517462529343

theorem tailTrace_7394821 : CollatzResearch.WordTrace tailWord_7394821 prefixEnd_7394821 3797097526961517462529343 := by
  unfold tailWord_7394821
  simp only [CollatzResearch.WordTrace]
  refine ⟨269711279542833926724528317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179807519695222617816352211 269711279542833926724528317)
  ·
    refine ⟨101141729828562722521698119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269711279542833926724528317 101141729828562722521698119)
    ·
      refine ⟨151712594742844083782547179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101141729828562722521698119 151712594742844083782547179)
      ·
        refine ⟨227568892114266125673820769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151712594742844083782547179 227568892114266125673820769)
        ·
          refine ⟨170676669085699594255365577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227568892114266125673820769 170676669085699594255365577)
          ·
            refine ⟨128007501814274695691524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170676669085699594255365577 128007501814274695691524183)
            ·
              refine ⟨192011252721412043537286275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128007501814274695691524183 192011252721412043537286275)
              ·
                refine ⟨288016879082118065305929413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192011252721412043537286275 288016879082118065305929413)
                ·
                  refine ⟨54003164827897137244861765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288016879082118065305929413 54003164827897137244861765)
                  ·
                    refine ⟨10125593405230713233411581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54003164827897137244861765 10125593405230713233411581)
                    ·
                      refine ⟨3797097526961517462529343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125593405230713233411581 3797097526961517462529343)
                      ·
                        rfl

theorem cell23_7394821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_7394821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394821 prefixEnd_7394821 := by exact prefixLift 7394821
  have htrace : WordTrace (prefixWord ++ tailWord_7394821) baseStart_7394821 baseEnd_7394821 := by
    simpa [prefixWord, tailWord_7394821, baseEnd_7394821] using wordTrace_append hprefix tailTrace_7394821
  have hstable : (prefixWord ++ tailWord_7394821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394821).length < 2 ^ (prefixWord ++ tailWord_7394821).sum := by decide
  have hdescent : baseEnd_7394821 < baseStart_7394821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394846 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7394846 : Nat := 118140960795 + 7394846 * 2 ^ 59
def prefixEnd_7394846 : Nat := 4983230072969 + 3 ^ 40 * 7394846 * 2
def baseEnd_7394846 : Nat := 3797110363977879864716729

theorem tailTrace_7394846 : CollatzResearch.WordTrace tailWord_7394846 prefixEnd_7394846 3797110363977879864716729 := by
  unfold tailWord_7394846
  simp only [CollatzResearch.WordTrace]
  refine ⟨33714023920967919499273549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179808127578495570662792261 33714023920967919499273549)
  ·
    refine ⟨12642758970362969812227581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33714023920967919499273549 12642758970362969812227581)
    ·
      refine ⟨4741034613886113679585343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12642758970362969812227581 4741034613886113679585343)
      ·
        refine ⟨7111551920829170519378015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741034613886113679585343 7111551920829170519378015)
        ·
          refine ⟨10667327881243755779067023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111551920829170519378015 10667327881243755779067023)
          ·
            refine ⟨16000991821865633668600535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10667327881243755779067023 16000991821865633668600535)
            ·
              refine ⟨24001487732798450502900803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16000991821865633668600535 24001487732798450502900803)
              ·
                refine ⟨36002231599197675754351205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24001487732798450502900803 36002231599197675754351205)
                ·
                  refine ⟨6750418424849564203940851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36002231599197675754351205 6750418424849564203940851)
                  ·
                    refine ⟨10125627637274346305911277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750418424849564203940851 10125627637274346305911277)
                    ·
                      refine ⟨3797110363977879864716729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125627637274346305911277 3797110363977879864716729)
                      ·
                        rfl

theorem cell23_7394846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7394846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394846 prefixEnd_7394846 := by exact prefixLift 7394846
  have htrace : WordTrace (prefixWord ++ tailWord_7394846) baseStart_7394846 baseEnd_7394846 := by
    simpa [prefixWord, tailWord_7394846, baseEnd_7394846] using wordTrace_append hprefix tailTrace_7394846
  have hstable : (prefixWord ++ tailWord_7394846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394846).length < 2 ^ (prefixWord ++ tailWord_7394846).sum := by decide
  have hdescent : baseEnd_7394846 < baseStart_7394846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394848 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7394848 : Nat := 118140960795 + 7394848 * 2 ^ 59
def prefixEnd_7394848 : Nat := 4983230072969 + 3 ^ 40 * 7394848 * 2
def baseEnd_7394848 : Nat := 3797111390939188856891719

theorem tailTrace_7394848 : CollatzResearch.WordTrace tailWord_7394848 prefixEnd_7394848 3797111390939188856891719 := by
  unfold tailWord_7394848
  simp only [CollatzResearch.WordTrace]
  refine ⟨134856132156868055167880599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179808176209157406890507465 134856132156868055167880599)
  ·
    refine ⟨202284198235302082751820899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134856132156868055167880599 202284198235302082751820899)
    ·
      refine ⟨303426297352953124127731349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202284198235302082751820899 303426297352953124127731349)
      ·
        refine ⟨14223107688419677693487407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303426297352953124127731349 14223107688419677693487407)
        ·
          refine ⟨21334661532629516540231111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14223107688419677693487407 21334661532629516540231111)
          ·
            refine ⟨32001992298944274810346667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21334661532629516540231111 32001992298944274810346667)
            ·
              refine ⟨48002988448416412215520001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32001992298944274810346667 48002988448416412215520001)
              ·
                refine ⟨36002241336312309161640001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48002988448416412215520001 36002241336312309161640001)
                ·
                  refine ⟨27001681002234231871230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36002241336312309161640001 27001681002234231871230001)
                  ·
                    refine ⟨20251260751675673903422501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27001681002234231871230001 20251260751675673903422501)
                    ·
                      refine ⟨3797111390939188856891719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20251260751675673903422501 3797111390939188856891719)
                      ·
                        rfl

theorem cell23_7394848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7394848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394848 prefixEnd_7394848 := by exact prefixLift 7394848
  have htrace : WordTrace (prefixWord ++ tailWord_7394848) baseStart_7394848 baseEnd_7394848 := by
    simpa [prefixWord, tailWord_7394848, baseEnd_7394848] using wordTrace_append hprefix tailTrace_7394848
  have hstable : (prefixWord ++ tailWord_7394848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394848).length < 2 ^ (prefixWord ++ tailWord_7394848).sum := by decide
  have hdescent : baseEnd_7394848 < baseStart_7394848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394858 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_7394858 : Nat := 118140960795 + 7394858 * 2 ^ 59
def prefixEnd_7394858 : Nat := 4983230072969 + 3 ^ 40 * 7394858 * 2
def baseEnd_7394858 : Nat := 421901836193970424196297

theorem tailTrace_7394858 : CollatzResearch.WordTrace tailWord_7394858 prefixEnd_7394858 421901836193970424196297 := by
  unfold tailWord_7394858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67428157260924970510906307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179808419362466588029083485 67428157260924970510906307)
  ·
    refine ⟨101142235891387455766359461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67428157260924970510906307 101142235891387455766359461)
    ·
      refine ⟨18964169229635147956192399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101142235891387455766359461 18964169229635147956192399)
      ·
        refine ⟨28446253844452721934288599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18964169229635147956192399 28446253844452721934288599)
        ·
          refine ⟨42669380766679082901432899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28446253844452721934288599 42669380766679082901432899)
          ·
            refine ⟨64004071150018624352149349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42669380766679082901432899 64004071150018624352149349)
            ·
              refine ⟨12000763340628492066028003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64004071150018624352149349 12000763340628492066028003)
              ·
                refine ⟨18001145010942738099042005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000763340628492066028003 18001145010942738099042005)
                ·
                  refine ⟨421901836193970424196297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18001145010942738099042005 421901836193970424196297)
                  ·
                    rfl

theorem cell23_7394858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_7394858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394858 prefixEnd_7394858 := by exact prefixLift 7394858
  have htrace : WordTrace (prefixWord ++ tailWord_7394858) baseStart_7394858 baseEnd_7394858 := by
    simpa [prefixWord, tailWord_7394858, baseEnd_7394858] using wordTrace_append hprefix tailTrace_7394858
  have hstable : (prefixWord ++ tailWord_7394858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394858).length < 2 ^ (prefixWord ++ tailWord_7394858).sum := by decide
  have hdescent : baseEnd_7394858 < baseStart_7394858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394869 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_7394869 : Nat := 118140960795 + 7394869 * 2 ^ 59
def prefixEnd_7394869 : Nat := 4983230072969 + 3 ^ 40 * 7394869 * 2
def baseEnd_7394869 : Nat := 3797122174032933274729123

theorem tailTrace_7394869 : CollatzResearch.WordTrace tailWord_7394869 prefixEnd_7394869 3797122174032933274729123 := by
  unfold tailWord_7394869
  simp only [CollatzResearch.WordTrace]
  refine ⟨269713030246660030922275661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179808686831106687281517107 269713030246660030922275661)
  ·
    refine ⟨101142386342497511595853373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269713030246660030922275661 101142386342497511595853373)
    ·
      refine ⟨37928394878436566848445015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101142386342497511595853373 37928394878436566848445015)
      ·
        refine ⟨56892592317654850272667523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37928394878436566848445015 56892592317654850272667523)
        ·
          refine ⟨85338888476482275409001285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56892592317654850272667523 85338888476482275409001285)
          ·
            refine ⟨16001041589340426639187741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85338888476482275409001285 16001041589340426639187741)
            ·
              refine ⟨6000390596002659989695403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16001041589340426639187741 6000390596002659989695403)
              ·
                refine ⟨9000585894003989984543105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000390596002659989695403 9000585894003989984543105)
                ·
                  refine ⟨6750439420502992488407329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000585894003989984543105 6750439420502992488407329)
                  ·
                    refine ⟨5062829565377244366305497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750439420502992488407329 5062829565377244366305497)
                    ·
                      refine ⟨3797122174032933274729123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062829565377244366305497 3797122174032933274729123)
                      ·
                        rfl

theorem cell23_7394869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_7394869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394869 prefixEnd_7394869 := by exact prefixLift 7394869
  have htrace : WordTrace (prefixWord ++ tailWord_7394869) baseStart_7394869 baseEnd_7394869 := by
    simpa [prefixWord, tailWord_7394869, baseEnd_7394869] using wordTrace_append hprefix tailTrace_7394869
  have hstable : (prefixWord ++ tailWord_7394869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394869).length < 2 ^ (prefixWord ++ tailWord_7394869).sum := by decide
  have hdescent : baseEnd_7394869 < baseStart_7394869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394871 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 7]
def baseStart_7394871 : Nat := 118140960795 + 7394871 * 2 ^ 59
def prefixEnd_7394871 : Nat := 4983230072969 + 3 ^ 40 * 7394871 * 2
def baseEnd_7394871 : Nat := 1265707733664747422301371

theorem tailTrace_7394871 : CollatzResearch.WordTrace tailWord_7394871 prefixEnd_7394871 1265707733664747422301371 := by
  unfold tailWord_7394871
  simp only [CollatzResearch.WordTrace]
  refine ⟨269713103192652785263848467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179808735461768523509232311 269713103192652785263848467)
  ·
    refine ⟨404569654788979177895772701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269713103192652785263848467 404569654788979177895772701)
    ·
      refine ⟨151713620545867191710914763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404569654788979177895772701 151713620545867191710914763)
      ·
        refine ⟨227570430818800787566372145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151713620545867191710914763 227570430818800787566372145)
        ·
          refine ⟨170677823114100590674779109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227570430818800787566372145 170677823114100590674779109)
          ·
            refine ⟨32002091833893860751521083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170677823114100590674779109 32002091833893860751521083)
            ·
              refine ⟨48003137750840791127281625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32002091833893860751521083 48003137750840791127281625)
              ·
                refine ⟨36002353313130593345461219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48003137750840791127281625 36002353313130593345461219)
                ·
                  refine ⟨54003529969695890018191829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36002353313130593345461219 54003529969695890018191829)
                  ·
                    refine ⟨1265707733664747422301371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54003529969695890018191829 1265707733664747422301371)
                    ·
                      rfl

theorem cell23_7394871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_7394871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394871 prefixEnd_7394871 := by exact prefixLift 7394871
  have htrace : WordTrace (prefixWord ++ tailWord_7394871) baseStart_7394871 baseEnd_7394871 := by
    simpa [prefixWord, tailWord_7394871, baseEnd_7394871] using wordTrace_append hprefix tailTrace_7394871
  have hstable : (prefixWord ++ tailWord_7394871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394871).length < 2 ^ (prefixWord ++ tailWord_7394871).sum := by decide
  have hdescent : baseEnd_7394871 < baseStart_7394871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394909 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 7]
def baseStart_7394909 : Nat := 118140960795 + 7394909 * 2 ^ 59
def prefixEnd_7394909 : Nat := 4983230072969 + 3 ^ 40 * 7394909 * 2
def baseEnd_7394909 : Nat := 421904745917679235358771

theorem tailTrace_7394909 : CollatzResearch.WordTrace tailWord_7394909 prefixEnd_7394909 421904745917679235358771 := by
  unfold tailWord_7394909
  simp only [CollatzResearch.WordTrace]
  refine ⟨269714489166515117753731781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179809659444343411835821187 269714489166515117753731781)
  ·
    refine ⟨50571466718721584578824709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269714489166515117753731781 50571466718721584578824709)
    ·
      refine ⟨9482150009760297108529633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50571466718721584578824709 9482150009760297108529633)
      ·
        refine ⟨7111612507320222831397225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9482150009760297108529633 7111612507320222831397225)
        ·
          refine ⟨5333709380490167123547919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111612507320222831397225 5333709380490167123547919)
          ·
            refine ⟨8000564070735250685321879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333709380490167123547919 8000564070735250685321879)
            ·
              refine ⟨12000846106102876027982819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000564070735250685321879 12000846106102876027982819)
              ·
                refine ⟨18001269159154314041974229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000846106102876027982819 18001269159154314041974229)
                ·
                  refine ⟨421904745917679235358771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18001269159154314041974229 421904745917679235358771)
                  ·
                    rfl

theorem cell23_7394909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_7394909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394909 prefixEnd_7394909 := by exact prefixLift 7394909
  have htrace : WordTrace (prefixWord ++ tailWord_7394909) baseStart_7394909 baseEnd_7394909 := by
    simpa [prefixWord, tailWord_7394909, baseEnd_7394909] using wordTrace_append hprefix tailTrace_7394909
  have hstable : (prefixWord ++ tailWord_7394909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394909).length < 2 ^ (prefixWord ++ tailWord_7394909).sum := by decide
  have hdescent : baseEnd_7394909 < baseStart_7394909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394921 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_7394921 : Nat := 118140960795 + 7394921 * 2 ^ 59
def prefixEnd_7394921 : Nat := 4983230072969 + 3 ^ 40 * 7394921 * 2
def baseEnd_7394921 : Nat := 3797148875026967071278883

theorem tailTrace_7394921 : CollatzResearch.WordTrace tailWord_7394921 prefixEnd_7394921 3797148875026967071278883 := by
  unfold tailWord_7394921
  simp only [CollatzResearch.WordTrace]
  refine ⟨269714926842471643803168617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179809951228314429202112411 269714926842471643803168617)
  ·
    refine ⟨202286195131853732852376463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269714926842471643803168617 202286195131853732852376463)
    ·
      refine ⟨303429292697780599278564695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202286195131853732852376463 303429292697780599278564695)
      ·
        refine ⟨455143939046670898917847043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303429292697780599278564695 455143939046670898917847043)
        ·
          refine ⟨682715908570006348376770565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455143939046670898917847043 682715908570006348376770565)
          ·
            refine ⟨128009232856876190320644481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 682715908570006348376770565 128009232856876190320644481)
            ·
              refine ⟨96006924642657142740483361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128009232856876190320644481 96006924642657142740483361)
              ·
                refine ⟨72005193481992857055362521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96006924642657142740483361 72005193481992857055362521)
                ·
                  refine ⟨54003895111494642791521891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72005193481992857055362521 54003895111494642791521891)
                  ·
                    refine ⟨81005842667241964187282837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54003895111494642791521891 81005842667241964187282837)
                    ·
                      refine ⟨3797148875026967071278883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81005842667241964187282837 3797148875026967071278883)
                      ·
                        rfl

theorem cell23_7394921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_7394921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394921 prefixEnd_7394921 := by exact prefixLift 7394921
  have htrace : WordTrace (prefixWord ++ tailWord_7394921) baseStart_7394921 baseEnd_7394921 := by
    simpa [prefixWord, tailWord_7394921, baseEnd_7394921] using wordTrace_append hprefix tailTrace_7394921
  have hstable : (prefixWord ++ tailWord_7394921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394921).length < 2 ^ (prefixWord ++ tailWord_7394921).sum := by decide
  have hdescent : baseEnd_7394921 < baseStart_7394921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7394945 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7394945 : Nat := 118140960795 + 7394945 * 2 ^ 59
def prefixEnd_7394945 : Nat := 4983230072969 + 3 ^ 40 * 7394945 * 2
def baseEnd_7394945 : Nat := 3797161198562674977378773

theorem tailTrace_7394945 : CollatzResearch.WordTrace tailWord_7394945 prefixEnd_7394945 3797161198562674977378773 := by
  unfold tailWord_7394945
  simp only [CollatzResearch.WordTrace]
  refine ⟨269715802194384695902042289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179810534796256463934694859 269715802194384695902042289)
  ·
    refine ⟨202286851645788521926531717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269715802194384695902042289 202286851645788521926531717)
    ·
      refine ⟨37928784683585347861224697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202286851645788521926531717 37928784683585347861224697)
      ·
        refine ⟨28446588512689010895918523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37928784683585347861224697 28446588512689010895918523)
        ·
          refine ⟨42669882769033516343877785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28446588512689010895918523 42669882769033516343877785)
          ·
            refine ⟨32002412076775137257908339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42669882769033516343877785 32002412076775137257908339)
            ·
              refine ⟨48003618115162705886862509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32002412076775137257908339 48003618115162705886862509)
              ·
                refine ⟨18001356793186014707573441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48003618115162705886862509 18001356793186014707573441)
                ·
                  refine ⟨13501017594889511030680081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18001356793186014707573441 13501017594889511030680081)
                  ·
                    refine ⟨10125763196167133273010061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501017594889511030680081 10125763196167133273010061)
                    ·
                      refine ⟨3797161198562674977378773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125763196167133273010061 3797161198562674977378773)
                      ·
                        rfl

theorem cell23_7394945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7394945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7394945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7394945 prefixEnd_7394945 := by exact prefixLift 7394945
  have htrace : WordTrace (prefixWord ++ tailWord_7394945) baseStart_7394945 baseEnd_7394945 := by
    simpa [prefixWord, tailWord_7394945, baseEnd_7394945] using wordTrace_append hprefix tailTrace_7394945
  have hstable : (prefixWord ++ tailWord_7394945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7394945).length < 2 ^ (prefixWord ++ tailWord_7394945).sum := by decide
  have hdescent : baseEnd_7394945 < baseStart_7394945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7394945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395002 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_7395002 : Nat := 118140960795 + 7395002 * 2 ^ 59
def prefixEnd_7395002 : Nat := 4983230072969 + 3 ^ 40 * 7395002 * 2
def baseEnd_7395002 : Nat := 3797190466959981254366011

theorem tailTrace_7395002 : CollatzResearch.WordTrace tailWord_7395002 prefixEnd_7395002 3797190466959981254366011 := by
  unfold tailWord_7395002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67429470288794548659216815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179811920770118796424578173 67429470288794548659216815)
  ·
    refine ⟨101144205433191822988825223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67429470288794548659216815 101144205433191822988825223)
    ·
      refine ⟨151716308149787734483237835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101144205433191822988825223 151716308149787734483237835)
      ·
        refine ⟨227574462224681601724856753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151716308149787734483237835 227574462224681601724856753)
        ·
          refine ⟨170680846668511201293642565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227574462224681601724856753 170680846668511201293642565)
          ·
            refine ⟨32002658750345850242557981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170680846668511201293642565 32002658750345850242557981)
            ·
              refine ⟨12000997031379693840959243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32002658750345850242557981 12000997031379693840959243)
              ·
                refine ⟨18001495547069540761438865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000997031379693840959243 18001495547069540761438865)
                ·
                  refine ⟨13501121660302155571079149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18001495547069540761438865 13501121660302155571079149)
                  ·
                    refine ⟨5062920622613308339154681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13501121660302155571079149 5062920622613308339154681)
                    ·
                      refine ⟨3797190466959981254366011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062920622613308339154681 3797190466959981254366011)
                      ·
                        rfl

theorem cell23_7395002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_7395002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395002 prefixEnd_7395002 := by exact prefixLift 7395002
  have htrace : WordTrace (prefixWord ++ tailWord_7395002) baseStart_7395002 baseEnd_7395002 := by
    simpa [prefixWord, tailWord_7395002, baseEnd_7395002] using wordTrace_append hprefix tailTrace_7395002
  have hstable : (prefixWord ++ tailWord_7395002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395002).length < 2 ^ (prefixWord ++ tailWord_7395002).sum := by decide
  have hdescent : baseEnd_7395002 < baseStart_7395002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395008 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_7395008 : Nat := 118140960795 + 7395008 * 2 ^ 59
def prefixEnd_7395008 : Nat := 4983230072969 + 3 ^ 40 * 7395008 * 2
def baseEnd_7395008 : Nat := 1265731182614636076963661

theorem tailTrace_7395008 : CollatzResearch.WordTrace tailWord_7395008 prefixEnd_7395008 1265731182614636076963661 := by
  unfold tailWord_7395008
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859049996578228830792839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179812066662104305107723785 134859049996578228830792839)
  ·
    refine ⟨202288574994867343246189259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134859049996578228830792839 202288574994867343246189259)
    ·
      refine ⟨303432862492301014869283889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202288574994867343246189259 303432862492301014869283889)
      ·
        refine ⟨227574646869225761151962917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303432862492301014869283889 227574646869225761151962917)
        ·
          refine ⟨42670246287979830215993047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227574646869225761151962917 42670246287979830215993047)
          ·
            refine ⟨64005369431969745323989571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42670246287979830215993047 64005369431969745323989571)
            ·
              refine ⟨96008054147954617985984357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64005369431969745323989571 96008054147954617985984357)
              ·
                refine ⟨18001510152741490872372067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96008054147954617985984357 18001510152741490872372067)
                ·
                  refine ⟨27002265229112236308558101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18001510152741490872372067 27002265229112236308558101)
                  ·
                    refine ⟨1265731182614636076963661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27002265229112236308558101 1265731182614636076963661)
                    ·
                      rfl

theorem cell23_7395008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_7395008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395008 prefixEnd_7395008 := by exact prefixLift 7395008
  have htrace : WordTrace (prefixWord ++ tailWord_7395008) baseStart_7395008 baseEnd_7395008 := by
    simpa [prefixWord, tailWord_7395008, baseEnd_7395008] using wordTrace_append hprefix tailTrace_7395008
  have hstable : (prefixWord ++ tailWord_7395008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395008).length < 2 ^ (prefixWord ++ tailWord_7395008).sum := by decide
  have hdescent : baseEnd_7395008 < baseStart_7395008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395015 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_7395015 : Nat := 118140960795 + 7395015 * 2 ^ 59
def prefixEnd_7395015 : Nat := 4983230072969 + 3 ^ 40 * 7395015 * 2
def baseEnd_7395015 : Nat := 3797197142208489703503451

theorem tailTrace_7395015 : CollatzResearch.WordTrace tailWord_7395015 prefixEnd_7395015 3797197142208489703503451 := by
  unfold tailWord_7395015
  simp only [CollatzResearch.WordTrace]
  refine ⟨269718355304131097857090499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179812236869420731904726999 269718355304131097857090499)
  ·
    refine ⟨404577532956196646785635749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269718355304131097857090499 404577532956196646785635749)
    ·
      refine ⟨75858287429286871272306703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404577532956196646785635749 75858287429286871272306703)
      ·
        refine ⟨113787431143930306908460055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75858287429286871272306703 113787431143930306908460055)
        ·
          refine ⟨170681146715895460362690083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113787431143930306908460055 170681146715895460362690083)
          ·
            refine ⟨256021720073843190544035125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170681146715895460362690083 256021720073843190544035125)
            ·
              refine ⟨24002036256922799113503293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256021720073843190544035125 24002036256922799113503293)
              ·
                refine ⟨9000763596346049667563735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24002036256922799113503293 9000763596346049667563735)
                ·
                  refine ⟨13501145394519074501345603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000763596346049667563735 13501145394519074501345603)
                  ·
                    refine ⟨20251718091778611752018405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13501145394519074501345603 20251718091778611752018405)
                    ·
                      refine ⟨3797197142208489703503451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20251718091778611752018405 3797197142208489703503451)
                      ·
                        rfl

theorem cell23_7395015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_7395015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395015 prefixEnd_7395015 := by exact prefixLift 7395015
  have htrace : WordTrace (prefixWord ++ tailWord_7395015) baseStart_7395015 baseEnd_7395015 := by
    simpa [prefixWord, tailWord_7395015, baseEnd_7395015] using wordTrace_append hprefix tailTrace_7395015
  have hstable : (prefixWord ++ tailWord_7395015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395015).length < 2 ^ (prefixWord ++ tailWord_7395015).sum := by decide
  have hdescent : baseEnd_7395015 < baseStart_7395015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395025 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_7395025 : Nat := 118140960795 + 7395025 * 2 ^ 59
def prefixEnd_7395025 : Nat := 4983230072969 + 3 ^ 40 * 7395025 * 2
def baseEnd_7395025 : Nat := 1265734092338344888126135

theorem tailTrace_7395025 : CollatzResearch.WordTrace tailWord_7395025 prefixEnd_7395025 1265734092338344888126135 := by
  unfold tailWord_7395025
  simp only [CollatzResearch.WordTrace]
  refine ⟨269718720034094869564954529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179812480022729913043303019 269718720034094869564954529)
  ·
    refine ⟨202289040025571152173715897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269718720034094869564954529 202289040025571152173715897)
    ·
      refine ⟨151716780019178364130286923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202289040025571152173715897 151716780019178364130286923)
      ·
        refine ⟨227575170028767546195430385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151716780019178364130286923 227575170028767546195430385)
        ·
          refine ⟨170681377521575659646572789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227575170028767546195430385 170681377521575659646572789)
          ·
            refine ⟨16001379142647718091866199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170681377521575659646572789 16001379142647718091866199)
            ·
              refine ⟨24002068713971577137799299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16001379142647718091866199 24002068713971577137799299)
              ·
                refine ⟨36003103070957365706698949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002068713971577137799299 36003103070957365706698949)
                ·
                  refine ⟨6750581825804506070006053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36003103070957365706698949 6750581825804506070006053)
                  ·
                    refine ⟨1265734092338344888126135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750581825804506070006053 1265734092338344888126135)
                    ·
                      rfl

theorem cell23_7395025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_7395025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395025 prefixEnd_7395025 := by exact prefixLift 7395025
  have htrace : WordTrace (prefixWord ++ tailWord_7395025) baseStart_7395025 baseEnd_7395025 := by
    simpa [prefixWord, tailWord_7395025, baseEnd_7395025] using wordTrace_append hprefix tailTrace_7395025
  have hstable : (prefixWord ++ tailWord_7395025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395025).length < 2 ^ (prefixWord ++ tailWord_7395025).sum := by decide
  have hdescent : baseEnd_7395025 < baseStart_7395025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395060 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7395060 : Nat := 118140960795 + 7395060 * 2 ^ 59
def prefixEnd_7395060 : Nat := 4983230072969 + 3 ^ 40 * 7395060 * 2
def baseEnd_7395060 : Nat := 3797220248837942027440745

theorem tailTrace_7395060 : CollatzResearch.WordTrace tailWord_7395060 prefixEnd_7395060 3797220248837942027440745 := by
  unfold tailWord_7395060
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859998294484035271239317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179813331059312047028319089 134859998294484035271239317)
  ·
    refine ⟨6321562420053939153339343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134859998294484035271239317 6321562420053939153339343)
    ·
      refine ⟨9482343630080908730009015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321562420053939153339343 9482343630080908730009015)
      ·
        refine ⟨14223515445121363095013523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482343630080908730009015 14223515445121363095013523)
        ·
          refine ⟨21335273167682044642520285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14223515445121363095013523 21335273167682044642520285)
          ·
            refine ⟨8000727437880766740945107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21335273167682044642520285 8000727437880766740945107)
            ·
              refine ⟨12001091156821150111417661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000727437880766740945107 12001091156821150111417661)
              ·
                refine ⟨4500409183807931291781623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12001091156821150111417661 4500409183807931291781623)
                ·
                  refine ⟨6750613775711896937672435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500409183807931291781623 6750613775711896937672435)
                  ·
                    refine ⟨10125920663567845406508653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750613775711896937672435 10125920663567845406508653)
                    ·
                      refine ⟨3797220248837942027440745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125920663567845406508653 3797220248837942027440745)
                      ·
                        rfl

theorem cell23_7395060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7395060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395060 prefixEnd_7395060 := by exact prefixLift 7395060
  have htrace : WordTrace (prefixWord ++ tailWord_7395060) baseStart_7395060 baseEnd_7395060 := by
    simpa [prefixWord, tailWord_7395060, baseEnd_7395060] using wordTrace_append hprefix tailTrace_7395060
  have hstable : (prefixWord ++ tailWord_7395060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395060).length < 2 ^ (prefixWord ++ tailWord_7395060).sum := by decide
  have hdescent : baseEnd_7395060 < baseStart_7395060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395082 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_7395082 : Nat := 118140960795 + 7395082 * 2 ^ 59
def prefixEnd_7395082 : Nat := 4983230072969 + 3 ^ 40 * 7395082 * 2
def baseEnd_7395082 : Nat := 3797231545412340941365643

theorem tailTrace_7395082 : CollatzResearch.WordTrace tailWord_7395082 prefixEnd_7395082 3797231545412340941365643 := by
  unfold tailWord_7395082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67430199748722092074944875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179813865996592245533186333 67430199748722092074944875)
  ·
    refine ⟨101145299623083138112417313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67430199748722092074944875 101145299623083138112417313)
    ·
      refine ⟨75858974717312353584312985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101145299623083138112417313 75858974717312353584312985)
      ·
        refine ⟨56894231037984265188234739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75858974717312353584312985 56894231037984265188234739)
        ·
          refine ⟨85341346556976397782352109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56894231037984265188234739 85341346556976397782352109)
          ·
            refine ⟨32003004958866149168382041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85341346556976397782352109 32003004958866149168382041)
            ·
              refine ⟨24002253719149611876286531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32003004958866149168382041 24002253719149611876286531)
              ·
                refine ⟨36003380578724417814429797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002253719149611876286531 36003380578724417814429797)
                ·
                  refine ⟨6750633858510828340205587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36003380578724417814429797 6750633858510828340205587)
                  ·
                    refine ⟨10125950787766242510308381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750633858510828340205587 10125950787766242510308381)
                    ·
                      refine ⟨3797231545412340941365643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10125950787766242510308381 3797231545412340941365643)
                      ·
                        rfl

theorem cell23_7395082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_7395082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395082 prefixEnd_7395082 := by exact prefixLift 7395082
  have htrace : WordTrace (prefixWord ++ tailWord_7395082) baseStart_7395082 baseEnd_7395082 := by
    simpa [prefixWord, tailWord_7395082, baseEnd_7395082] using wordTrace_append hprefix tailTrace_7395082
  have hstable : (prefixWord ++ tailWord_7395082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395082).length < 2 ^ (prefixWord ++ tailWord_7395082).sum := by decide
  have hdescent : baseEnd_7395082 < baseStart_7395082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395109 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_7395109 : Nat := 118140960795 + 7395109 * 2 ^ 59
def prefixEnd_7395109 : Nat := 4983230072969 + 3 ^ 40 * 7395109 * 2
def baseEnd_7395109 : Nat := 3797245409390012335728019

theorem tailTrace_7395109 : CollatzResearch.WordTrace tailWord_7395109 prefixEnd_7395109 3797245409390012335728019 := by
  unfold tailWord_7395109
  simp only [CollatzResearch.WordTrace]
  refine ⟨269721783765790551911012381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179814522510527034607341587 269721783765790551911012381)
  ·
    refine ⟨101145668912171456966629643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269721783765790551911012381 101145668912171456966629643)
    ·
      refine ⟨151718503368257185449944465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101145668912171456966629643 151718503368257185449944465)
      ·
        refine ⟨113788877526192889087458349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151718503368257185449944465 113788877526192889087458349)
        ·
          refine ⟨42670829072322333407796881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113788877526192889087458349 42670829072322333407796881)
          ·
            refine ⟨32003121804241750055847661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42670829072322333407796881 32003121804241750055847661)
            ·
              refine ⟨12001170676590656270942873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32003121804241750055847661 12001170676590656270942873)
              ·
                refine ⟨9000878007442992203207155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001170676590656270942873 9000878007442992203207155)
                ·
                  refine ⟨13501317011164488304810733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000878007442992203207155 13501317011164488304810733)
                  ·
                    refine ⟨5062993879186683114304025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13501317011164488304810733 5062993879186683114304025)
                    ·
                      refine ⟨3797245409390012335728019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5062993879186683114304025 3797245409390012335728019)
                      ·
                        rfl

theorem cell23_7395109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_7395109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395109 prefixEnd_7395109 := by exact prefixLift 7395109
  have htrace : WordTrace (prefixWord ++ tailWord_7395109) baseStart_7395109 baseEnd_7395109 := by
    simpa [prefixWord, tailWord_7395109, baseEnd_7395109] using wordTrace_append hprefix tailTrace_7395109
  have hstable : (prefixWord ++ tailWord_7395109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395109).length < 2 ^ (prefixWord ++ tailWord_7395109).sum := by decide
  have hdescent : baseEnd_7395109 < baseStart_7395109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395122 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_7395122 : Nat := 118140960795 + 7395122 * 2 ^ 59
def prefixEnd_7395122 : Nat := 4983230072969 + 3 ^ 40 * 7395122 * 2
def baseEnd_7395122 : Nat := 3797252084638520784865459

theorem tailTrace_7395122 : CollatzResearch.WordTrace tailWord_7395122 prefixEnd_7395122 3797252084638520784865459 := by
  unfold tailWord_7395122
  simp only [CollatzResearch.WordTrace]
  refine ⟨67430564478685863782808905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179814838609828970087490413 67430564478685863782808905)
  ·
    refine ⟨50572923359014397837106679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67430564478685863782808905 50572923359014397837106679)
    ·
      refine ⟨75859385038521596755660019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50572923359014397837106679 75859385038521596755660019)
      ·
        refine ⟨113789077557782395133490029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75859385038521596755660019 113789077557782395133490029)
        ·
          refine ⟨42670904084168398175058761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113789077557782395133490029 42670904084168398175058761)
          ·
            refine ⟨32003178063126298631294071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42670904084168398175058761 32003178063126298631294071)
            ·
              refine ⟨48004767094689447946941107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32003178063126298631294071 48004767094689447946941107)
              ·
                refine ⟨72007150642034171920411661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48004767094689447946941107 72007150642034171920411661)
                ·
                  refine ⟨27002681490762814470154373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72007150642034171920411661 27002681490762814470154373)
                  ·
                    refine ⟨5063002779518027713153945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27002681490762814470154373 5063002779518027713153945)
                    ·
                      refine ⟨3797252084638520784865459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063002779518027713153945 3797252084638520784865459)
                      ·
                        rfl

theorem cell23_7395122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_7395122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395122 prefixEnd_7395122 := by exact prefixLift 7395122
  have htrace : WordTrace (prefixWord ++ tailWord_7395122) baseStart_7395122 baseEnd_7395122 := by
    simpa [prefixWord, tailWord_7395122, baseEnd_7395122] using wordTrace_append hprefix tailTrace_7395122
  have hstable : (prefixWord ++ tailWord_7395122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395122).length < 2 ^ (prefixWord ++ tailWord_7395122).sum := by decide
  have hdescent : baseEnd_7395122 < baseStart_7395122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395139 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 2, 2, 2]
def baseStart_7395139 : Nat := 118140960795 + 7395139 * 2 ^ 59
def prefixEnd_7395139 : Nat := 4983230072969 + 3 ^ 40 * 7395139 * 2
def baseEnd_7395139 : Nat := 3797260813809647218352881

theorem tailTrace_7395139 : CollatzResearch.WordTrace tailWord_7395139 prefixEnd_7395139 3797260813809647218352881 := by
  unfold tailWord_7395139
  simp only [CollatzResearch.WordTrace]
  refine ⟨269722877955681867034604471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179815251970454578023069647 269722877955681867034604471)
  ·
    refine ⟨404584316933522800551906707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269722877955681867034604471 404584316933522800551906707)
    ·
      refine ⟨606876475400284200827860061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404584316933522800551906707 606876475400284200827860061)
      ·
        refine ⟨227578678275106575310447523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606876475400284200827860061 227578678275106575310447523)
        ·
          refine ⟨341368017412659862965671285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227578678275106575310447523 341368017412659862965671285)
          ·
            refine ⟨32003251632436862153031683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341368017412659862965671285 32003251632436862153031683)
            ·
              refine ⟨48004877448655293229547525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32003251632436862153031683 48004877448655293229547525)
              ·
                refine ⟨9000914521622867480540161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48004877448655293229547525 9000914521622867480540161)
                ·
                  refine ⟨6750685891217150610405121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000914521622867480540161 6750685891217150610405121)
                  ·
                    refine ⟨5063014418412862957803841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750685891217150610405121 5063014418412862957803841)
                    ·
                      refine ⟨3797260813809647218352881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063014418412862957803841 3797260813809647218352881)
                      ·
                        rfl

theorem cell23_7395139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_7395139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395139 prefixEnd_7395139 := by exact prefixLift 7395139
  have htrace : WordTrace (prefixWord ++ tailWord_7395139) baseStart_7395139 baseEnd_7395139 := by
    simpa [prefixWord, tailWord_7395139, baseEnd_7395139] using wordTrace_append hprefix tailTrace_7395139
  have hstable : (prefixWord ++ tailWord_7395139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395139).length < 2 ^ (prefixWord ++ tailWord_7395139).sum := by decide
  have hdescent : baseEnd_7395139 < baseStart_7395139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395156 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_7395156 : Nat := 118140960795 + 7395156 * 2 ^ 59
def prefixEnd_7395156 : Nat := 4983230072969 + 3 ^ 40 * 7395156 * 2
def baseEnd_7395156 : Nat := 3797269542980773651840303

theorem tailTrace_7395156 : CollatzResearch.WordTrace tailWord_7395156 prefixEnd_7395156 3797269542980773651840303 := by
  unfold tailWord_7395156
  simp only [CollatzResearch.WordTrace]
  refine ⟨134861748998310139468986661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179815665331080185958648881 134861748998310139468986661)
  ·
    refine ⟨25286577937183151150434999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134861748998310139468986661 25286577937183151150434999)
    ·
      refine ⟨37929866905774726725652499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25286577937183151150434999 37929866905774726725652499)
      ·
        refine ⟨56894800358662090088478749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37929866905774726725652499 56894800358662090088478749)
        ·
          refine ⟨21335550134498283783179531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56894800358662090088478749 21335550134498283783179531)
          ·
            refine ⟨32003325201747425674769297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21335550134498283783179531 32003325201747425674769297)
            ·
              refine ⟨24002493901310569256076973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32003325201747425674769297 24002493901310569256076973)
              ·
                refine ⟨9000935212991463471028865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24002493901310569256076973 9000935212991463471028865)
                ·
                  refine ⟨6750701409743597603271649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000935212991463471028865 6750701409743597603271649)
                  ·
                    refine ⟨5063026057307698202453737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750701409743597603271649 5063026057307698202453737)
                    ·
                      refine ⟨3797269542980773651840303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063026057307698202453737 3797269542980773651840303)
                      ·
                        rfl

theorem cell23_7395156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_7395156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395156 prefixEnd_7395156 := by exact prefixLift 7395156
  have htrace : WordTrace (prefixWord ++ tailWord_7395156) baseStart_7395156 baseEnd_7395156 := by
    simpa [prefixWord, tailWord_7395156, baseEnd_7395156] using wordTrace_append hprefix tailTrace_7395156
  have hstable : (prefixWord ++ tailWord_7395156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395156).length < 2 ^ (prefixWord ++ tailWord_7395156).sum := by decide
  have hdescent : baseEnd_7395156 < baseStart_7395156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395175 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 7]
def baseStart_7395175 : Nat := 118140960795 + 7395175 * 2 ^ 59
def prefixEnd_7395175 : Nat := 4983230072969 + 3 ^ 40 * 7395175 * 2
def baseEnd_7395175 : Nat := 1265759766371069692500905

theorem tailTrace_7395175 : CollatzResearch.WordTrace tailWord_7395175 prefixEnd_7395175 1265759766371069692500905 := by
  unfold tailWord_7395175
  simp only [CollatzResearch.WordTrace]
  refine ⟨269724190983551445182914979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179816127322367630121943319 269724190983551445182914979)
  ·
    refine ⟨404586286475327167774372469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269724190983551445182914979 404586286475327167774372469)
    ·
      refine ⟨37929964357061921978847419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 404586286475327167774372469 37929964357061921978847419)
      ·
        refine ⟨56894946535592882968271129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37929964357061921978847419 56894946535592882968271129)
        ·
          refine ⟨42671209901694662226203347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56894946535592882968271129 42671209901694662226203347)
          ·
            refine ⟨64006814852541993339305021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42671209901694662226203347 64006814852541993339305021)
            ·
              refine ⟨24002555569703247502239383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64006814852541993339305021 24002555569703247502239383)
              ·
                refine ⟨36003833354554871253359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002555569703247502239383 36003833354554871253359075)
                ·
                  refine ⟨54005750031832306880038613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36003833354554871253359075 54005750031832306880038613)
                  ·
                    refine ⟨1265759766371069692500905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54005750031832306880038613 1265759766371069692500905)
                    ·
                      rfl

theorem cell23_7395175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_7395175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395175 prefixEnd_7395175 := by exact prefixLift 7395175
  have htrace : WordTrace (prefixWord ++ tailWord_7395175) baseStart_7395175 baseEnd_7395175 := by
    simpa [prefixWord, tailWord_7395175, baseEnd_7395175] using wordTrace_append hprefix tailTrace_7395175
  have hstable : (prefixWord ++ tailWord_7395175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395175).length < 2 ^ (prefixWord ++ tailWord_7395175).sum := by decide
  have hdescent : baseEnd_7395175 < baseStart_7395175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395190 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7395190 : Nat := 118140960795 + 7395190 * 2 ^ 59
def prefixEnd_7395190 : Nat := 4983230072969 + 3 ^ 40 * 7395190 * 2
def baseEnd_7395190 : Nat := 3797287001323026518815147

theorem tailTrace_7395190 : CollatzResearch.WordTrace tailWord_7395190 prefixEnd_7395190 3797287001323026518815147 := by
  unfold tailWord_7395190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857796129906068921544439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179816492052331401829807349 16857796129906068921544439)
  ·
    refine ⟨25286694194859103382316659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16857796129906068921544439 25286694194859103382316659)
    ·
      refine ⟨37930041292288655073474989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25286694194859103382316659 37930041292288655073474989)
      ·
        refine ⟨14223765484608245652553121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37930041292288655073474989 14223765484608245652553121)
        ·
          refine ⟨10667824113456184239414841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14223765484608245652553121 10667824113456184239414841)
          ·
            refine ⟨8000868085092138179561131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667824113456184239414841 8000868085092138179561131)
            ·
              refine ⟨12001302127638207269341697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000868085092138179561131 12001302127638207269341697)
              ·
                refine ⟨9000976595728655452006273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001302127638207269341697 9000976595728655452006273)
                ·
                  refine ⟨6750732446796491589004705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000976595728655452006273 6750732446796491589004705)
                  ·
                    refine ⟨5063049335097368691753529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750732446796491589004705 5063049335097368691753529)
                    ·
                      refine ⟨3797287001323026518815147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063049335097368691753529 3797287001323026518815147)
                      ·
                        rfl

theorem cell23_7395190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7395190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395190 prefixEnd_7395190 := by exact prefixLift 7395190
  have htrace : WordTrace (prefixWord ++ tailWord_7395190) baseStart_7395190 baseEnd_7395190 := by
    simpa [prefixWord, tailWord_7395190, baseEnd_7395190] using wordTrace_append hprefix tailTrace_7395190
  have hstable : (prefixWord ++ tailWord_7395190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395190).length < 2 ^ (prefixWord ++ tailWord_7395190).sum := by decide
  have hdescent : baseEnd_7395190 < baseStart_7395190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395195 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4]
def baseStart_7395195 : Nat := 118140960795 + 7395195 * 2 ^ 59
def prefixEnd_7395195 : Nat := 4983230072969 + 3 ^ 40 * 7395195 * 2
def baseEnd_7395195 : Nat := 3797289568726298999252623

theorem tailTrace_7395195 : CollatzResearch.WordTrace tailWord_7395195 prefixEnd_7395195 3797289568726298999252623 := by
  unfold tailWord_7395195
  simp only [CollatzResearch.WordTrace]
  refine ⟨269724920443478988598643039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179816613628985992399095359 269724920443478988598643039)
  ·
    refine ⟨404587380665218482897964559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269724920443478988598643039 404587380665218482897964559)
    ·
      refine ⟨606881070997827724346946839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404587380665218482897964559 606881070997827724346946839)
      ·
        refine ⟨910321606496741586520420259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606881070997827724346946839 910321606496741586520420259)
        ·
          refine ⟨1365482409745112379780630389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910321606496741586520420259 1365482409745112379780630389)
          ·
            refine ⟨128013975913604285604434099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1365482409745112379780630389 128013975913604285604434099)
            ·
              refine ⟨192020963870406428406651149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128013975913604285604434099 192020963870406428406651149)
              ·
                refine ⟨72007861451402410652494181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192020963870406428406651149 72007861451402410652494181)
                ·
                  refine ⟨13501474022137951997342659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72007861451402410652494181 13501474022137951997342659)
                  ·
                    refine ⟨20252211033206927996013989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13501474022137951997342659 20252211033206927996013989)
                    ·
                      refine ⟨3797289568726298999252623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20252211033206927996013989 3797289568726298999252623)
                      ·
                        rfl

theorem cell23_7395195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_7395195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395195 prefixEnd_7395195 := by exact prefixLift 7395195
  have htrace : WordTrace (prefixWord ++ tailWord_7395195) baseStart_7395195 baseEnd_7395195 := by
    simpa [prefixWord, tailWord_7395195, baseEnd_7395195] using wordTrace_append hprefix tailTrace_7395195
  have hstable : (prefixWord ++ tailWord_7395195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395195).length < 2 ^ (prefixWord ++ tailWord_7395195).sum := by decide
  have hdescent : baseEnd_7395195 < baseStart_7395195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395230 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7395230 : Nat := 118140960795 + 7395230 * 2 ^ 59
def prefixEnd_7395230 : Nat := 4983230072969 + 3 ^ 40 * 7395230 * 2
def baseEnd_7395230 : Nat := 421923060061022929146107

theorem tailTrace_7395230 : CollatzResearch.WordTrace tailWord_7395230 prefixEnd_7395230 421923060061022929146107 := by
  unfold tailWord_7395230
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715774624794023697020893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179817464665568126384111429 33715774624794023697020893)
  ·
    refine ⟨12643415484297758886382835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33715774624794023697020893 12643415484297758886382835)
    ·
      refine ⟨18965123226446638329574253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643415484297758886382835 18965123226446638329574253)
      ·
        refine ⟨7111921209917489373590345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18965123226446638329574253 7111921209917489373590345)
        ·
          refine ⟨5333940907438117030192759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111921209917489373590345 5333940907438117030192759)
          ·
            refine ⟨8000911361157175545289139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333940907438117030192759 8000911361157175545289139)
            ·
              refine ⟨12001367041735763317933709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000911361157175545289139 12001367041735763317933709)
              ·
                refine ⟨4500512640650911244225141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12001367041735763317933709 4500512640650911244225141)
                ·
                  refine ⟨421923060061022929146107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4500512640650911244225141 421923060061022929146107)
                  ·
                    rfl

theorem cell23_7395230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7395230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395230 prefixEnd_7395230 := by exact prefixLift 7395230
  have htrace : WordTrace (prefixWord ++ tailWord_7395230) baseStart_7395230 baseEnd_7395230 := by
    simpa [prefixWord, tailWord_7395230, baseEnd_7395230] using wordTrace_append hprefix tailTrace_7395230
  have hstable : (prefixWord ++ tailWord_7395230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395230).length < 2 ^ (prefixWord ++ tailWord_7395230).sum := by decide
  have hdescent : baseEnd_7395230 < baseStart_7395230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395232 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_7395232 : Nat := 118140960795 + 7395232 * 2 ^ 59
def prefixEnd_7395232 : Nat := 4983230072969 + 3 ^ 40 * 7395232 * 2
def baseEnd_7395232 : Nat := 3797308567510515354489953

theorem tailTrace_7395232 : CollatzResearch.WordTrace tailWord_7395232 prefixEnd_7395232 3797308567510515354489953 := by
  unfold tailWord_7395232
  simp only [CollatzResearch.WordTrace]
  refine ⟨134863134972172471958869975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179817513296229962611826633 134863134972172471958869975)
  ·
    refine ⟨202294702458258707938304963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134863134972172471958869975 202294702458258707938304963)
    ·
      refine ⟨303442053687388061907457445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202294702458258707938304963 303442053687388061907457445)
      ·
        refine ⟨56895385066385261607648271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303442053687388061907457445 56895385066385261607648271)
        ·
          refine ⟨85343077599577892411472407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56895385066385261607648271 85343077599577892411472407)
          ·
            refine ⟨128014616399366838617208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85343077599577892411472407 128014616399366838617208611)
            ·
              refine ⟨192021924599050257925812917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128014616399366838617208611 192021924599050257925812917)
              ·
                refine ⟨18002055431160961680544961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192021924599050257925812917 18002055431160961680544961)
                ·
                  refine ⟨13501541573370721260408721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002055431160961680544961 13501541573370721260408721)
                  ·
                    refine ⟨10126156180028040945306541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501541573370721260408721 10126156180028040945306541)
                    ·
                      refine ⟨3797308567510515354489953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126156180028040945306541 3797308567510515354489953)
                      ·
                        rfl

theorem cell23_7395232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_7395232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395232 prefixEnd_7395232 := by exact prefixLift 7395232
  have htrace : WordTrace (prefixWord ++ tailWord_7395232) baseStart_7395232 baseEnd_7395232 := by
    simpa [prefixWord, tailWord_7395232, baseEnd_7395232] using wordTrace_append hprefix tailTrace_7395232
  have hstable : (prefixWord ++ tailWord_7395232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395232).length < 2 ^ (prefixWord ++ tailWord_7395232).sum := by decide
  have hdescent : baseEnd_7395232 < baseStart_7395232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395249 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7395249 : Nat := 118140960795 + 7395249 * 2 ^ 59
def prefixEnd_7395249 : Nat := 4983230072969 + 3 ^ 40 * 7395249 * 2
def baseEnd_7395249 : Nat := 3797317296681641787977375

theorem tailTrace_7395249 : CollatzResearch.WordTrace tailWord_7395249 prefixEnd_7395249 3797317296681641787977375 := by
  unfold tailWord_7395249
  simp only [CollatzResearch.WordTrace]
  refine ⟨269726889985283355821108801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179817926656855570547405867 269726889985283355821108801)
  ·
    refine ⟨202295167488962516865831601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269726889985283355821108801 202295167488962516865831601)
    ·
      refine ⟨151721375616721887649373701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202295167488962516865831601 151721375616721887649373701)
      ·
        refine ⟨28447757928135353934257569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151721375616721887649373701 28447757928135353934257569)
        ·
          refine ⟨21335818446101515450693177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28447757928135353934257569 21335818446101515450693177)
          ·
            refine ⟨16001863834576136588019883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21335818446101515450693177 16001863834576136588019883)
            ·
              refine ⟨24002795751864204882029825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16001863834576136588019883 24002795751864204882029825)
              ·
                refine ⟨18002096813898153661522369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24002795751864204882029825 18002096813898153661522369)
                ·
                  refine ⟨13501572610423615246141777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002096813898153661522369 13501572610423615246141777)
                  ·
                    refine ⟨10126179457817711434606333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501572610423615246141777 10126179457817711434606333)
                    ·
                      refine ⟨3797317296681641787977375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126179457817711434606333 3797317296681641787977375)
                      ·
                        rfl

theorem cell23_7395249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7395249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395249 prefixEnd_7395249 := by exact prefixLift 7395249
  have htrace : WordTrace (prefixWord ++ tailWord_7395249) baseStart_7395249 baseEnd_7395249 := by
    simpa [prefixWord, tailWord_7395249, baseEnd_7395249] using wordTrace_append hprefix tailTrace_7395249
  have hstable : (prefixWord ++ tailWord_7395249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395249).length < 2 ^ (prefixWord ++ tailWord_7395249).sum := by decide
  have hdescent : baseEnd_7395249 < baseStart_7395249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395256 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 1, 4]
def baseStart_7395256 : Nat := 118140960795 + 7395256 * 2 ^ 59
def prefixEnd_7395256 : Nat := 4983230072969 + 3 ^ 40 * 7395256 * 2
def baseEnd_7395256 : Nat := 1265773630348741086863281

theorem tailTrace_7395256 : CollatzResearch.WordTrace tailWord_7395256 prefixEnd_7395256 1265773630348741086863281 := by
  unfold tailWord_7395256
  simp only [CollatzResearch.WordTrace]
  refine ⟨134863572648128998008306811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179818096864171997344409081 134863572648128998008306811)
  ·
    refine ⟨202295358972193497012460217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134863572648128998008306811 202295358972193497012460217)
    ·
      refine ⟨151721519229145122759345163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202295358972193497012460217 151721519229145122759345163)
      ·
        refine ⟨227582278843717684139017745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151721519229145122759345163 227582278843717684139017745)
        ·
          refine ⟨170686709132788263104263309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227582278843717684139017745 170686709132788263104263309)
          ·
            refine ⟨64007515924795598664098741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170686709132788263104263309 64007515924795598664098741)
            ·
              refine ⟨6000704617949587374759257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64007515924795598664098741 6000704617949587374759257)
              ·
                refine ⟨4500528463462190531069443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6000704617949587374759257 4500528463462190531069443)
                ·
                  refine ⟨6750792695193285796604165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500528463462190531069443 6750792695193285796604165)
                  ·
                    refine ⟨1265773630348741086863281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750792695193285796604165 1265773630348741086863281)
                    ·
                      rfl

theorem cell23_7395256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_7395256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395256 prefixEnd_7395256 := by exact prefixLift 7395256
  have htrace : WordTrace (prefixWord ++ tailWord_7395256) baseStart_7395256 baseEnd_7395256 := by
    simpa [prefixWord, tailWord_7395256, baseEnd_7395256] using wordTrace_append hprefix tailTrace_7395256
  have hstable : (prefixWord ++ tailWord_7395256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395256).length < 2 ^ (prefixWord ++ tailWord_7395256).sum := by decide
  have hdescent : baseEnd_7395256 < baseStart_7395256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395312 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_7395312 : Nat := 118140960795 + 7395312 * 2 ^ 59
def prefixEnd_7395312 : Nat := 4983230072969 + 3 ^ 40 * 7395312 * 2
def baseEnd_7395312 : Nat := 1265783215320958347163195

theorem tailTrace_7395312 : CollatzResearch.WordTrace tailWord_7395312 prefixEnd_7395312 1265783215320958347163195 := by
  unfold tailWord_7395312
  simp only [CollatzResearch.WordTrace]
  refine ⟨134864593892027558790326095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179819458522703411720434793 134864593892027558790326095)
  ·
    refine ⟨202296890838041338185489143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134864593892027558790326095 202296890838041338185489143)
    ·
      refine ⟨303445336257062007278233715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202296890838041338185489143 303445336257062007278233715)
      ·
        refine ⟨455168004385593010917350573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303445336257062007278233715 455168004385593010917350573)
        ·
          refine ⟨170688001644597379094006465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455168004385593010917350573 170688001644597379094006465)
          ·
            refine ⟨128016001233448034320504849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170688001644597379094006465 128016001233448034320504849)
            ·
              refine ⟨96012000925086025740378637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128016001233448034320504849 96012000925086025740378637)
              ·
                refine ⟨36004500346907259652641989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96012000925086025740378637 36004500346907259652641989)
                ·
                  refine ⟨6750843815045111184870373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36004500346907259652641989 6750843815045111184870373)
                  ·
                    refine ⟨1265783215320958347163195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750843815045111184870373 1265783215320958347163195)
                    ·
                      rfl

theorem cell23_7395312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_7395312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395312 prefixEnd_7395312 := by exact prefixLift 7395312
  have htrace : WordTrace (prefixWord ++ tailWord_7395312) baseStart_7395312 baseEnd_7395312 := by
    simpa [prefixWord, tailWord_7395312, baseEnd_7395312] using wordTrace_append hprefix tailTrace_7395312
  have hstable : (prefixWord ++ tailWord_7395312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395312).length < 2 ^ (prefixWord ++ tailWord_7395312).sum := by decide
  have hdescent : baseEnd_7395312 < baseStart_7395312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395313 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_7395313 : Nat := 118140960795 + 7395313 * 2 ^ 59
def prefixEnd_7395313 : Nat := 4983230072969 + 3 ^ 40 * 7395313 * 2
def baseEnd_7395313 : Nat := 3797350159443529537577081

theorem tailTrace_7395313 : CollatzResearch.WordTrace tailWord_7395313 prefixEnd_7395313 3797350159443529537577081 := by
  unfold tailWord_7395313
  simp only [CollatzResearch.WordTrace]
  refine ⟨269729224257051494751438593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179819482838034329834292395 269729224257051494751438593)
  ·
    refine ⟨202296918192788621063578945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269729224257051494751438593 202296918192788621063578945)
    ·
      refine ⟨151722688644591465797684209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202296918192788621063578945 151722688644591465797684209)
      ·
        refine ⟨113792016483443599348263157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151722688644591465797684209 113792016483443599348263157)
        ·
          refine ⟨10668001545322837438899671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113792016483443599348263157 10668001545322837438899671)
          ·
            refine ⟨16002002317984256158349507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668001545322837438899671 16002002317984256158349507)
            ·
              refine ⟨24003003476976384237524261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16002002317984256158349507 24003003476976384237524261)
              ·
                refine ⟨4500563151933072044535799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24003003476976384237524261 4500563151933072044535799)
                ·
                  refine ⟨6750844727899608066803699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500563151933072044535799 6750844727899608066803699)
                  ·
                    refine ⟨10126267091849412100205549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750844727899608066803699 10126267091849412100205549)
                    ·
                      refine ⟨3797350159443529537577081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126267091849412100205549 3797350159443529537577081)
                      ·
                        rfl

theorem cell23_7395313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_7395313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395313 prefixEnd_7395313 := by exact prefixLift 7395313
  have htrace : WordTrace (prefixWord ++ tailWord_7395313) baseStart_7395313 baseEnd_7395313 := by
    simpa [prefixWord, tailWord_7395313, baseEnd_7395313] using wordTrace_append hprefix tailTrace_7395313
  have hstable : (prefixWord ++ tailWord_7395313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395313).length < 2 ^ (prefixWord ++ tailWord_7395313).sum := by decide
  have hdescent : baseEnd_7395313 < baseStart_7395313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395315 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_7395315 : Nat := 118140960795 + 7395315 * 2 ^ 59
def prefixEnd_7395315 : Nat := 4983230072969 + 3 ^ 40 * 7395315 * 2
def baseEnd_7395315 : Nat := 3797351186404838529752071

theorem tailTrace_7395315 : CollatzResearch.WordTrace tailWord_7395315 prefixEnd_7395315 3797351186404838529752071 := by
  unfold tailWord_7395315
  simp only [CollatzResearch.WordTrace]
  refine ⟨269729297203044249093011399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179819531468696166062007599 269729297203044249093011399)
  ·
    refine ⟨404593945804566373639517099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269729297203044249093011399 404593945804566373639517099)
    ·
      refine ⟨606890918706849560459275649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404593945804566373639517099 606890918706849560459275649)
      ·
        refine ⟨455168189030137170344456737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606890918706849560459275649 455168189030137170344456737)
        ·
          refine ⟨341376141772602877758342553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455168189030137170344456737 341376141772602877758342553)
          ·
            refine ⟨256032106329452158318756915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341376141772602877758342553 256032106329452158318756915)
            ·
              refine ⟨384048159494178237478135373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256032106329452158318756915 384048159494178237478135373)
              ·
                refine ⟨144018059810316839054300765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384048159494178237478135373 144018059810316839054300765)
                ·
                  refine ⟨54006772428868814645362787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144018059810316839054300765 54006772428868814645362787)
                  ·
                    refine ⟨81010158643303221968044181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54006772428868814645362787 81010158643303221968044181)
                    ·
                      refine ⟨3797351186404838529752071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81010158643303221968044181 3797351186404838529752071)
                      ·
                        rfl

theorem cell23_7395315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_7395315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395315 prefixEnd_7395315 := by exact prefixLift 7395315
  have htrace : WordTrace (prefixWord ++ tailWord_7395315) baseStart_7395315 baseEnd_7395315 := by
    simpa [prefixWord, tailWord_7395315, baseEnd_7395315] using wordTrace_append hprefix tailTrace_7395315
  have hstable : (prefixWord ++ tailWord_7395315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395315).length < 2 ^ (prefixWord ++ tailWord_7395315).sum := by decide
  have hdescent : baseEnd_7395315 < baseStart_7395315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395319 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_7395319 : Nat := 118140960795 + 7395319 * 2 ^ 59
def prefixEnd_7395319 : Nat := 4983230072969 + 3 ^ 40 * 7395319 * 2
def baseEnd_7395319 : Nat := 3797353240327456514102053

theorem tailTrace_7395319 : CollatzResearch.WordTrace tailWord_7395319 prefixEnd_7395319 3797353240327456514102053 := by
  unfold tailWord_7395319
  simp only [CollatzResearch.WordTrace]
  refine ⟨269729443095029757776157011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179819628730019838517438007 269729443095029757776157011)
  ·
    refine ⟨404594164642544636664235517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269729443095029757776157011 404594164642544636664235517)
    ·
      refine ⟨151722811740954238749088319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404594164642544636664235517 151722811740954238749088319)
      ·
        refine ⟨227584217611431358123632479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151722811740954238749088319 227584217611431358123632479)
        ·
          refine ⟨341376326417147037185448719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227584217611431358123632479 341376326417147037185448719)
          ·
            refine ⟨512064489625720555778173079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341376326417147037185448719 512064489625720555778173079)
            ·
              refine ⟨768096734438580833667259619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512064489625720555778173079 768096734438580833667259619)
              ·
                refine ⟨1152145101657871250500889429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768096734438580833667259619 1152145101657871250500889429)
                ·
                  refine ⟨6750850205026589358403649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1152145101657871250500889429 6750850205026589358403649)
                  ·
                    refine ⟨5063137653769942018802737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750850205026589358403649 5063137653769942018802737)
                    ·
                      refine ⟨3797353240327456514102053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063137653769942018802737 3797353240327456514102053)
                      ·
                        rfl

theorem cell23_7395319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_7395319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395319 prefixEnd_7395319 := by exact prefixLift 7395319
  have htrace : WordTrace (prefixWord ++ tailWord_7395319) baseStart_7395319 baseEnd_7395319 := by
    simpa [prefixWord, tailWord_7395319, baseEnd_7395319] using wordTrace_append hprefix tailTrace_7395319
  have hstable : (prefixWord ++ tailWord_7395319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395319).length < 2 ^ (prefixWord ++ tailWord_7395319).sum := by decide
  have hdescent : baseEnd_7395319 < baseStart_7395319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395329 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7395329 : Nat := 118140960795 + 7395329 * 2 ^ 59
def prefixEnd_7395329 : Nat := 4983230072969 + 3 ^ 40 * 7395329 * 2
def baseEnd_7395329 : Nat := 1265786125044667158325669

theorem tailTrace_7395329 : CollatzResearch.WordTrace tailWord_7395329 prefixEnd_7395329 1265786125044667158325669 := by
  unfold tailWord_7395329
  simp only [CollatzResearch.WordTrace]
  refine ⟨269729807824993529484021041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179819871883329019656014027 269729807824993529484021041)
  ·
    refine ⟨202297355868745147113015781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269729807824993529484021041 202297355868745147113015781)
    ·
      refine ⟨37930754225389715083690459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202297355868745147113015781 37930754225389715083690459)
      ·
        refine ⟨56896131338084572625535689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37930754225389715083690459 56896131338084572625535689)
        ·
          refine ⟨42672098503563429469151767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56896131338084572625535689 42672098503563429469151767)
          ·
            refine ⟨64008147755345144203727651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42672098503563429469151767 64008147755345144203727651)
            ·
              refine ⟨96012221633017716305591477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64008147755345144203727651 96012221633017716305591477)
              ·
                refine ⟨9001145778095410903649201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96012221633017716305591477 9001145778095410903649201)
                ·
                  refine ⟨6750859333571558177736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9001145778095410903649201 6750859333571558177736901)
                  ·
                    refine ⟨1265786125044667158325669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750859333571558177736901 1265786125044667158325669)
                    ·
                      rfl

theorem cell23_7395329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7395329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395329 prefixEnd_7395329 := by exact prefixLift 7395329
  have htrace : WordTrace (prefixWord ++ tailWord_7395329) baseStart_7395329 baseEnd_7395329 := by
    simpa [prefixWord, tailWord_7395329, baseEnd_7395329] using wordTrace_append hprefix tailTrace_7395329
  have hstable : (prefixWord ++ tailWord_7395329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395329).length < 2 ^ (prefixWord ++ tailWord_7395329).sum := by decide
  have hdescent : baseEnd_7395329 < baseStart_7395329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395334 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7395334 : Nat := 118140960795 + 7395334 * 2 ^ 59
def prefixEnd_7395334 : Nat := 4983230072969 + 3 ^ 40 * 7395334 * 2
def baseEnd_7395334 : Nat := 3797360942537273955414485

theorem tailTrace_7395334 : CollatzResearch.WordTrace tailWord_7395334 prefixEnd_7395334 3797360942537273955414485 := by
  unfold tailWord_7395334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429062193436731729311033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179819993459983610225302037 8429062193436731729311033)
  ·
    refine ⟨6321796645077548796983275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8429062193436731729311033 6321796645077548796983275)
    ·
      refine ⟨9482694967616323195474913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321796645077548796983275 9482694967616323195474913)
      ·
        refine ⟨7112021225712242396606185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9482694967616323195474913 7112021225712242396606185)
        ·
          refine ⟨5334015919284181797454639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112021225712242396606185 5334015919284181797454639)
          ·
            refine ⟨8001023878926272696181959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334015919284181797454639 8001023878926272696181959)
            ·
              refine ⟨12001535818389409044272939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001023878926272696181959 12001535818389409044272939)
              ·
                refine ⟨18002303727584113566409409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001535818389409044272939 18002303727584113566409409)
                ·
                  refine ⟨13501727795688085174807057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002303727584113566409409 13501727795688085174807057)
                  ·
                    refine ⟨10126295846766063881105293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501727795688085174807057 10126295846766063881105293)
                    ·
                      refine ⟨3797360942537273955414485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126295846766063881105293 3797360942537273955414485)
                      ·
                        rfl

theorem cell23_7395334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7395334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395334 prefixEnd_7395334 := by exact prefixLift 7395334
  have htrace : WordTrace (prefixWord ++ tailWord_7395334) baseStart_7395334 baseEnd_7395334 := by
    simpa [prefixWord, tailWord_7395334, baseEnd_7395334] using wordTrace_append hprefix tailTrace_7395334
  have hstable : (prefixWord ++ tailWord_7395334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395334).length < 2 ^ (prefixWord ++ tailWord_7395334).sum := by decide
  have hdescent : baseEnd_7395334 < baseStart_7395334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395336 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_7395336 : Nat := 118140960795 + 7395336 * 2 ^ 59
def prefixEnd_7395336 : Nat := 4983230072969 + 3 ^ 40 * 7395336 * 2
def baseEnd_7395336 : Nat := 3797361969498582947589475

theorem tailTrace_7395336 : CollatzResearch.WordTrace tailWord_7395336 prefixEnd_7395336 3797361969498582947589475 := by
  unfold tailWord_7395336
  simp only [CollatzResearch.WordTrace]
  refine ⟨134865031567984084839762931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179820042090645446453017241 134865031567984084839762931)
  ·
    refine ⟨202297547351976127259644397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134865031567984084839762931 202297547351976127259644397)
    ·
      refine ⟨75861580256991047722366649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202297547351976127259644397 75861580256991047722366649)
      ·
        refine ⟨56896185192743285791774987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75861580256991047722366649 56896185192743285791774987)
        ·
          refine ⟨85344277789114928687662481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56896185192743285791774987 85344277789114928687662481)
          ·
            refine ⟨64008208341836196515746861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85344277789114928687662481 64008208341836196515746861)
            ·
              refine ⟨24003078128188573693405073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64008208341836196515746861 24003078128188573693405073)
              ·
                refine ⟨18002308596141430270053805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24003078128188573693405073 18002308596141430270053805)
                ·
                  refine ⟨6750865723553036351270177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18002308596141430270053805 6750865723553036351270177)
                  ·
                    refine ⟨5063149292664777263452633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750865723553036351270177 5063149292664777263452633)
                    ·
                      refine ⟨3797361969498582947589475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063149292664777263452633 3797361969498582947589475)
                      ·
                        rfl

theorem cell23_7395336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_7395336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395336 prefixEnd_7395336 := by exact prefixLift 7395336
  have htrace : WordTrace (prefixWord ++ tailWord_7395336) baseStart_7395336 baseEnd_7395336 := by
    simpa [prefixWord, tailWord_7395336, baseEnd_7395336] using wordTrace_append hprefix tailTrace_7395336
  have hstable : (prefixWord ++ tailWord_7395336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395336).length < 2 ^ (prefixWord ++ tailWord_7395336).sum := by decide
  have hdescent : baseEnd_7395336 < baseStart_7395336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395339 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 3]
def baseStart_7395339 : Nat := 118140960795 + 7395339 * 2 ^ 59
def prefixEnd_7395339 : Nat := 4983230072969 + 3 ^ 40 * 7395339 * 2
def baseEnd_7395339 : Nat := 3797363509940546435851961

theorem tailTrace_7395339 : CollatzResearch.WordTrace tailWord_7395339 prefixEnd_7395339 3797363509940546435851961 := by
  unfold tailWord_7395339
  simp only [CollatzResearch.WordTrace]
  refine ⟨269730172554957301191885071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179820115036638200794590047 269730172554957301191885071)
  ·
    refine ⟨404595258832435951787827607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269730172554957301191885071 404595258832435951787827607)
    ·
      refine ⟨606892888248653927681741411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404595258832435951787827607 606892888248653927681741411)
      ·
        refine ⟨910339332372980891522612117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606892888248653927681741411 910339332372980891522612117)
        ·
          refine ⟨42672156204983479290122443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 910339332372980891522612117 42672156204983479290122443)
          ·
            refine ⟨64008234307475218935183665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42672156204983479290122443 64008234307475218935183665)
            ·
              refine ⟨48006175730606414201387749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64008234307475218935183665 48006175730606414201387749)
              ·
                refine ⟨9001157949488702662760203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48006175730606414201387749 9001157949488702662760203)
                ·
                  refine ⟨13501736924233053994140305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9001157949488702662760203 13501736924233053994140305)
                  ·
                    refine ⟨10126302693174790495605229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501736924233053994140305 10126302693174790495605229)
                    ·
                      refine ⟨3797363509940546435851961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126302693174790495605229 3797363509940546435851961)
                      ·
                        rfl

theorem cell23_7395339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 3].length) (baseStart_7395339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395339 prefixEnd_7395339 := by exact prefixLift 7395339
  have htrace : WordTrace (prefixWord ++ tailWord_7395339) baseStart_7395339 baseEnd_7395339 := by
    simpa [prefixWord, tailWord_7395339, baseEnd_7395339] using wordTrace_append hprefix tailTrace_7395339
  have hstable : (prefixWord ++ tailWord_7395339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395339).length < 2 ^ (prefixWord ++ tailWord_7395339).sum := by decide
  have hdescent : baseEnd_7395339 < baseStart_7395339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395355 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 9]
def baseStart_7395355 : Nat := 118140960795 + 7395355 * 2 ^ 59
def prefixEnd_7395355 : Nat := 4983230072969 + 3 ^ 40 * 7395355 * 2
def baseEnd_7395355 : Nat := 1265790575210339457750629

theorem tailTrace_7395355 : CollatzResearch.WordTrace tailWord_7395355 prefixEnd_7395355 1265790575210339457750629 := by
  unfold tailWord_7395355
  simp only [CollatzResearch.WordTrace]
  refine ⟨269730756122899335924467519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179820504081932890616311679 269730756122899335924467519)
  ·
    refine ⟨404596134184349003886701279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269730756122899335924467519 404596134184349003886701279)
    ·
      refine ⟨606894201276523505830051919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404596134184349003886701279 606894201276523505830051919)
      ·
        refine ⟨910341301914785258745077879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606894201276523505830051919 910341301914785258745077879)
        ·
          refine ⟨1365511952872177888117616819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910341301914785258745077879 1365511952872177888117616819)
          ·
            refine ⟨2048267929308266832176425229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365511952872177888117616819 2048267929308266832176425229)
            ·
              refine ⟨768100473490600062066159461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2048267929308266832176425229 768100473490600062066159461)
              ·
                refine ⟨144018838779487511637404899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768100473490600062066159461 144018838779487511637404899)
                ·
                  refine ⟨216028258169231267456107349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144018838779487511637404899 216028258169231267456107349)
                  ·
                    refine ⟨1265790575210339457750629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216028258169231267456107349 1265790575210339457750629)
                    ·
                      rfl

theorem cell23_7395355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_7395355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395355 prefixEnd_7395355 := by exact prefixLift 7395355
  have htrace : WordTrace (prefixWord ++ tailWord_7395355) baseStart_7395355 baseEnd_7395355 := by
    simpa [prefixWord, tailWord_7395355, baseEnd_7395355] using wordTrace_append hprefix tailTrace_7395355
  have hstable : (prefixWord ++ tailWord_7395355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395355).length < 2 ^ (prefixWord ++ tailWord_7395355).sum := by decide
  have hdescent : baseEnd_7395355 < baseStart_7395355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395356 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7395356 : Nat := 118140960795 + 7395356 * 2 ^ 59
def prefixEnd_7395356 : Nat := 4983230072969 + 3 ^ 40 * 7395356 * 2
def baseEnd_7395356 : Nat := 3797372239111672869339383

theorem tailTrace_7395356 : CollatzResearch.WordTrace tailWord_7395356 prefixEnd_7395356 3797372239111672869339383 := by
  unfold tailWord_7395356
  simp only [CollatzResearch.WordTrace]
  refine ⟨134865396297947856547626961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179820528397263808730169281 134865396297947856547626961)
  ·
    refine ⟨101149047223460892410720221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134865396297947856547626961 101149047223460892410720221)
    ·
      refine ⟨37930892708797834654020083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101149047223460892410720221 37930892708797834654020083)
      ·
        refine ⟨56896339063196751981030125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37930892708797834654020083 56896339063196751981030125)
        ·
          refine ⟨21336127148698781992886297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56896339063196751981030125 21336127148698781992886297)
          ·
            refine ⟨16002095361524086494664723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21336127148698781992886297 16002095361524086494664723)
            ·
              refine ⟨24003143042286129741997085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16002095361524086494664723 24003143042286129741997085)
              ·
                refine ⟨9001178640857298653248907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24003143042286129741997085 9001178640857298653248907)
                ·
                  refine ⟨13501767961285947979873361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9001178640857298653248907 13501767961285947979873361)
                  ·
                    refine ⟨10126325970964460984905021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13501767961285947979873361 10126325970964460984905021)
                    ·
                      refine ⟨3797372239111672869339383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10126325970964460984905021 3797372239111672869339383)
                      ·
                        rfl

theorem cell23_7395356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7395356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395356 prefixEnd_7395356 := by exact prefixLift 7395356
  have htrace : WordTrace (prefixWord ++ tailWord_7395356) baseStart_7395356 baseEnd_7395356 := by
    simpa [prefixWord, tailWord_7395356, baseEnd_7395356] using wordTrace_append hprefix tailTrace_7395356
  have hstable : (prefixWord ++ tailWord_7395356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395356).length < 2 ^ (prefixWord ++ tailWord_7395356).sum := by decide
  have hdescent : baseEnd_7395356 < baseStart_7395356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395370 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7395370 : Nat := 118140960795 + 7395370 * 2 ^ 59
def prefixEnd_7395370 : Nat := 4983230072969 + 3 ^ 40 * 7395370 * 2
def baseEnd_7395370 : Nat := 3797379427840835814564319

theorem tailTrace_7395370 : CollatzResearch.WordTrace tailWord_7395370 prefixEnd_7395370 3797379427840835814564319 := by
  unfold tailWord_7395370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67432825804461248371565891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179820868811896662324175709 67432825804461248371565891)
  ·
    refine ⟨101149238706691872557348837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67432825804461248371565891 101149238706691872557348837)
    ·
      refine ⟨18965482257504726104502907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101149238706691872557348837 18965482257504726104502907)
      ·
        refine ⟨28448223386257089156754361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18965482257504726104502907 28448223386257089156754361)
        ·
          refine ⟨21336167539692816867565771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28448223386257089156754361 21336167539692816867565771)
          ·
            refine ⟨32004251309539225301348657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21336167539692816867565771 32004251309539225301348657)
            ·
              refine ⟨24003188482154418976011493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32004251309539225301348657 24003188482154418976011493)
              ·
                refine ⟨4500597840403953558002155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24003188482154418976011493 4500597840403953558002155)
                ·
                  refine ⟨6750896760605930337003233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500597840403953558002155 6750896760605930337003233)
                  ·
                    refine ⟨5063172570454447752752425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750896760605930337003233 5063172570454447752752425)
                    ·
                      refine ⟨3797379427840835814564319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063172570454447752752425 3797379427840835814564319)
                      ·
                        rfl

theorem cell23_7395370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7395370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395370 prefixEnd_7395370 := by exact prefixLift 7395370
  have htrace : WordTrace (prefixWord ++ tailWord_7395370) baseStart_7395370 baseEnd_7395370 := by
    simpa [prefixWord, tailWord_7395370, baseEnd_7395370] using wordTrace_append hprefix tailTrace_7395370
  have hstable : (prefixWord ++ tailWord_7395370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395370).length < 2 ^ (prefixWord ++ tailWord_7395370).sum := by decide
  have hdescent : baseEnd_7395370 < baseStart_7395370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395379 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 5, 3, 2]
def baseStart_7395379 : Nat := 118140960795 + 7395379 * 2 ^ 59
def prefixEnd_7395379 : Nat := 4983230072969 + 3 ^ 40 * 7395379 * 2
def baseEnd_7395379 : Nat := 3797384049166726279351777

theorem tailTrace_7395379 : CollatzResearch.WordTrace tailWord_7395379 prefixEnd_7395379 3797384049166726279351777 := by
  unfold tailWord_7395379
  simp only [CollatzResearch.WordTrace]
  refine ⟨269731631474812388023341191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179821087649874925348894127 269731631474812388023341191)
  ·
    refine ⟨404597447212218582035011787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269731631474812388023341191 404597447212218582035011787)
    ·
      refine ⟨606896170818327873052517681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404597447212218582035011787 606896170818327873052517681)
      ·
        refine ⟨455172128113745904789388261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606896170818327873052517681 455172128113745904789388261)
        ·
          refine ⟨85344774021327357148010299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455172128113745904789388261 85344774021327357148010299)
          ·
            refine ⟨128017161031991035722015449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85344774021327357148010299 128017161031991035722015449)
            ·
              refine ⟨96012870773993276791511587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128017161031991035722015449 96012870773993276791511587)
              ·
                refine ⟨144019306160989915187267381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96012870773993276791511587 144019306160989915187267381)
                ·
                  refine ⟨13501809952592804548806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144019306160989915187267381 13501809952592804548806317)
                  ·
                    refine ⟨5063178732222301705802369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13501809952592804548806317 5063178732222301705802369)
                    ·
                      refine ⟨3797384049166726279351777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063178732222301705802369 3797384049166726279351777)
                      ·
                        rfl

theorem cell23_7395379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3, 2].length) (baseStart_7395379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395379 prefixEnd_7395379 := by exact prefixLift 7395379
  have htrace : WordTrace (prefixWord ++ tailWord_7395379) baseStart_7395379 baseEnd_7395379 := by
    simpa [prefixWord, tailWord_7395379, baseEnd_7395379] using wordTrace_append hprefix tailTrace_7395379
  have hstable : (prefixWord ++ tailWord_7395379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395379).length < 2 ^ (prefixWord ++ tailWord_7395379).sum := by decide
  have hdescent : baseEnd_7395379 < baseStart_7395379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395380 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_7395380 : Nat := 118140960795 + 7395380 * 2 ^ 59
def prefixEnd_7395380 : Nat := 4983230072969 + 3 ^ 40 * 7395380 * 2
def baseEnd_7395380 : Nat := 1265794854215793591813091

theorem tailTrace_7395380 : CollatzResearch.WordTrace tailWord_7395380 prefixEnd_7395380 1265794854215793591813091 := by
  unfold tailWord_7395380
  simp only [CollatzResearch.WordTrace]
  refine ⟨134865833973904382597063797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179821111965205843462751729 134865833973904382597063797)
  ·
    refine ⟨12643671935053535868474731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134865833973904382597063797 12643671935053535868474731)
    ·
      refine ⟨18965507902580303802712097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643671935053535868474731 18965507902580303802712097)
      ·
        refine ⟨14224130926935227852034073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18965507902580303802712097 14224130926935227852034073)
        ·
          refine ⟨10668098195201420889025555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14224130926935227852034073 10668098195201420889025555)
          ·
            refine ⟨16002147292802131333538333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668098195201420889025555 16002147292802131333538333)
            ·
              refine ⟨6000805234800799250076875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16002147292802131333538333 6000805234800799250076875)
              ·
                refine ⟨9001207852201198875115313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000805234800799250076875 9001207852201198875115313)
                ·
                  refine ⟨6750905889150899156336485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9001207852201198875115313 6750905889150899156336485)
                  ·
                    refine ⟨1265794854215793591813091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750905889150899156336485 1265794854215793591813091)
                    ·
                      rfl

theorem cell23_7395380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_7395380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395380 prefixEnd_7395380 := by exact prefixLift 7395380
  have htrace : WordTrace (prefixWord ++ tailWord_7395380) baseStart_7395380 baseEnd_7395380 := by
    simpa [prefixWord, tailWord_7395380, baseEnd_7395380] using wordTrace_append hprefix tailTrace_7395380
  have hstable : (prefixWord ++ tailWord_7395380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395380).length < 2 ^ (prefixWord ++ tailWord_7395380).sum := by decide
  have hdescent : baseEnd_7395380 < baseStart_7395380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395409 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_7395409 : Nat := 118140960795 + 7395409 * 2 ^ 59
def prefixEnd_7395409 : Nat := 4983230072969 + 3 ^ 40 * 7395409 * 2
def baseEnd_7395409 : Nat := 3797399453586361161976639

theorem tailTrace_7395409 : CollatzResearch.WordTrace tailWord_7395409 prefixEnd_7395409 3797399453586361161976639 := by
  unfold tailWord_7395409
  simp only [CollatzResearch.WordTrace]
  refine ⟨269732725664703703146933281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179821817109802468764622187 269732725664703703146933281)
  ·
    refine ⟨202299544248527777360199961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269732725664703703146933281 202299544248527777360199961)
    ·
      refine ⟨151724658186395833020149971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202299544248527777360199961 151724658186395833020149971)
      ·
        refine ⟨227586987279593749530224957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151724658186395833020149971 227586987279593749530224957)
        ·
          refine ⟨85345120229847656073834359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227586987279593749530224957 85345120229847656073834359)
          ·
            refine ⟨128017680344771484110751539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85345120229847656073834359 128017680344771484110751539)
            ·
              refine ⟨192026520517157226166127309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128017680344771484110751539 192026520517157226166127309)
              ·
                refine ⟨72009945193933959812297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192026520517157226166127309 72009945193933959812297741)
                ·
                  refine ⟨27003729447725234929611653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72009945193933959812297741 27003729447725234929611653)
                  ·
                    refine ⟨5063199271448481549302185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27003729447725234929611653 5063199271448481549302185)
                    ·
                      refine ⟨3797399453586361161976639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063199271448481549302185 3797399453586361161976639)
                      ·
                        rfl

theorem cell23_7395409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_7395409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395409 prefixEnd_7395409 := by exact prefixLift 7395409
  have htrace : WordTrace (prefixWord ++ tailWord_7395409) baseStart_7395409 baseEnd_7395409 := by
    simpa [prefixWord, tailWord_7395409, baseEnd_7395409] using wordTrace_append hprefix tailTrace_7395409
  have hstable : (prefixWord ++ tailWord_7395409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395409).length < 2 ^ (prefixWord ++ tailWord_7395409).sum := by decide
  have hdescent : baseEnd_7395409 < baseStart_7395409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395472 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_7395472 : Nat := 118140960795 + 7395472 * 2 ^ 59
def prefixEnd_7395472 : Nat := 4983230072969 + 3 ^ 40 * 7395472 * 2
def baseEnd_7395472 : Nat := 3797431802867594415488849

theorem tailTrace_7395472 : CollatzResearch.WordTrace tailWord_7395472 prefixEnd_7395472 3797431802867594415488849 := by
  unfold tailWord_7395472
  simp only [CollatzResearch.WordTrace]
  refine ⟨134867511731737732453238335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179823348975650309937651113 134867511731737732453238335)
  ·
    refine ⟨202301267597606598679857503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134867511731737732453238335 202301267597606598679857503)
    ·
      refine ⟨303451901396409898019786255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202301267597606598679857503 303451901396409898019786255)
      ·
        refine ⟨455177852094614847029679383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303451901396409898019786255 455177852094614847029679383)
        ·
          refine ⟨682766778141922270544519075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455177852094614847029679383 682766778141922270544519075)
          ·
            refine ⟨1024150167212883405816778613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682766778141922270544519075 1024150167212883405816778613)
            ·
              refine ⟨96014078176207819295322995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1024150167212883405816778613 96014078176207819295322995)
              ·
                refine ⟨144021117264311728942984493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96014078176207819295322995 144021117264311728942984493)
                ·
                  refine ⟨54007918974116898353619185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144021117264311728942984493 54007918974116898353619185)
                  ·
                    refine ⟨40505939230587673765214389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54007918974116898353619185 40505939230587673765214389)
                    ·
                      refine ⟨3797431802867594415488849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40505939230587673765214389 3797431802867594415488849)
                      ·
                        rfl

theorem cell23_7395472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_7395472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395472 prefixEnd_7395472 := by exact prefixLift 7395472
  have htrace : WordTrace (prefixWord ++ tailWord_7395472) baseStart_7395472 baseEnd_7395472 := by
    simpa [prefixWord, tailWord_7395472, baseEnd_7395472] using wordTrace_append hprefix tailTrace_7395472
  have hstable : (prefixWord ++ tailWord_7395472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395472).length < 2 ^ (prefixWord ++ tailWord_7395472).sum := by decide
  have hdescent : baseEnd_7395472 < baseStart_7395472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395489 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7395489 : Nat := 118140960795 + 7395489 * 2 ^ 59
def prefixEnd_7395489 : Nat := 4983230072969 + 3 ^ 40 * 7395489 * 2
def baseEnd_7395489 : Nat := 3797440532038720848976271

theorem tailTrace_7395489 : CollatzResearch.WordTrace tailWord_7395489 prefixEnd_7395489 3797440532038720848976271 := by
  unfold tailWord_7395489
  simp only [CollatzResearch.WordTrace]
  refine ⟨269735643504413876809845521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179823762336275917873230347 269735643504413876809845521)
  ·
    refine ⟨202301732628310407607384141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269735643504413876809845521 202301732628310407607384141)
    ·
      refine ⟨75863149735616402852769053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202301732628310407607384141 75863149735616402852769053)
      ·
        refine ⟨28448681150856151069788395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75863149735616402852769053 28448681150856151069788395)
        ·
          refine ⟨42673021726284226604682593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28448681150856151069788395 42673021726284226604682593)
          ·
            refine ⟨32004766294713169953511945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42673021726284226604682593 32004766294713169953511945)
            ·
              refine ⟨24003574721034877465133959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32004766294713169953511945 24003574721034877465133959)
              ·
                refine ⟨36005362081552316197700939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24003574721034877465133959 36005362081552316197700939)
                ·
                  refine ⟨54008043122328474296551409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36005362081552316197700939 54008043122328474296551409)
                  ·
                    refine ⟨40506032341746355722413557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54008043122328474296551409 40506032341746355722413557)
                    ·
                      refine ⟨3797440532038720848976271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40506032341746355722413557 3797440532038720848976271)
                      ·
                        rfl

theorem cell23_7395489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7395489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395489 prefixEnd_7395489 := by exact prefixLift 7395489
  have htrace : WordTrace (prefixWord ++ tailWord_7395489) baseStart_7395489 baseEnd_7395489 := by
    simpa [prefixWord, tailWord_7395489, baseEnd_7395489] using wordTrace_append hprefix tailTrace_7395489
  have hstable : (prefixWord ++ tailWord_7395489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395489).length < 2 ^ (prefixWord ++ tailWord_7395489).sum := by decide
  have hdescent : baseEnd_7395489 < baseStart_7395489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395516 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_7395516 : Nat := 118140960795 + 7395516 * 2 ^ 59
def prefixEnd_7395516 : Nat := 4983230072969 + 3 ^ 40 * 7395516 * 2
def baseEnd_7395516 : Nat := 3797454396016392243338647

theorem tailTrace_7395516 : CollatzResearch.WordTrace tailWord_7395516 prefixEnd_7395516 3797454396016392243338647 := by
  unfold tailWord_7395516
  simp only [CollatzResearch.WordTrace]
  refine ⟨134868314137658030210539201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179824418850210706947385601 134868314137658030210539201)
  ·
    refine ⟨101151235603243522657904401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134868314137658030210539201 101151235603243522657904401)
    ·
      refine ⟨75863426702432641993428301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101151235603243522657904401 75863426702432641993428301)
      ·
        refine ⟨28448785013412240747535613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75863426702432641993428301 28448785013412240747535613)
        ·
          refine ⟨10668294380029590280325855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28448785013412240747535613 10668294380029590280325855)
          ·
            refine ⟨16002441570044385420488783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668294380029590280325855 16002441570044385420488783)
            ·
              refine ⟨24003662355066578130733175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16002441570044385420488783 24003662355066578130733175)
              ·
                refine ⟨36005493532599867196099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24003662355066578130733175 36005493532599867196099763)
                ·
                  refine ⟨54008240298899800794149645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36005493532599867196099763 54008240298899800794149645)
                  ·
                    refine ⟨20253090112087425297806117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54008240298899800794149645 20253090112087425297806117)
                    ·
                      refine ⟨3797454396016392243338647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20253090112087425297806117 3797454396016392243338647)
                      ·
                        rfl

theorem cell23_7395516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_7395516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395516 prefixEnd_7395516 := by exact prefixLift 7395516
  have htrace : WordTrace (prefixWord ++ tailWord_7395516) baseStart_7395516 baseEnd_7395516 := by
    simpa [prefixWord, tailWord_7395516, baseEnd_7395516] using wordTrace_append hprefix tailTrace_7395516
  have hstable : (prefixWord ++ tailWord_7395516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395516).length < 2 ^ (prefixWord ++ tailWord_7395516).sum := by decide
  have hdescent : baseEnd_7395516 < baseStart_7395516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395569 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_7395569 : Nat := 118140960795 + 7395569 * 2 ^ 59
def prefixEnd_7395569 : Nat := 4983230072969 + 3 ^ 40 * 7395569 * 2
def baseEnd_7395569 : Nat := 1265827203497026845325301

theorem tailTrace_7395569 : CollatzResearch.WordTrace tailWord_7395569 prefixEnd_7395569 1265827203497026845325301 := by
  unfold tailWord_7395569
  simp only [CollatzResearch.WordTrace]
  refine ⟨269738561344124050472757761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179825707562749366981838507 269738561344124050472757761)
  ·
    refine ⟨202303921008093037854568321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269738561344124050472757761 202303921008093037854568321)
    ·
      refine ⟨151727940756069778390926241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202303921008093037854568321 151727940756069778390926241)
      ·
        refine ⟨113795955567052333793194681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151727940756069778390926241 113795955567052333793194681)
        ·
          refine ⟨85346966675289250344896011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113795955567052333793194681 85346966675289250344896011)
          ·
            refine ⟨128020450012933875517344017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85346966675289250344896011 128020450012933875517344017)
            ·
              refine ⟨96015337509700406638008013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128020450012933875517344017 96015337509700406638008013)
              ·
                refine ⟨36005751566137652489253005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96015337509700406638008013 36005751566137652489253005)
                ·
                  refine ⟨13502156837301619683469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36005751566137652489253005 13502156837301619683469877)
                  ·
                    refine ⟨1265827203497026845325301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13502156837301619683469877 1265827203497026845325301)
                    ·
                      rfl

theorem cell23_7395569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_7395569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395569 prefixEnd_7395569 := by exact prefixLift 7395569
  have htrace : WordTrace (prefixWord ++ tailWord_7395569) baseStart_7395569 baseEnd_7395569 := by
    simpa [prefixWord, tailWord_7395569, baseEnd_7395569] using wordTrace_append hprefix tailTrace_7395569
  have hstable : (prefixWord ++ tailWord_7395569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395569).length < 2 ^ (prefixWord ++ tailWord_7395569).sum := by decide
  have hdescent : baseEnd_7395569 < baseStart_7395569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_7395576 : Nat := 118140960795 + 7395576 * 2 ^ 59
def prefixEnd_7395576 : Nat := 4983230072969 + 3 ^ 40 * 7395576 * 2
def baseEnd_7395576 : Nat := 3797485204855662008588371

theorem tailTrace_7395576 : CollatzResearch.WordTrace tailWord_7395576 prefixEnd_7395576 3797485204855662008588371 := by
  unfold tailWord_7395576
  simp only [CollatzResearch.WordTrace]
  refine ⟨134869408327549345334131291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179825877770065793778841721 134869408327549345334131291)
  ·
    refine ⟨202304112491324018001196937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134869408327549345334131291 202304112491324018001196937)
    ·
      refine ⟨151728084368493013500897703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202304112491324018001196937 151728084368493013500897703)
      ·
        refine ⟨227592126552739520251346555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151728084368493013500897703 227592126552739520251346555)
        ·
          refine ⟨341388189829109280377019833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227592126552739520251346555 341388189829109280377019833)
          ·
            refine ⟨256041142371831960282764875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341388189829109280377019833 256041142371831960282764875)
            ·
              refine ⟨384061713557747940424147313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256041142371831960282764875 384061713557747940424147313)
              ·
                refine ⟨288046285168310955318110485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384061713557747940424147313 288046285168310955318110485)
                ·
                  refine ⟨13502169617264576030536429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288046285168310955318110485 13502169617264576030536429)
                  ·
                    refine ⟨5063313606474216011451161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13502169617264576030536429 5063313606474216011451161)
                    ·
                      refine ⟨3797485204855662008588371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063313606474216011451161 3797485204855662008588371)
                      ·
                        rfl

theorem cell23_7395576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_7395576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395576 prefixEnd_7395576 := by exact prefixLift 7395576
  have htrace : WordTrace (prefixWord ++ tailWord_7395576) baseStart_7395576 baseEnd_7395576 := by
    simpa [prefixWord, tailWord_7395576, baseEnd_7395576] using wordTrace_append hprefix tailTrace_7395576
  have hstable : (prefixWord ++ tailWord_7395576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395576).length < 2 ^ (prefixWord ++ tailWord_7395576).sum := by decide
  have hdescent : baseEnd_7395576 < baseStart_7395576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395593 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 2, 3, 2]
def baseStart_7395593 : Nat := 118140960795 + 7395593 * 2 ^ 59
def prefixEnd_7395593 : Nat := 4983230072969 + 3 ^ 40 * 7395593 * 2
def baseEnd_7395593 : Nat := 3797493934026788442075793

theorem tailTrace_7395593 : CollatzResearch.WordTrace tailWord_7395593 prefixEnd_7395593 3797493934026788442075793 := by
  unfold tailWord_7395593
  simp only [CollatzResearch.WordTrace]
  refine ⟨269739436696037102571631433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179826291130691401714420955 269739436696037102571631433)
  ·
    refine ⟨202304577522027826928723575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269739436696037102571631433 202304577522027826928723575)
    ·
      refine ⟨303456866283041740393085363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202304577522027826928723575 303456866283041740393085363)
      ·
        refine ⟨455185299424562610589628045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303456866283041740393085363 455185299424562610589628045)
        ·
          refine ⟨170694487284210978971110517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455185299424562610589628045 170694487284210978971110517)
          ·
            refine ⟨16002608182894779278541611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170694487284210978971110517 16002608182894779278541611)
            ·
              refine ⟨24003912274342168917812417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16002608182894779278541611 24003912274342168917812417)
              ·
                refine ⟨18002934205756626688359313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24003912274342168917812417 18002934205756626688359313)
                ·
                  refine ⟨13502200654317470016269485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002934205756626688359313 13502200654317470016269485)
                  ·
                    refine ⟨5063325245369051256101057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13502200654317470016269485 5063325245369051256101057)
                    ·
                      refine ⟨3797493934026788442075793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063325245369051256101057 3797493934026788442075793)
                      ·
                        rfl

theorem cell23_7395593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3, 2].length) (baseStart_7395593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395593 prefixEnd_7395593 := by exact prefixLift 7395593
  have htrace : WordTrace (prefixWord ++ tailWord_7395593) baseStart_7395593 baseEnd_7395593 := by
    simpa [prefixWord, tailWord_7395593, baseEnd_7395593] using wordTrace_append hprefix tailTrace_7395593
  have hstable : (prefixWord ++ tailWord_7395593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395593).length < 2 ^ (prefixWord ++ tailWord_7395593).sum := by decide
  have hdescent : baseEnd_7395593 < baseStart_7395593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395619 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_7395619 : Nat := 118140960795 + 7395619 * 2 ^ 59
def prefixEnd_7395619 : Nat := 4983230072969 + 3 ^ 40 * 7395619 * 2
def baseEnd_7395619 : Nat := 3797507284523805340350673

theorem tailTrace_7395619 : CollatzResearch.WordTrace tailWord_7395619 prefixEnd_7395619 3797507284523805340350673 := by
  unfold tailWord_7395619
  simp only [CollatzResearch.WordTrace]
  refine ⟨269740384993942909012077911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179826923329295272674718607 269740384993942909012077911)
  ·
    refine ⟨404610577490914363518116867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269740384993942909012077911 404610577490914363518116867)
    ·
      refine ⟨606915866236371545277175301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404610577490914363518116867 606915866236371545277175301)
      ·
        refine ⟨113796724919319664739470369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 606915866236371545277175301 113796724919319664739470369)
        ·
          refine ⟨85347543689489748554602777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113796724919319664739470369 85347543689489748554602777)
          ·
            refine ⟨64010657767117311415952083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85347543689489748554602777 64010657767117311415952083)
            ·
              refine ⟨96015986650675967123928125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64010657767117311415952083 96015986650675967123928125)
              ·
                refine ⟨36005994994003487671473047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96015986650675967123928125 36005994994003487671473047)
                ·
                  refine ⟨54008992491005231507209571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36005994994003487671473047 54008992491005231507209571)
                  ·
                    refine ⟨81013488736507847260814357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54008992491005231507209571 81013488736507847260814357)
                    ·
                      refine ⟨3797507284523805340350673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81013488736507847260814357 3797507284523805340350673)
                      ·
                        rfl

theorem cell23_7395619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_7395619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395619 prefixEnd_7395619 := by exact prefixLift 7395619
  have htrace : WordTrace (prefixWord ++ tailWord_7395619) baseStart_7395619 baseEnd_7395619 := by
    simpa [prefixWord, tailWord_7395619, baseEnd_7395619] using wordTrace_append hprefix tailTrace_7395619
  have hstable : (prefixWord ++ tailWord_7395619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395619).length < 2 ^ (prefixWord ++ tailWord_7395619).sum := by decide
  have hdescent : baseEnd_7395619 < baseStart_7395619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395678 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7395678 : Nat := 118140960795 + 7395678 * 2 ^ 59
def prefixEnd_7395678 : Nat := 4983230072969 + 3 ^ 40 * 7395678 * 2
def baseEnd_7395678 : Nat := 3797537579882420609512903

theorem tailTrace_7395678 : CollatzResearch.WordTrace tailWord_7395678 prefixEnd_7395678 3797537579882420609512903 := by
  unfold tailWord_7395678
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717817112591145261059461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179828357933819441392317125 33717817112591145261059461)
  ·
    refine ⟨6322090708610839736448649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33717817112591145261059461 6322090708610839736448649)
    ·
      refine ⟨4741568031458129802336487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6322090708610839736448649 4741568031458129802336487)
      ·
        refine ⟨7112352047187194703504731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741568031458129802336487 7112352047187194703504731)
        ·
          refine ⟨10668528070780792055257097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112352047187194703504731 10668528070780792055257097)
          ·
            refine ⟨8001396053085594041442823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10668528070780792055257097 8001396053085594041442823)
            ·
              refine ⟨12002094079628391062164235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001396053085594041442823 12002094079628391062164235)
              ·
                refine ⟨18003141119442586593246353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002094079628391062164235 18003141119442586593246353)
                ·
                  refine ⟨13502355839581939944934765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18003141119442586593246353 13502355839581939944934765)
                  ·
                    refine ⟨5063383439843227479350537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13502355839581939944934765 5063383439843227479350537)
                    ·
                      refine ⟨3797537579882420609512903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063383439843227479350537 3797537579882420609512903)
                      ·
                        rfl

theorem cell23_7395678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7395678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395678 prefixEnd_7395678 := by exact prefixLift 7395678
  have htrace : WordTrace (prefixWord ++ tailWord_7395678) baseStart_7395678 baseEnd_7395678 := by
    simpa [prefixWord, tailWord_7395678, baseEnd_7395678] using wordTrace_append hprefix tailTrace_7395678
  have hstable : (prefixWord ++ tailWord_7395678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395678).length < 2 ^ (prefixWord ++ tailWord_7395678).sum := by decide
  have hdescent : baseEnd_7395678 < baseStart_7395678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395683 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 3, 3, 2]
def baseStart_7395683 : Nat := 118140960795 + 7395683 * 2 ^ 59
def prefixEnd_7395683 : Nat := 4983230072969 + 3 ^ 40 * 7395683 * 2
def baseEnd_7395683 : Nat := 3797540147285693089950379

theorem tailTrace_7395683 : CollatzResearch.WordTrace tailWord_7395683 prefixEnd_7395683 3797540147285693089950379 := by
  unfold tailWord_7395683
  simp only [CollatzResearch.WordTrace]
  refine ⟨269742719265711047942407703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179828479510474031961605135 269742719265711047942407703)
  ·
    refine ⟨404614078898566571913611555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269742719265711047942407703 404614078898566571913611555)
    ·
      refine ⟨606921118347849857870417333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404614078898566571913611555 606921118347849857870417333)
      ·
        refine ⟨56898854845110924175351625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 606921118347849857870417333 56898854845110924175351625)
        ·
          refine ⟨42674141133833193131513719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56898854845110924175351625 42674141133833193131513719)
          ·
            refine ⟨64011211700749789697270579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42674141133833193131513719 64011211700749789697270579)
            ·
              refine ⟨96016817551124684545905869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64011211700749789697270579 96016817551124684545905869)
              ·
                refine ⟨36006306581671756704714701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96016817551124684545905869 36006306581671756704714701)
                ·
                  refine ⟨13502364968126908764268013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36006306581671756704714701 13502364968126908764268013)
                  ·
                    refine ⟨5063386863047590786600505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13502364968126908764268013 5063386863047590786600505)
                    ·
                      refine ⟨3797540147285693089950379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063386863047590786600505 3797540147285693089950379)
                      ·
                        rfl

theorem cell23_7395683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_7395683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395683 prefixEnd_7395683 := by exact prefixLift 7395683
  have htrace : WordTrace (prefixWord ++ tailWord_7395683) baseStart_7395683 baseEnd_7395683 := by
    simpa [prefixWord, tailWord_7395683, baseEnd_7395683] using wordTrace_append hprefix tailTrace_7395683
  have hstable : (prefixWord ++ tailWord_7395683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395683).length < 2 ^ (prefixWord ++ tailWord_7395683).sum := by decide
  have hdescent : baseEnd_7395683 < baseStart_7395683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395689 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_7395689 : Nat := 118140960795 + 7395689 * 2 ^ 59
def prefixEnd_7395689 : Nat := 4983230072969 + 3 ^ 40 * 7395689 * 2
def baseEnd_7395689 : Nat := 1265847742723206688825117

theorem tailTrace_7395689 : CollatzResearch.WordTrace tailWord_7395689 prefixEnd_7395689 1265847742723206688825117 := by
  unfold tailWord_7395689
  simp only [CollatzResearch.WordTrace]
  refine ⟨269742938103689310967126121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179828625402459540644750747 269742938103689310967126121)
  ·
    refine ⟨202307203577766983225344591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269742938103689310967126121 202307203577766983225344591)
    ·
      refine ⟨303460805366650474838016887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202307203577766983225344591 303460805366650474838016887)
      ·
        refine ⟨455191208049975712257025331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303460805366650474838016887 455191208049975712257025331)
        ·
          refine ⟨682786812074963568385537997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455191208049975712257025331 682786812074963568385537997)
          ·
            refine ⟨256045054528111338144576749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682786812074963568385537997 256045054528111338144576749)
            ·
              refine ⟨96016895448041751804216281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256045054528111338144576749 96016895448041751804216281)
              ·
                refine ⟨72012671586031313853162211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96016895448041751804216281 72012671586031313853162211)
                ·
                  refine ⟨108019007379046970779743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72012671586031313853162211 108019007379046970779743317)
                  ·
                    refine ⟨1265847742723206688825117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108019007379046970779743317 1265847742723206688825117)
                    ·
                      rfl

theorem cell23_7395689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_7395689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395689 prefixEnd_7395689 := by exact prefixLift 7395689
  have htrace : WordTrace (prefixWord ++ tailWord_7395689) baseStart_7395689 baseEnd_7395689 := by
    simpa [prefixWord, tailWord_7395689, baseEnd_7395689] using wordTrace_append hprefix tailTrace_7395689
  have hstable : (prefixWord ++ tailWord_7395689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395689).length < 2 ^ (prefixWord ++ tailWord_7395689).sum := by decide
  have hdescent : baseEnd_7395689 < baseStart_7395689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395830 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7395830 : Nat := 118140960795 + 7395830 * 2 ^ 59
def prefixEnd_7395830 : Nat := 4983230072969 + 3 ^ 40 * 7395830 * 2
def baseEnd_7395830 : Nat := 1265871876313968004937401

theorem tailTrace_7395830 : CollatzResearch.WordTrace tailWord_7395830 prefixEnd_7395830 1265871876313968004937401 := by
  unfold tailWord_7395830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859255049761155753000559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179832053864118994698672629 16859255049761155753000559)
  ·
    refine ⟨25288882574641733629500839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16859255049761155753000559 25288882574641733629500839)
    ·
      refine ⟨37933323861962600444251259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25288882574641733629500839 37933323861962600444251259)
      ·
        refine ⟨56899985792943900666376889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37933323861962600444251259 56899985792943900666376889)
        ·
          refine ⟨42674989344707925499782667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56899985792943900666376889 42674989344707925499782667)
          ·
            refine ⟨64012484017061888249674001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42674989344707925499782667 64012484017061888249674001)
            ·
              refine ⟨48009363012796416187255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64012484017061888249674001 48009363012796416187255501)
              ·
                refine ⟨18003511129798656070220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48009363012796416187255501 18003511129798656070220813)
                ·
                  refine ⟨6751316673674496026332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18003511129798656070220813 6751316673674496026332805)
                  ·
                    refine ⟨1265871876313968004937401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751316673674496026332805 1265871876313968004937401)
                    ·
                      rfl

theorem cell23_7395830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7395830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395830 prefixEnd_7395830 := by exact prefixLift 7395830
  have htrace : WordTrace (prefixWord ++ tailWord_7395830) baseStart_7395830 baseEnd_7395830 := by
    simpa [prefixWord, tailWord_7395830, baseEnd_7395830] using wordTrace_append hprefix tailTrace_7395830
  have hstable : (prefixWord ++ tailWord_7395830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395830).length < 2 ^ (prefixWord ++ tailWord_7395830).sum := by decide
  have hdescent : baseEnd_7395830 < baseStart_7395830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395938 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7395938 : Nat := 118140960795 + 7395938 * 2 ^ 59
def prefixEnd_7395938 : Nat := 4983230072969 + 3 ^ 40 * 7395938 * 2
def baseEnd_7395938 : Nat := 3797671084852589592261707

theorem tailTrace_7395938 : CollatzResearch.WordTrace tailWord_7395938 prefixEnd_7395938 3797671084852589592261707 := by
  unfold tailWord_7395938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67438004969946806623235117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179834679919858150995293645 67438004969946806623235117)
  ·
    refine ⟨25289251863730052483713169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67438004969946806623235117 25289251863730052483713169)
    ·
      refine ⟨18966938897797539362784877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25289251863730052483713169 18966938897797539362784877)
      ·
        refine ⟨7112602086674077261044329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18966938897797539362784877 7112602086674077261044329)
        ·
          refine ⟨5334451565005557945783247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112602086674077261044329 5334451565005557945783247)
          ·
            refine ⟨8001677347508336918674871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334451565005557945783247 8001677347508336918674871)
            ·
              refine ⟨12002516021262505378012307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001677347508336918674871 12002516021262505378012307)
              ·
                refine ⟨18003774031893758067018461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002516021262505378012307 18003774031893758067018461)
                ·
                  refine ⟨6751415261960159275131923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18003774031893758067018461 6751415261960159275131923)
                  ·
                    refine ⟨10127122892940238912697885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6751415261960159275131923 10127122892940238912697885)
                    ·
                      refine ⟨3797671084852589592261707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10127122892940238912697885 3797671084852589592261707)
                      ·
                        rfl

theorem cell23_7395938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7395938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395938 prefixEnd_7395938 := by exact prefixLift 7395938
  have htrace : WordTrace (prefixWord ++ tailWord_7395938) baseStart_7395938 baseEnd_7395938 := by
    simpa [prefixWord, tailWord_7395938, baseEnd_7395938] using wordTrace_append hprefix tailTrace_7395938
  have hstable : (prefixWord ++ tailWord_7395938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395938).length < 2 ^ (prefixWord ++ tailWord_7395938).sum := by decide
  have hdescent : baseEnd_7395938 < baseStart_7395938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395950 : List Nat := [4, 1, 2, 2, 2, 2, 2, 8]
def baseStart_7395950 : Nat := 118140960795 + 7395950 * 2 ^ 59
def prefixEnd_7395950 : Nat := 4983230072969 + 3 ^ 40 * 7395950 * 2
def baseEnd_7395950 : Nat := 140654712837794205381913

theorem tailTrace_7395950 : CollatzResearch.WordTrace tailWord_7395950 prefixEnd_7395950 140654712837794205381913 := by
  unfold tailWord_7395950
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719057194467969067797163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179834971703829168361584869 33719057194467969067797163)
  ·
    refine ⟨50578585791701953601695745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33719057194467969067797163 50578585791701953601695745)
    ·
      refine ⟨37933939343776465201271809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50578585791701953601695745 37933939343776465201271809)
      ·
        refine ⟨28450454507832348900953857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37933939343776465201271809 28450454507832348900953857)
        ·
          refine ⟨21337840880874261675715393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28450454507832348900953857 21337840880874261675715393)
          ·
            refine ⟨16003380660655696256786545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21337840880874261675715393 16003380660655696256786545)
            ·
              refine ⟨12002535495491772192589909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16003380660655696256786545 12002535495491772192589909)
              ·
                refine ⟨140654712837794205381913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12002535495491772192589909 140654712837794205381913)
                ·
                  rfl

theorem cell23_7395950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_7395950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395950 prefixEnd_7395950 := by exact prefixLift 7395950
  have htrace : WordTrace (prefixWord ++ tailWord_7395950) baseStart_7395950 baseEnd_7395950 := by
    simpa [prefixWord, tailWord_7395950, baseEnd_7395950] using wordTrace_append hprefix tailTrace_7395950
  have hstable : (prefixWord ++ tailWord_7395950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395950).length < 2 ^ (prefixWord ++ tailWord_7395950).sum := by decide
  have hdescent : baseEnd_7395950 < baseStart_7395950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395993 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_7395993 : Nat := 118140960795 + 7395993 * 2 ^ 59
def prefixEnd_7395993 : Nat := 4983230072969 + 3 ^ 40 * 7395993 * 2
def baseEnd_7395993 : Nat := 1265899775429528959024651

theorem tailTrace_7395993 : CollatzResearch.WordTrace tailWord_7395993 prefixEnd_7395993 1265899775429528959024651 := by
  unfold tailWord_7395993
  simp only [CollatzResearch.WordTrace]
  refine ⟨269754025894587970886192633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179836017263058647257461755 269754025894587970886192633)
  ·
    refine ⟨202315519420940978164644475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269754025894587970886192633 202315519420940978164644475)
    ·
      refine ⟨303473279131411467246966713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202315519420940978164644475 303473279131411467246966713)
      ·
        refine ⟨227604959348558600435225035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303473279131411467246966713 227604959348558600435225035)
        ·
          refine ⟨341407439022837900652837553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227604959348558600435225035 341407439022837900652837553)
          ·
            refine ⟨256055579267128425489628165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341407439022837900652837553 256055579267128425489628165)
            ·
              refine ⟨48010421112586579779305281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256055579267128425489628165 48010421112586579779305281)
              ·
                refine ⟨36007815834439934834478961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48010421112586579779305281 36007815834439934834478961)
                ·
                  refine ⟨27005861875829951125859221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36007815834439934834478961 27005861875829951125859221)
                  ·
                    refine ⟨1265899775429528959024651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27005861875829951125859221 1265899775429528959024651)
                    ·
                      rfl

theorem cell23_7395993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_7395993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7395993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7395993 prefixEnd_7395993 := by exact prefixLift 7395993
  have htrace : WordTrace (prefixWord ++ tailWord_7395993) baseStart_7395993 baseEnd_7395993 := by
    simpa [prefixWord, tailWord_7395993, baseEnd_7395993] using wordTrace_append hprefix tailTrace_7395993
  have hstable : (prefixWord ++ tailWord_7395993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395993).length < 2 ^ (prefixWord ++ tailWord_7395993).sum := by decide
  have hdescent : baseEnd_7395993 < baseStart_7395993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396003 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_7396003 : Nat := 118140960795 + 7396003 * 2 ^ 59
def prefixEnd_7396003 : Nat := 4983230072969 + 3 ^ 40 * 7396003 * 2
def baseEnd_7396003 : Nat := 3797704461095131837948907

theorem tailTrace_7396003 : CollatzResearch.WordTrace tailWord_7396003 prefixEnd_7396003 3797704461095131837948907 := by
  unfold tailWord_7396003
  simp only [CollatzResearch.WordTrace]
  refine ⟨269754390624551742594056663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179836260416367828396037775 269754390624551742594056663)
  ·
    refine ⟨404631585936827613891084995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269754390624551742594056663 404631585936827613891084995)
    ·
      refine ⟨606947378905241420836627493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404631585936827613891084995 606947378905241420836627493)
      ·
        refine ⟨113802633544732766406867655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 606947378905241420836627493 113802633544732766406867655)
        ·
          refine ⟨170703950317099149610301483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113802633544732766406867655 170703950317099149610301483)
          ·
            refine ⟨256055925475648724415452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170703950317099149610301483 256055925475648724415452225)
            ·
              refine ⟨192041944106736543311589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256055925475648724415452225 192041944106736543311589169)
              ·
                refine ⟨144031458080052407483691877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192041944106736543311589169 144031458080052407483691877)
                ·
                  refine ⟨27005898390009826403192227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144031458080052407483691877 27005898390009826403192227)
                  ·
                    refine ⟨40508847585014739604788341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27005898390009826403192227 40508847585014739604788341)
                    ·
                      refine ⟨3797704461095131837948907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40508847585014739604788341 3797704461095131837948907)
                      ·
                        rfl

theorem cell23_7396003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_7396003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396003 prefixEnd_7396003 := by exact prefixLift 7396003
  have htrace : WordTrace (prefixWord ++ tailWord_7396003) baseStart_7396003 baseEnd_7396003 := by
    simpa [prefixWord, tailWord_7396003, baseEnd_7396003] using wordTrace_append hprefix tailTrace_7396003
  have hstable : (prefixWord ++ tailWord_7396003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396003).length < 2 ^ (prefixWord ++ tailWord_7396003).sum := by decide
  have hdescent : baseEnd_7396003 < baseStart_7396003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396030 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_7396030 : Nat := 118140960795 + 7396030 * 2 ^ 59
def prefixEnd_7396030 : Nat := 4983230072969 + 3 ^ 40 * 7396030 * 2
def baseEnd_7396030 : Nat := 3797718325072803232311283

theorem tailTrace_7396030 : CollatzResearch.WordTrace tailWord_7396030 prefixEnd_7396030 3797718325072803232311283 := by
  unfold tailWord_7396030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719421924431740775661193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179836916930302617470193029 33719421924431740775661193)
  ·
    refine ⟨25289566443323805581745895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33719421924431740775661193 25289566443323805581745895)
    ·
      refine ⟨37934349664985708372618843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25289566443323805581745895 37934349664985708372618843)
      ·
        refine ⟨56901524497478562558928265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37934349664985708372618843 56901524497478562558928265)
        ·
          refine ⟨42676143373108921919196199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56901524497478562558928265 42676143373108921919196199)
          ·
            refine ⟨64014215059663382878794299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42676143373108921919196199 64014215059663382878794299)
            ·
              refine ⟨96021322589495074318191449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64014215059663382878794299 96021322589495074318191449)
              ·
                refine ⟨72015991942121305738643587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96021322589495074318191449 72015991942121305738643587)
                ·
                  refine ⟨108023987913181958607965381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72015991942121305738643587 108023987913181958607965381)
                  ·
                    refine ⟨20254497733721617238993509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108023987913181958607965381 20254497733721617238993509)
                    ·
                      refine ⟨3797718325072803232311283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20254497733721617238993509 3797718325072803232311283)
                      ·
                        rfl

theorem cell23_7396030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_7396030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396030 prefixEnd_7396030 := by exact prefixLift 7396030
  have htrace : WordTrace (prefixWord ++ tailWord_7396030) baseStart_7396030 baseEnd_7396030 := by
    simpa [prefixWord, tailWord_7396030, baseEnd_7396030] using wordTrace_append hprefix tailTrace_7396030
  have hstable : (prefixWord ++ tailWord_7396030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396030).length < 2 ^ (prefixWord ++ tailWord_7396030).sum := by decide
  have hdescent : baseEnd_7396030 < baseStart_7396030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396045 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7396045 : Nat := 118140960795 + 7396045 * 2 ^ 59
def prefixEnd_7396045 : Nat := 4983230072969 + 3 ^ 40 * 7396045 * 2
def baseEnd_7396045 : Nat := 3797726027282620673623715

theorem tailTrace_7396045 : CollatzResearch.WordTrace tailWord_7396045 prefixEnd_7396045 3797726027282620673623715 := by
  unfold tailWord_7396045
  simp only [CollatzResearch.WordTrace]
  refine ⟨269755922490399583767085589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179837281660266389178057059 269755922490399583767085589)
  ·
    refine ⟨12644808866737480489082137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269755922490399583767085589 12644808866737480489082137)
    ·
      refine ⟨9483606650053110366811603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12644808866737480489082137 9483606650053110366811603)
      ·
        refine ⟨14225409975079665550217405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483606650053110366811603 14225409975079665550217405)
        ·
          refine ⟨5334528740654874581331527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14225409975079665550217405 5334528740654874581331527)
          ·
            refine ⟨8001793110982311871997291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334528740654874581331527 8001793110982311871997291)
            ·
              refine ⟨12002689666473467807995937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001793110982311871997291 12002689666473467807995937)
              ·
                refine ⟨9002017249855100855996953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12002689666473467807995937 9002017249855100855996953)
                ·
                  refine ⟨6751512937391325641997715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002017249855100855996953 6751512937391325641997715)
                  ·
                    refine ⟨10127269406086988462996573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6751512937391325641997715 10127269406086988462996573)
                    ·
                      refine ⟨3797726027282620673623715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10127269406086988462996573 3797726027282620673623715)
                      ·
                        rfl

theorem cell23_7396045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7396045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396045 prefixEnd_7396045 := by exact prefixLift 7396045
  have htrace : WordTrace (prefixWord ++ tailWord_7396045) baseStart_7396045 baseEnd_7396045 := by
    simpa [prefixWord, tailWord_7396045, baseEnd_7396045] using wordTrace_append hprefix tailTrace_7396045
  have hstable : (prefixWord ++ tailWord_7396045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396045).length < 2 ^ (prefixWord ++ tailWord_7396045).sum := by decide
  have hdescent : baseEnd_7396045 < baseStart_7396045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396067 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7396067 : Nat := 118140960795 + 7396067 * 2 ^ 59
def prefixEnd_7396067 : Nat := 4983230072969 + 3 ^ 40 * 7396067 * 2
def baseEnd_7396067 : Nat := 3797737323857019587548613

theorem tailTrace_7396067 : CollatzResearch.WordTrace tailWord_7396067 prefixEnd_7396067 3797737323857019587548613 := by
  unfold tailWord_7396067
  simp only [CollatzResearch.WordTrace]
  refine ⟨269756724896319881524386455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179837816597546587682924303 269756724896319881524386455)
  ·
    refine ⟨404635087344479822286579683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269756724896319881524386455 404635087344479822286579683)
    ·
      refine ⟨606952631016719733429869525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404635087344479822286579683 606952631016719733429869525)
      ·
        refine ⟨14225452289454368752262567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 606952631016719733429869525 14225452289454368752262567)
        ·
          refine ⟨21338178434181553128393851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225452289454368752262567 21338178434181553128393851)
          ·
            refine ⟨32007267651272329692590777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21338178434181553128393851 32007267651272329692590777)
            ·
              refine ⟨24005450738454247269443083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32007267651272329692590777 24005450738454247269443083)
              ·
                refine ⟨36008176107681370904164625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005450738454247269443083 36008176107681370904164625)
                ·
                  refine ⟨27006132080761028178123469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36008176107681370904164625 27006132080761028178123469)
                  ·
                    refine ⟨10127299530285385566796301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27006132080761028178123469 10127299530285385566796301)
                    ·
                      refine ⟨3797737323857019587548613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10127299530285385566796301 3797737323857019587548613)
                      ·
                        rfl

theorem cell23_7396067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7396067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396067 prefixEnd_7396067 := by exact prefixLift 7396067
  have htrace : WordTrace (prefixWord ++ tailWord_7396067) baseStart_7396067 baseEnd_7396067 := by
    simpa [prefixWord, tailWord_7396067, baseEnd_7396067] using wordTrace_append hprefix tailTrace_7396067
  have hstable : (prefixWord ++ tailWord_7396067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396067).length < 2 ^ (prefixWord ++ tailWord_7396067).sum := by decide
  have hdescent : baseEnd_7396067 < baseStart_7396067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396083 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 10]
def baseStart_7396083 : Nat := 118140960795 + 7396083 * 2 ^ 59
def prefixEnd_7396083 : Nat := 4983230072969 + 3 ^ 40 * 7396083 * 2
def baseEnd_7396083 : Nat := 1265915179849163841649513

theorem tailTrace_7396083 : CollatzResearch.WordTrace tailWord_7396083 prefixEnd_7396083 1265915179849163841649513 := by
  unfold tailWord_7396083
  simp only [CollatzResearch.WordTrace]
  refine ⟨269757308464261916256968903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179838205642841277504645935 269757308464261916256968903)
  ·
    refine ⟨404635962696392874385453355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269757308464261916256968903 404635962696392874385453355)
    ·
      refine ⟨606953944044589311578180033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404635962696392874385453355 606953944044589311578180033)
      ·
        refine ⟨455215458033441983683635025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606953944044589311578180033 455215458033441983683635025)
        ·
          refine ⟨341411593525081487762726269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455215458033441983683635025 341411593525081487762726269)
          ·
            refine ⟨128029347571905557911022351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341411593525081487762726269 128029347571905557911022351)
            ·
              refine ⟨192044021357858336866533527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128029347571905557911022351 192044021357858336866533527)
              ·
                refine ⟨288066032036787505299800291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192044021357858336866533527 288066032036787505299800291)
                ·
                  refine ⟨432099048055181257949700437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288066032036787505299800291 432099048055181257949700437)
                  ·
                    refine ⟨1265915179849163841649513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 432099048055181257949700437 1265915179849163841649513)
                    ·
                      rfl

theorem cell23_7396083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_7396083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396083 prefixEnd_7396083 := by exact prefixLift 7396083
  have htrace : WordTrace (prefixWord ++ tailWord_7396083) baseStart_7396083 baseEnd_7396083 := by
    simpa [prefixWord, tailWord_7396083, baseEnd_7396083] using wordTrace_append hprefix tailTrace_7396083
  have hstable : (prefixWord ++ tailWord_7396083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396083).length < 2 ^ (prefixWord ++ tailWord_7396083).sum := by decide
  have hdescent : baseEnd_7396083 < baseStart_7396083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396090 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_7396090 : Nat := 118140960795 + 7396090 * 2 ^ 59
def prefixEnd_7396090 : Nat := 4983230072969 + 3 ^ 40 * 7396090 * 2
def baseEnd_7396090 : Nat := 3797749133912072997561007

theorem tailTrace_7396090 : CollatzResearch.WordTrace tailWord_7396090 prefixEnd_7396090 3797749133912072997561007 := by
  unfold tailWord_7396090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67439390943809139113118431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179838375850157704301649149 67439390943809139113118431)
  ·
    refine ⟨101159086415713708669677647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67439390943809139113118431 101159086415713708669677647)
    ·
      refine ⟨151738629623570563004516471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101159086415713708669677647 151738629623570563004516471)
      ·
        refine ⟨227607944435355844506774707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151738629623570563004516471 227607944435355844506774707)
        ·
          refine ⟨341411916653033766760162061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227607944435355844506774707 341411916653033766760162061)
          ·
            refine ⟨128029468744887662535060773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341411916653033766760162061 128029468744887662535060773)
            ·
              refine ⟨24005525389666436725323895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128029468744887662535060773 24005525389666436725323895)
              ·
                refine ⟨36008288084499655087985843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005525389666436725323895 36008288084499655087985843)
                ·
                  refine ⟨54012432126749482631978765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36008288084499655087985843 54012432126749482631978765)
                  ·
                    refine ⟨20254662047531055986992037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54012432126749482631978765 20254662047531055986992037)
                    ·
                      refine ⟨3797749133912072997561007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20254662047531055986992037 3797749133912072997561007)
                      ·
                        rfl

theorem cell23_7396090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_7396090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396090 prefixEnd_7396090 := by exact prefixLift 7396090
  have htrace : WordTrace (prefixWord ++ tailWord_7396090) baseStart_7396090 baseEnd_7396090 := by
    simpa [prefixWord, tailWord_7396090, baseEnd_7396090] using wordTrace_append hprefix tailTrace_7396090
  have hstable : (prefixWord ++ tailWord_7396090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396090).length < 2 ^ (prefixWord ++ tailWord_7396090).sum := by decide
  have hdescent : baseEnd_7396090 < baseStart_7396090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396114 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7396114 : Nat := 118140960795 + 7396114 * 2 ^ 59
def prefixEnd_7396114 : Nat := 4983230072969 + 3 ^ 40 * 7396114 * 2
def baseEnd_7396114 : Nat := 3797761457447780903660897

theorem tailTrace_7396114 : CollatzResearch.WordTrace tailWord_7396114 prefixEnd_7396114 3797761457447780903660897 := by
  unfold tailWord_7396114
  simp only [CollatzResearch.WordTrace]
  refine ⟨67439609781787402137836849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179838959418099739034231597 67439609781787402137836849)
  ·
    refine ⟨50579707336340551603377637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67439609781787402137836849 50579707336340551603377637)
    ·
      refine ⟨9483695125563853425633307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50579707336340551603377637 9483695125563853425633307)
      ·
        refine ⟨14225542688345780138449961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483695125563853425633307 14225542688345780138449961)
        ·
          refine ⟨10669157016259335103837471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14225542688345780138449961 10669157016259335103837471)
          ·
            refine ⟨16003735524389002655756207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669157016259335103837471 16003735524389002655756207)
            ·
              refine ⟨24005603286583503983634311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16003735524389002655756207 24005603286583503983634311)
              ·
                refine ⟨36008404929875255975451467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005603286583503983634311 36008404929875255975451467)
                ·
                  refine ⟨54012607394812883963177201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36008404929875255975451467 54012607394812883963177201)
                  ·
                    refine ⟨40509455546109662972382901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54012607394812883963177201 40509455546109662972382901)
                    ·
                      refine ⟨3797761457447780903660897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40509455546109662972382901 3797761457447780903660897)
                      ·
                        rfl

theorem cell23_7396114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7396114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396114 prefixEnd_7396114 := by exact prefixLift 7396114
  have htrace : WordTrace (prefixWord ++ tailWord_7396114) baseStart_7396114 baseEnd_7396114 := by
    simpa [prefixWord, tailWord_7396114, baseEnd_7396114] using wordTrace_append hprefix tailTrace_7396114
  have hstable : (prefixWord ++ tailWord_7396114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396114).length < 2 ^ (prefixWord ++ tailWord_7396114).sum := by decide
  have hdescent : baseEnd_7396114 < baseStart_7396114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396167 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_7396167 : Nat := 118140960795 + 7396167 * 2 ^ 59
def prefixEnd_7396167 : Nat := 4983230072969 + 3 ^ 40 * 7396167 * 2
def baseEnd_7396167 : Nat := 3797788671922469196298153

theorem tailTrace_7396167 : CollatzResearch.WordTrace tailWord_7396167 prefixEnd_7396167 3797788671922469196298153 := by
  unfold tailWord_7396167
  simp only [CollatzResearch.WordTrace]
  refine ⟨269760372195957598603026755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179840248130638399068684503 269760372195957598603026755)
  ·
    refine ⟨404640558293936397904540133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269760372195957598603026755 404640558293936397904540133)
    ·
      refine ⟨75870104680113074607101275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404640558293936397904540133 75870104680113074607101275)
      ·
        refine ⟨113805157020169611910651913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75870104680113074607101275 113805157020169611910651913)
        ·
          refine ⟨85353867765127208932988935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113805157020169611910651913 85353867765127208932988935)
          ·
            refine ⟨128030801647690813399483403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85353867765127208932988935 128030801647690813399483403)
            ·
              refine ⟨192046202471536220099225105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128030801647690813399483403 192046202471536220099225105)
              ·
                refine ⟨144034651853652165074418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192046202471536220099225105 144034651853652165074418829)
                ·
                  refine ⟨54012994445119561902907061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144034651853652165074418829 54012994445119561902907061)
                  ·
                    refine ⟨5063718229229958928397537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54012994445119561902907061 5063718229229958928397537)
                    ·
                      refine ⟨3797788671922469196298153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063718229229958928397537 3797788671922469196298153)
                      ·
                        rfl

theorem cell23_7396167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_7396167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396167 prefixEnd_7396167 := by exact prefixLift 7396167
  have htrace : WordTrace (prefixWord ++ tailWord_7396167) baseStart_7396167 baseEnd_7396167 := by
    simpa [prefixWord, tailWord_7396167, baseEnd_7396167] using wordTrace_append hprefix tailTrace_7396167
  have hstable : (prefixWord ++ tailWord_7396167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396167).length < 2 ^ (prefixWord ++ tailWord_7396167).sum := by decide
  have hdescent : baseEnd_7396167 < baseStart_7396167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396197 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7396197 : Nat := 118140960795 + 7396197 * 2 ^ 59
def prefixEnd_7396197 : Nat := 4983230072969 + 3 ^ 40 * 7396197 * 2
def baseEnd_7396197 : Nat := 3797804076342104078923015

theorem tailTrace_7396197 : CollatzResearch.WordTrace tailWord_7396197 prefixEnd_7396197 3797804076342104078923015 := by
  unfold tailWord_7396197
  simp only [CollatzResearch.WordTrace]
  refine ⟨269761466385848913726618845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179840977590565942484412563 269761466385848913726618845)
  ·
    refine ⟨101160549894693342647482067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269761466385848913726618845 101160549894693342647482067)
    ·
      refine ⟨151740824842040013971223101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101160549894693342647482067 151740824842040013971223101)
      ·
        refine ⟨56902809315765005239208663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151740824842040013971223101 56902809315765005239208663)
        ·
          refine ⟨85354213973647507858812995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56902809315765005239208663 85354213973647507858812995)
          ·
            refine ⟨128031320960471261788219493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85354213973647507858812995 128031320960471261788219493)
            ·
              refine ⟨24005872680088361585291155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128031320960471261788219493 24005872680088361585291155)
              ·
                refine ⟨36008809020132542377936733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005872680088361585291155 36008809020132542377936733)
                ·
                  refine ⟨13503303382549703391726275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36008809020132542377936733 13503303382549703391726275)
                  ·
                    refine ⟨20254955073824555087589413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13503303382549703391726275 20254955073824555087589413)
                    ·
                      refine ⟨3797804076342104078923015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20254955073824555087589413 3797804076342104078923015)
                      ·
                        rfl

theorem cell23_7396197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7396197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396197 prefixEnd_7396197 := by exact prefixLift 7396197
  have htrace : WordTrace (prefixWord ++ tailWord_7396197) baseStart_7396197 baseEnd_7396197 := by
    simpa [prefixWord, tailWord_7396197, baseEnd_7396197] using wordTrace_append hprefix tailTrace_7396197
  have hstable : (prefixWord ++ tailWord_7396197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396197).length < 2 ^ (prefixWord ++ tailWord_7396197).sum := by decide
  have hdescent : baseEnd_7396197 < baseStart_7396197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396231 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_7396231 : Nat := 118140960795 + 7396231 * 2 ^ 59
def prefixEnd_7396231 : Nat := 4983230072969 + 3 ^ 40 * 7396231 * 2
def baseEnd_7396231 : Nat := 3797821534684356945897859

theorem tailTrace_7396231 : CollatzResearch.WordTrace tailWord_7396231 prefixEnd_7396231 3797821534684356945897859 := by
  unfold tailWord_7396231
  simp only [CollatzResearch.WordTrace]
  refine ⟨269762706467725737533356547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179841804311817158355571031 269762706467725737533356547)
  ·
    refine ⟨404644059701588606300034821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269762706467725737533356547 404644059701588606300034821)
    ·
      refine ⟨75870761194047863681256529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404644059701588606300034821 75870761194047863681256529)
      ·
        refine ⟨56903070895535897760942397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75870761194047863681256529 56903070895535897760942397)
        ·
          refine ⟨21338651585825961660353399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56903070895535897760942397 21338651585825961660353399)
          ·
            refine ⟨32007977378738942490530099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21338651585825961660353399 32007977378738942490530099)
            ·
              refine ⟨48011966068108413735795149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32007977378738942490530099 48011966068108413735795149)
              ·
                refine ⟨18004487275540655150923181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48011966068108413735795149 18004487275540655150923181)
                ·
                  refine ⟨6751682728327745681596193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18004487275540655150923181 6751682728327745681596193)
                  ·
                    refine ⟨5063762046245809261197145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6751682728327745681596193 5063762046245809261197145)
                    ·
                      refine ⟨3797821534684356945897859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063762046245809261197145 3797821534684356945897859)
                      ·
                        rfl

theorem cell23_7396231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_7396231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396231 prefixEnd_7396231 := by exact prefixLift 7396231
  have htrace : WordTrace (prefixWord ++ tailWord_7396231) baseStart_7396231 baseEnd_7396231 := by
    simpa [prefixWord, tailWord_7396231, baseEnd_7396231] using wordTrace_append hprefix tailTrace_7396231
  have hstable : (prefixWord ++ tailWord_7396231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396231).length < 2 ^ (prefixWord ++ tailWord_7396231).sum := by decide
  have hdescent : baseEnd_7396231 < baseStart_7396231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396234 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7396234 : Nat := 118140960795 + 7396234 * 2 ^ 59
def prefixEnd_7396234 : Nat := 4983230072969 + 3 ^ 40 * 7396234 * 2
def baseEnd_7396234 : Nat := 3797823075126320434160345

theorem tailTrace_7396234 : CollatzResearch.WordTrace tailWord_7396234 prefixEnd_7396234 3797823075126320434160345 := by
  unfold tailWord_7396234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67440703971678717261428939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179841877257809912697143837 67440703971678717261428939)
  ·
    refine ⟨101161055957518075892143409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67440703971678717261428939 101161055957518075892143409)
    ·
      refine ⟨75870791968138556919107557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101161055957518075892143409 75870791968138556919107557)
      ·
        refine ⟨14225773494025979422332667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75870791968138556919107557 14225773494025979422332667)
        ·
          refine ⟨21338660241038969133499001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225773494025979422332667 21338660241038969133499001)
          ·
            refine ⟨16003995180779226850124251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21338660241038969133499001 16003995180779226850124251)
            ·
              refine ⟨24005992771168840275186377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16003995180779226850124251 24005992771168840275186377)
              ·
                refine ⟨18004494578376630206389783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24005992771168840275186377 18004494578376630206389783)
                ·
                  refine ⟨27006741867564945309584675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18004494578376630206389783 27006741867564945309584675)
                  ·
                    refine ⟨40510112801347417964377013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27006741867564945309584675 40510112801347417964377013)
                    ·
                      refine ⟨3797823075126320434160345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40510112801347417964377013 3797823075126320434160345)
                      ·
                        rfl

theorem cell23_7396234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7396234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396234 prefixEnd_7396234 := by exact prefixLift 7396234
  have htrace : WordTrace (prefixWord ++ tailWord_7396234) baseStart_7396234 baseEnd_7396234 := by
    simpa [prefixWord, tailWord_7396234, baseEnd_7396234] using wordTrace_append hprefix tailTrace_7396234
  have hstable : (prefixWord ++ tailWord_7396234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396234).length < 2 ^ (prefixWord ++ tailWord_7396234).sum := by decide
  have hdescent : baseEnd_7396234 < baseStart_7396234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396274 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_7396274 : Nat := 118140960795 + 7396274 * 2 ^ 59
def prefixEnd_7396274 : Nat := 4983230072969 + 3 ^ 40 * 7396274 * 2
def baseEnd_7396274 : Nat := 3797843614352500277660161

theorem tailTrace_7396274 : CollatzResearch.WordTrace tailWord_7396274 prefixEnd_7396274 3797843614352500277660161 := by
  unfold tailWord_7396274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67441068701642488969292969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179842849871046637251447917 67441068701642488969292969)
  ·
    refine ⟨50580801526231866726969727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67441068701642488969292969 50580801526231866726969727)
    ·
      refine ⟨75871202289347800090454591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50580801526231866726969727 75871202289347800090454591)
      ·
        refine ⟨113806803434021700135681887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75871202289347800090454591 113806803434021700135681887)
        ·
          refine ⟨170710205151032550203522831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113806803434021700135681887 170710205151032550203522831)
          ·
            refine ⟨256065307726548825305284247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170710205151032550203522831 256065307726548825305284247)
            ·
              refine ⟨384097961589823237957926371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256065307726548825305284247 384097961589823237957926371)
              ·
                refine ⟨576146942384734856936889557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384097961589823237957926371 576146942384734856936889557)
                ·
                  refine ⟨13503443962142223209458349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 576146942384734856936889557 13503443962142223209458349)
                  ·
                    refine ⟨5063791485803333703546881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13503443962142223209458349 5063791485803333703546881)
                    ·
                      refine ⟨3797843614352500277660161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063791485803333703546881 3797843614352500277660161)
                      ·
                        rfl

theorem cell23_7396274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_7396274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396274 prefixEnd_7396274 := by exact prefixLift 7396274
  have htrace : WordTrace (prefixWord ++ tailWord_7396274) baseStart_7396274 baseEnd_7396274 := by
    simpa [prefixWord, tailWord_7396274, baseEnd_7396274] using wordTrace_append hprefix tailTrace_7396274
  have hstable : (prefixWord ++ tailWord_7396274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396274).length < 2 ^ (prefixWord ++ tailWord_7396274).sum := by decide
  have hdescent : baseEnd_7396274 < baseStart_7396274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396277 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7396277 : Nat := 118140960795 + 7396277 * 2 ^ 59
def prefixEnd_7396277 : Nat := 4983230072969 + 3 ^ 40 * 7396277 * 2
def baseEnd_7396277 : Nat := 3797845154794463765922647

theorem tailTrace_7396277 : CollatzResearch.WordTrace tailWord_7396277 prefixEnd_7396277 3797845154794463765922647 := by
  unfold tailWord_7396277
  simp only [CollatzResearch.WordTrace]
  refine ⟨269764384225559087389531085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179842922817039391593020723 269764384225559087389531085)
  ·
    refine ⟨101161644084584657771074157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269764384225559087389531085 101161644084584657771074157)
    ·
      refine ⟨37935616531719246664152809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101161644084584657771074157 37935616531719246664152809)
      ·
        refine ⟨28451712398789434998114607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37935616531719246664152809 28451712398789434998114607)
        ·
          refine ⟨42677568598184152497171911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28451712398789434998114607 42677568598184152497171911)
          ·
            refine ⟨64016352897276228745757867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42677568598184152497171911 64016352897276228745757867)
            ·
              refine ⟨96024529345914343118636801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64016352897276228745757867 96024529345914343118636801)
              ·
                refine ⟨72018397009435757338977601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96024529345914343118636801 72018397009435757338977601)
                ·
                  refine ⟨54013797757076818004233201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72018397009435757338977601 54013797757076818004233201)
                  ·
                    refine ⟨40510348317807613503174901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54013797757076818004233201 40510348317807613503174901)
                    ·
                      refine ⟨3797845154794463765922647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40510348317807613503174901 3797845154794463765922647)
                      ·
                        rfl

theorem cell23_7396277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7396277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396277 prefixEnd_7396277 := by exact prefixLift 7396277
  have htrace : WordTrace (prefixWord ++ tailWord_7396277) baseStart_7396277 baseEnd_7396277 := by
    simpa [prefixWord, tailWord_7396277, baseEnd_7396277] using wordTrace_append hprefix tailTrace_7396277
  have hstable : (prefixWord ++ tailWord_7396277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396277).length < 2 ^ (prefixWord ++ tailWord_7396277).sum := by decide
  have hdescent : baseEnd_7396277 < baseStart_7396277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396292 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7396292 : Nat := 118140960795 + 7396292 * 2 ^ 59
def prefixEnd_7396292 : Nat := 4983230072969 + 3 ^ 40 * 7396292 * 2
def baseEnd_7396292 : Nat := 1265950952334760402411693

theorem tailTrace_7396292 : CollatzResearch.WordTrace tailWord_7396292 prefixEnd_7396292 1265950952334760402411693 := by
  unfold tailWord_7396292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134882465660252372475663565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179843287547003163300884753 134882465660252372475663565)
  ·
    refine ⟨50580924622594639678373837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134882465660252372475663565 50580924622594639678373837)
    ·
      refine ⟨18967846733472989879390189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50580924622594639678373837 18967846733472989879390189)
      ·
        refine ⟨7112942525052371204771321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18967846733472989879390189 7112942525052371204771321)
        ·
          refine ⟨5334706893789278403578491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112942525052371204771321 5334706893789278403578491)
          ·
            refine ⟨8002060340683917605367737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334706893789278403578491 8002060340683917605367737)
            ·
              refine ⟨6001545255512938204025803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8002060340683917605367737 6001545255512938204025803)
              ·
                refine ⟨9002317883269407306038705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001545255512938204025803 9002317883269407306038705)
                ·
                  refine ⟨6751738412452055479529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002317883269407306038705 6751738412452055479529029)
                  ·
                    refine ⟨1265950952334760402411693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751738412452055479529029 1265950952334760402411693)
                    ·
                      rfl

theorem cell23_7396292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7396292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396292 prefixEnd_7396292 := by exact prefixLift 7396292
  have htrace : WordTrace (prefixWord ++ tailWord_7396292) baseStart_7396292 baseEnd_7396292 := by
    simpa [prefixWord, tailWord_7396292, baseEnd_7396292] using wordTrace_append hprefix tailTrace_7396292
  have hstable : (prefixWord ++ tailWord_7396292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396292).length < 2 ^ (prefixWord ++ tailWord_7396292).sum := by decide
  have hdescent : baseEnd_7396292 < baseStart_7396292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396304 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2]
def baseStart_7396304 : Nat := 118140960795 + 7396304 * 2 ^ 59
def prefixEnd_7396304 : Nat := 4983230072969 + 3 ^ 40 * 7396304 * 2
def baseEnd_7396304 : Nat := 3797859018772135160285023

theorem tailTrace_7396304 : CollatzResearch.WordTrace tailWord_7396304 prefixEnd_7396304 3797859018772135160285023 := by
  unfold tailWord_7396304
  simp only [CollatzResearch.WordTrace]
  refine ⟨134882684498230635500381983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179843579330974180667175977 134882684498230635500381983)
  ·
    refine ⟨202324026747345953250572975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134882684498230635500381983 202324026747345953250572975)
    ·
      refine ⟨303486040121018929875859463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202324026747345953250572975 303486040121018929875859463)
      ·
        refine ⟨455229060181528394813789195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303486040121018929875859463 455229060181528394813789195)
        ·
          refine ⟨682843590272292592220683793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455229060181528394813789195 682843590272292592220683793)
          ·
            refine ⟨512132692704219444165512845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682843590272292592220683793 512132692704219444165512845)
            ·
              refine ⟨192049759764082291562067317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512132692704219444165512845 192049759764082291562067317)
              ·
                refine ⟨18004664977882714833943811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192049759764082291562067317 18004664977882714833943811)
                ·
                  refine ⟨27006997466824072250915717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18004664977882714833943811 27006997466824072250915717)
                  ·
                    refine ⟨5063812025029513547046697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27006997466824072250915717 5063812025029513547046697)
                    ·
                      refine ⟨3797859018772135160285023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063812025029513547046697 3797859018772135160285023)
                      ·
                        rfl

theorem cell23_7396304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2].length) (baseStart_7396304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396304 prefixEnd_7396304 := by exact prefixLift 7396304
  have htrace : WordTrace (prefixWord ++ tailWord_7396304) baseStart_7396304 baseEnd_7396304 := by
    simpa [prefixWord, tailWord_7396304, baseEnd_7396304] using wordTrace_append hprefix tailTrace_7396304
  have hstable : (prefixWord ++ tailWord_7396304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396304).length < 2 ^ (prefixWord ++ tailWord_7396304).sum := by decide
  have hdescent : baseEnd_7396304 < baseStart_7396304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396308 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7396308 : Nat := 118140960795 + 7396308 * 2 ^ 59
def prefixEnd_7396308 : Nat := 4983230072969 + 3 ^ 40 * 7396308 * 2
def baseEnd_7396308 : Nat := 3797861072694753144635005

theorem tailTrace_7396308 : CollatzResearch.WordTrace tailWord_7396308 prefixEnd_7396308 3797861072694753144635005 := by
  unfold tailWord_7396308
  simp only [CollatzResearch.WordTrace]
  refine ⟨134882757444223389841954789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179843676592297853122606385 134882757444223389841954789)
  ·
    refine ⟨25290517020791885595366523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134882757444223389841954789 25290517020791885595366523)
    ·
      refine ⟨37935775531187828393049785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25290517020791885595366523 37935775531187828393049785)
      ·
        refine ⟨28451831648390871294787339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37935775531187828393049785 28451831648390871294787339)
        ·
          refine ⟨42677747472586306942181009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28451831648390871294787339 42677747472586306942181009)
          ·
            refine ⟨32008310604439730206635757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42677747472586306942181009 32008310604439730206635757)
            ·
              refine ⟨12003116476664898827488409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32008310604439730206635757 12003116476664898827488409)
              ·
                refine ⟨9002337357498674120616307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003116476664898827488409 9002337357498674120616307)
                ·
                  refine ⟨13503506036248011180924461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002337357498674120616307 13503506036248011180924461)
                  ·
                    refine ⟨5063814763593004192846673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13503506036248011180924461 5063814763593004192846673)
                    ·
                      refine ⟨3797861072694753144635005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063814763593004192846673 3797861072694753144635005)
                      ·
                        rfl

theorem cell23_7396308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7396308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396308 prefixEnd_7396308 := by exact prefixLift 7396308
  have htrace : WordTrace (prefixWord ++ tailWord_7396308) baseStart_7396308 baseEnd_7396308 := by
    simpa [prefixWord, tailWord_7396308, baseEnd_7396308] using wordTrace_append hprefix tailTrace_7396308
  have hstable : (prefixWord ++ tailWord_7396308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396308).length < 2 ^ (prefixWord ++ tailWord_7396308).sum := by decide
  have hdescent : baseEnd_7396308 < baseStart_7396308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396357 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_7396357 : Nat := 118140960795 + 7396357 * 2 ^ 59
def prefixEnd_7396357 : Nat := 4983230072969 + 3 ^ 40 * 7396357 * 2
def baseEnd_7396357 : Nat := 1265962077748941150974093

theorem tailTrace_7396357 : CollatzResearch.WordTrace tailWord_7396357 prefixEnd_7396357 1265962077748941150974093 := by
  unfold tailWord_7396357
  simp only [CollatzResearch.WordTrace]
  refine ⟨269767302065269261052443325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179844868043512840701628883 269767302065269261052443325)
  ·
    refine ⟨101162738274475972894666247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269767302065269261052443325 101162738274475972894666247)
    ·
      refine ⟨151744107411713959341999371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101162738274475972894666247 151744107411713959341999371)
      ·
        refine ⟨227616161117570939012999057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151744107411713959341999371 227616161117570939012999057)
        ·
          refine ⟨170712120838178204259749293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227616161117570939012999057 170712120838178204259749293)
          ·
            refine ⟨64017045314316826597405985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170712120838178204259749293 64017045314316826597405985)
            ·
              refine ⟨48012783985737619948054489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64017045314316826597405985 48012783985737619948054489)
              ·
                refine ⟨36009587989303214961040867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48012783985737619948054489 36009587989303214961040867)
                ·
                  refine ⟨54014381983954822441561301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36009587989303214961040867 54014381983954822441561301)
                  ·
                    refine ⟨1265962077748941150974093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54014381983954822441561301 1265962077748941150974093)
                    ·
                      rfl

theorem cell23_7396357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_7396357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396357 prefixEnd_7396357 := by exact prefixLift 7396357
  have htrace : WordTrace (prefixWord ++ tailWord_7396357) baseStart_7396357 baseEnd_7396357 := by
    simpa [prefixWord, tailWord_7396357, baseEnd_7396357] using wordTrace_append hprefix tailTrace_7396357
  have hstable : (prefixWord ++ tailWord_7396357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396357).length < 2 ^ (prefixWord ++ tailWord_7396357).sum := by decide
  have hdescent : baseEnd_7396357 < baseStart_7396357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396407 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_7396407 : Nat := 118140960795 + 7396407 * 2 ^ 59
def prefixEnd_7396407 : Nat := 4983230072969 + 3 ^ 40 * 7396407 * 2
def baseEnd_7396407 : Nat := 3797911907279548257297049

theorem tailTrace_7396407 : CollatzResearch.WordTrace tailWord_7396407 prefixEnd_7396407 3797911907279548257297049 := by
  unfold tailWord_7396407
  simp only [CollatzResearch.WordTrace]
  refine ⟨269769125715088119591763475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179846083810058746394508983 269769125715088119591763475)
  ·
    refine ⟨404653688572632179387645213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269769125715088119591763475 404653688572632179387645213)
    ·
      refine ⟨151745133214737067270366955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404653688572632179387645213 151745133214737067270366955)
      ·
        refine ⟨227617699822105600905550433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151745133214737067270366955 227617699822105600905550433)
        ·
          refine ⟨170713274866579200679162825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227617699822105600905550433 170713274866579200679162825)
          ·
            refine ⟨128034956149934400509372119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170713274866579200679162825 128034956149934400509372119)
            ·
              refine ⟨192052434224901600764058179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128034956149934400509372119 192052434224901600764058179)
              ·
                refine ⟨288078651337352401146087269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192052434224901600764058179 288078651337352401146087269)
                ·
                  refine ⟨54014747125753575214891363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288078651337352401146087269 54014747125753575214891363)
                  ·
                    refine ⟨81022120688630362822337045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54014747125753575214891363 81022120688630362822337045)
                    ·
                      refine ⟨3797911907279548257297049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81022120688630362822337045 3797911907279548257297049)
                      ·
                        rfl

theorem cell23_7396407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_7396407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396407 prefixEnd_7396407 := by exact prefixLift 7396407
  have htrace : WordTrace (prefixWord ++ tailWord_7396407) baseStart_7396407 baseEnd_7396407 := by
    simpa [prefixWord, tailWord_7396407, baseEnd_7396407] using wordTrace_append hprefix tailTrace_7396407
  have hstable : (prefixWord ++ tailWord_7396407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396407).length < 2 ^ (prefixWord ++ tailWord_7396407).sum := by decide
  have hdescent : baseEnd_7396407 < baseStart_7396407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396434 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_7396434 : Nat := 118140960795 + 7396434 * 2 ^ 59
def prefixEnd_7396434 : Nat := 4983230072969 + 3 ^ 40 * 7396434 * 2
def baseEnd_7396434 : Nat := 421991752361913294628825

theorem tailTrace_7396434 : CollatzResearch.WordTrace tailWord_7396434 prefixEnd_7396434 421991752361913294628825 := by
  unfold tailWord_7396434
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442527621497575800749089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179846740323993535468664237 67442527621497575800749089)
  ·
    refine ⟨50581895716123181850561817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67442527621497575800749089 50581895716123181850561817)
    ·
      refine ⟨37936421787092386387921363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50581895716123181850561817 37936421787092386387921363)
      ·
        refine ⟨56904632680638579581882045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37936421787092386387921363 56904632680638579581882045)
        ·
          refine ⟨21339237255239467343205767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56904632680638579581882045 21339237255239467343205767)
          ·
            refine ⟨32008855882859201014808651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21339237255239467343205767 32008855882859201014808651)
            ·
              refine ⟨48013283824288801522212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32008855882859201014808651 48013283824288801522212977)
              ·
                refine ⟨36009962868216601141659733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48013283824288801522212977 36009962868216601141659733)
                ·
                  refine ⟨421991752361913294628825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36009962868216601141659733 421991752361913294628825)
                  ·
                    rfl

theorem cell23_7396434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_7396434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396434 prefixEnd_7396434 := by exact prefixLift 7396434
  have htrace : WordTrace (prefixWord ++ tailWord_7396434) baseStart_7396434 baseEnd_7396434 := by
    simpa [prefixWord, tailWord_7396434, baseEnd_7396434] using wordTrace_append hprefix tailTrace_7396434
  have hstable : (prefixWord ++ tailWord_7396434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396434).length < 2 ^ (prefixWord ++ tailWord_7396434).sum := by decide
  have hdescent : baseEnd_7396434 < baseStart_7396434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396455 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 1, 4]
def baseStart_7396455 : Nat := 118140960795 + 7396455 * 2 ^ 59
def prefixEnd_7396455 : Nat := 4983230072969 + 3 ^ 40 * 7396455 * 2
def baseEnd_7396455 : Nat := 1265978851450321356498943

theorem tailTrace_7396455 : CollatzResearch.WordTrace tailWord_7396455 prefixEnd_7396455 1265978851450321356498943 := by
  unfold tailWord_7396455
  simp only [CollatzResearch.WordTrace]
  refine ⟨269770876418914223789510819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179847250945942815859673879 269770876418914223789510819)
  ·
    refine ⟨404656314628371335684266229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269770876418914223789510819 404656314628371335684266229)
    ·
      refine ⟨37936529496409812720399959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 404656314628371335684266229 37936529496409812720399959)
      ·
        refine ⟨56904794244614719080599939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37936529496409812720399959 56904794244614719080599939)
        ·
          refine ⟨85357191366922078620899909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56904794244614719080599939 85357191366922078620899909)
          ·
            refine ⟨16004473381297889741418733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85357191366922078620899909 16004473381297889741418733)
            ·
              refine ⟨6001677517986708653032025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16004473381297889741418733 6001677517986708653032025)
              ·
                refine ⟨4501258138490031489774019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6001677517986708653032025 4501258138490031489774019)
                ·
                  refine ⟨6751887207735047234661029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501258138490031489774019 6751887207735047234661029)
                  ·
                    refine ⟨1265978851450321356498943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751887207735047234661029 1265978851450321356498943)
                    ·
                      rfl

theorem cell23_7396455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_7396455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396455 prefixEnd_7396455 := by exact prefixLift 7396455
  have htrace : WordTrace (prefixWord ++ tailWord_7396455) baseStart_7396455 baseEnd_7396455 := by
    simpa [prefixWord, tailWord_7396455, baseEnd_7396455] using wordTrace_append hprefix tailTrace_7396455
  have hstable : (prefixWord ++ tailWord_7396455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396455).length < 2 ^ (prefixWord ++ tailWord_7396455).sum := by decide
  have hdescent : baseEnd_7396455 < baseStart_7396455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396464 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_7396464 : Nat := 118140960795 + 7396464 * 2 ^ 59
def prefixEnd_7396464 : Nat := 4983230072969 + 3 ^ 40 * 7396464 * 2
def baseEnd_7396464 : Nat := 1265980391892284844761429

theorem tailTrace_7396464 : CollatzResearch.WordTrace tailWord_7396464 prefixEnd_7396464 1265980391892284844761429 := by
  unfold tailWord_7396464
  simp only [CollatzResearch.WordTrace]
  refine ⟨134885602337940809163294223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179847469783921078884392297 134885602337940809163294223)
  ·
    refine ⟨202328403506911213744941335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134885602337940809163294223 202328403506911213744941335)
    ·
      refine ⟨303492605260366820617412003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202328403506911213744941335 303492605260366820617412003)
      ·
        refine ⟨455238907890550230926118005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303492605260366820617412003 455238907890550230926118005)
        ·
          refine ⟨42678647614739084149323563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455238907890550230926118005 42678647614739084149323563)
          ·
            refine ⟨64017971422108626223985345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42678647614739084149323563 64017971422108626223985345)
            ·
              refine ⟨48013478566581469667989009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64017971422108626223985345 48013478566581469667989009)
              ·
                refine ⟨36010108924936102250991757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48013478566581469667989009 36010108924936102250991757)
                ·
                  refine ⟨13503790846851038344121909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36010108924936102250991757 13503790846851038344121909)
                  ·
                    refine ⟨1265980391892284844761429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13503790846851038344121909 1265980391892284844761429)
                    ·
                      rfl

theorem cell23_7396464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_7396464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396464 prefixEnd_7396464 := by exact prefixLift 7396464
  have htrace : WordTrace (prefixWord ++ tailWord_7396464) baseStart_7396464 baseEnd_7396464 := by
    simpa [prefixWord, tailWord_7396464, baseEnd_7396464] using wordTrace_append hprefix tailTrace_7396464
  have hstable : (prefixWord ++ tailWord_7396464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396464).length < 2 ^ (prefixWord ++ tailWord_7396464).sum := by decide
  have hdescent : baseEnd_7396464 < baseStart_7396464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396467 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_7396467 : Nat := 118140960795 + 7396467 * 2 ^ 59
def prefixEnd_7396467 : Nat := 4983230072969 + 3 ^ 40 * 7396467 * 2
def baseEnd_7396467 : Nat := 3797942716118818022546773

theorem tailTrace_7396467 : CollatzResearch.WordTrace tailWord_7396467 prefixEnd_7396467 3797942716118818022546773 := by
  unfold tailWord_7396467
  simp only [CollatzResearch.WordTrace]
  refine ⟨269771314094870749838947655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179847542729913833225965103 269771314094870749838947655)
  ·
    refine ⟨404656971142306124758421483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269771314094870749838947655 404656971142306124758421483)
    ·
      refine ⟨606985456713459187137632225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404656971142306124758421483 606985456713459187137632225)
      ·
        refine ⟨455239092535094390353224169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606985456713459187137632225 455239092535094390353224169)
        ·
          refine ⟨341429319401320792764918127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455239092535094390353224169 341429319401320792764918127)
          ·
            refine ⟨512143979101981189147377191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341429319401320792764918127 512143979101981189147377191)
            ·
              refine ⟨768215968652971783721065787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512143979101981189147377191 768215968652971783721065787)
              ·
                refine ⟨1152323952979457675581598681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768215968652971783721065787 1152323952979457675581598681)
                ·
                  refine ⟨864242964734593256686199011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1152323952979457675581598681 864242964734593256686199011)
                  ·
                    refine ⟨1296364447101889885029298517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864242964734593256686199011 1296364447101889885029298517)
                    ·
                      refine ⟨3797942716118818022546773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1296364447101889885029298517 3797942716118818022546773)
                      ·
                        rfl

theorem cell23_7396467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_7396467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396467 prefixEnd_7396467 := by exact prefixLift 7396467
  have htrace : WordTrace (prefixWord ++ tailWord_7396467) baseStart_7396467 baseEnd_7396467 := by
    simpa [prefixWord, tailWord_7396467, baseEnd_7396467] using wordTrace_append hprefix tailTrace_7396467
  have hstable : (prefixWord ++ tailWord_7396467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396467).length < 2 ^ (prefixWord ++ tailWord_7396467).sum := by decide
  have hdescent : baseEnd_7396467 < baseStart_7396467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396471 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_7396471 : Nat := 118140960795 + 7396471 * 2 ^ 59
def prefixEnd_7396471 : Nat := 4983230072969 + 3 ^ 40 * 7396471 * 2
def baseEnd_7396471 : Nat := 3797944770041436006896755

theorem tailTrace_7396471 : CollatzResearch.WordTrace tailWord_7396471 prefixEnd_7396471 3797944770041436006896755 := by
  unfold tailWord_7396471
  simp only [CollatzResearch.WordTrace]
  refine ⟨269771459986856258522093267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179847639991237505681395511 269771459986856258522093267)
  ·
    refine ⟨404657189980284387783139901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269771459986856258522093267 404657189980284387783139901)
    ·
      refine ⟨151746446242606645418677463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404657189980284387783139901 151746446242606645418677463)
      ·
        refine ⟨227619669363909968128016195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151746446242606645418677463 227619669363909968128016195)
        ·
          refine ⟨341429504045864952192024293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227619669363909968128016195 341429504045864952192024293)
          ·
            refine ⟨64018032008599678536004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341429504045864952192024293 64018032008599678536004555)
            ·
              refine ⟨96027048012899517804006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64018032008599678536004555 96027048012899517804006833)
              ·
                refine ⟨72020286009674638353005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96027048012899517804006833 72020286009674638353005125)
                ·
                  refine ⟨13503803626813994691188461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72020286009674638353005125 13503803626813994691188461)
                  ·
                    refine ⟨5063926360055248009195673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13503803626813994691188461 5063926360055248009195673)
                    ·
                      refine ⟨3797944770041436006896755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5063926360055248009195673 3797944770041436006896755)
                      ·
                        rfl

theorem cell23_7396471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_7396471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396471 prefixEnd_7396471 := by exact prefixLift 7396471
  have htrace : WordTrace (prefixWord ++ tailWord_7396471) baseStart_7396471 baseEnd_7396471 := by
    simpa [prefixWord, tailWord_7396471, baseEnd_7396471] using wordTrace_append hprefix tailTrace_7396471
  have hstable : (prefixWord ++ tailWord_7396471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396471).length < 2 ^ (prefixWord ++ tailWord_7396471).sum := by decide
  have hdescent : baseEnd_7396471 < baseStart_7396471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396481 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7396481 : Nat := 118140960795 + 7396481 * 2 ^ 59
def prefixEnd_7396481 : Nat := 4983230072969 + 3 ^ 40 * 7396481 * 2
def baseEnd_7396481 : Nat := 1265983301615993655923903

theorem tailTrace_7396481 : CollatzResearch.WordTrace tailWord_7396481 prefixEnd_7396481 1265983301615993655923903 := by
  unfold tailWord_7396481
  simp only [CollatzResearch.WordTrace]
  refine ⟨269771824716820030229957297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179847883144546686819971531 269771824716820030229957297)
  ·
    refine ⟨202328868537615022672467973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269771824716820030229957297 202328868537615022672467973)
    ·
      refine ⟨37936662850802816751087745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202328868537615022672467973 37936662850802816751087745)
      ·
        refine ⟨28452497138102112563315809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37936662850802816751087745 28452497138102112563315809)
        ·
          refine ⟨21339372853576584422486857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28452497138102112563315809 21339372853576584422486857)
          ·
            refine ⟨16004529640182438316865143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21339372853576584422486857 16004529640182438316865143)
            ·
              refine ⟨24006794460273657475297715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004529640182438316865143 24006794460273657475297715)
              ·
                refine ⟨36010191690410486212946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24006794460273657475297715 36010191690410486212946573)
                ·
                  refine ⟨13503821883903932329854965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36010191690410486212946573 13503821883903932329854965)
                  ·
                    refine ⟨1265983301615993655923903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13503821883903932329854965 1265983301615993655923903)
                    ·
                      rfl

theorem cell23_7396481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7396481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396481 prefixEnd_7396481 := by exact prefixLift 7396481
  have htrace : WordTrace (prefixWord ++ tailWord_7396481) baseStart_7396481 baseEnd_7396481 := by
    simpa [prefixWord, tailWord_7396481, baseEnd_7396481] using wordTrace_append hprefix tailTrace_7396481
  have hstable : (prefixWord ++ tailWord_7396481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396481).length < 2 ^ (prefixWord ++ tailWord_7396481).sum := by decide
  have hdescent : baseEnd_7396481 < baseStart_7396481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396546 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7396546 : Nat := 118140960795 + 7396546 * 2 ^ 59
def prefixEnd_7396546 : Nat := 4983230072969 + 3 ^ 40 * 7396546 * 2
def baseEnd_7396546 : Nat := 3797983281090523213458911

theorem tailTrace_7396546 : CollatzResearch.WordTrace tailWord_7396546 prefixEnd_7396546 3797983281090523213458911 := by
  unfold tailWord_7396546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67443548865396136582768373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179849463641056364220715661 67443548865396136582768373)
  ·
    refine ⟨6322832706130887804634535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67443548865396136582768373 6322832706130887804634535)
    ·
      refine ⟨9484249059196331706951803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6322832706130887804634535 9484249059196331706951803)
      ·
        refine ⟨14226373588794497560427705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484249059196331706951803 14226373588794497560427705)
        ·
          refine ⟨10669780191595873170320779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14226373588794497560427705 10669780191595873170320779)
          ·
            refine ⟨16004670287393809755481169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669780191595873170320779 16004670287393809755481169)
            ·
              refine ⟨12003502715545357316610877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16004670287393809755481169 12003502715545357316610877)
              ·
                refine ⟨4501313518329508993729079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12003502715545357316610877 4501313518329508993729079)
                ·
                  refine ⟨6751970277494263490593619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501313518329508993729079 6751970277494263490593619)
                  ·
                    refine ⟨10127955416241395235890429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6751970277494263490593619 10127955416241395235890429)
                    ·
                      refine ⟨3797983281090523213458911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10127955416241395235890429 3797983281090523213458911)
                      ·
                        rfl

theorem cell23_7396546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7396546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396546 prefixEnd_7396546 := by exact prefixLift 7396546
  have htrace : WordTrace (prefixWord ++ tailWord_7396546) baseStart_7396546 baseEnd_7396546 := by
    simpa [prefixWord, tailWord_7396546, baseEnd_7396546] using wordTrace_append hprefix tailTrace_7396546
  have hstable : (prefixWord ++ tailWord_7396546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396546).length < 2 ^ (prefixWord ++ tailWord_7396546).sum := by decide
  have hdescent : baseEnd_7396546 < baseStart_7396546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396595 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 1, 3, 2]
def baseStart_7396595 : Nat := 118140960795 + 7396595 * 2 ^ 59
def prefixEnd_7396595 : Nat := 4983230072969 + 3 ^ 40 * 7396595 * 2
def baseEnd_7396595 : Nat := 3798008441642593521746185

theorem tailTrace_7396595 : CollatzResearch.WordTrace tailWord_7396595 prefixEnd_7396595 3798008441642593521746185 := by
  unfold tailWord_7396595
  simp only [CollatzResearch.WordTrace]
  refine ⟨269775982638407027699607239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179850655092271351799738159 269775982638407027699607239)
  ·
    refine ⟨404663973957610541549410859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269775982638407027699607239 404663973957610541549410859)
    ·
      refine ⟨606995960936415812324116289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404663973957610541549410859 606995960936415812324116289)
      ·
        refine ⟨455246970702311859243087217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606995960936415812324116289 455246970702311859243087217)
        ·
          refine ⟨341435228026733894432315413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455246970702311859243087217 341435228026733894432315413)
          ·
            refine ⟨16004776313753151301514785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 341435228026733894432315413 16004776313753151301514785)
            ·
              refine ⟨12003582235314863476136089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16004776313753151301514785 12003582235314863476136089)
              ·
                refine ⟨9002686676486147607102067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003582235314863476136089 9002686676486147607102067)
                ·
                  refine ⟨13504030014729221410653101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002686676486147607102067 13504030014729221410653101)
                  ·
                    refine ⟨5064011255523458028994913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13504030014729221410653101 5064011255523458028994913)
                    ·
                      refine ⟨3798008441642593521746185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064011255523458028994913 3798008441642593521746185)
                      ·
                        rfl

theorem cell23_7396595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3, 2].length) (baseStart_7396595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396595 prefixEnd_7396595 := by exact prefixLift 7396595
  have htrace : WordTrace (prefixWord ++ tailWord_7396595) baseStart_7396595 baseEnd_7396595 := by
    simpa [prefixWord, tailWord_7396595, baseEnd_7396595] using wordTrace_append hprefix tailTrace_7396595
  have hstable : (prefixWord ++ tailWord_7396595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396595).length < 2 ^ (prefixWord ++ tailWord_7396595).sum := by decide
  have hdescent : baseEnd_7396595 < baseStart_7396595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396611 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_7396611 : Nat := 118140960795 + 7396611 * 2 ^ 59
def prefixEnd_7396611 : Nat := 4983230072969 + 3 ^ 40 * 7396611 * 2
def baseEnd_7396611 : Nat := 3798016657333065459146111

theorem tailTrace_7396611 : CollatzResearch.WordTrace tailWord_7396611 prefixEnd_7396611 3798016657333065459146111 := by
  unfold tailWord_7396611
  simp only [CollatzResearch.WordTrace]
  refine ⟨269776566206349062432189687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179851044137566041621459791 269776566206349062432189687)
  ·
    refine ⟨404664849309523593648284531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269776566206349062432189687 404664849309523593648284531)
    ·
      refine ⟨606997273964285390472426797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404664849309523593648284531 606997273964285390472426797)
      ·
        refine ⟨227623977736607021427160049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606997273964285390472426797 227623977736607021427160049)
        ·
          refine ⟨170717983302455266070370037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227623977736607021427160049 170717983302455266070370037)
          ·
            refine ⟨16004810934605181194097191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170717983302455266070370037 16004810934605181194097191)
            ·
              refine ⟨24007216401907771791145787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004810934605181194097191 24007216401907771791145787)
              ·
                refine ⟨36010824602861657686718681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24007216401907771791145787 36010824602861657686718681)
                ·
                  refine ⟨27008118452146243265039011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36010824602861657686718681 27008118452146243265039011)
                  ·
                    refine ⟨40512177678219364897558517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27008118452146243265039011 40512177678219364897558517)
                    ·
                      refine ⟨3798016657333065459146111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40512177678219364897558517 3798016657333065459146111)
                      ·
                        rfl

theorem cell23_7396611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_7396611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396611 prefixEnd_7396611 := by exact prefixLift 7396611
  have htrace : WordTrace (prefixWord ++ tailWord_7396611) baseStart_7396611 baseEnd_7396611 := by
    simpa [prefixWord, tailWord_7396611, baseEnd_7396611] using wordTrace_append hprefix tailTrace_7396611
  have hstable : (prefixWord ++ tailWord_7396611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396611).length < 2 ^ (prefixWord ++ tailWord_7396611).sum := by decide
  have hdescent : baseEnd_7396611 < baseStart_7396611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396625 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_7396625 : Nat := 118140960795 + 7396625 * 2 ^ 59
def prefixEnd_7396625 : Nat := 4983230072969 + 3 ^ 40 * 7396625 * 2
def baseEnd_7396625 : Nat := 3798023846062228404371047

theorem tailTrace_7396625 : CollatzResearch.WordTrace tailWord_7396625 prefixEnd_7396625 3798023846062228404371047 := by
  unfold tailWord_7396625
  simp only [CollatzResearch.WordTrace]
  refine ⟨269777076828298342823199329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179851384552198895215466219 269777076828298342823199329)
  ·
    refine ⟨202332807621223757117399497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269777076828298342823199329 202332807621223757117399497)
    ·
      refine ⟨151749605715917817838049623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202332807621223757117399497 151749605715917817838049623)
      ·
        refine ⟨227624408573876726757074435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151749605715917817838049623 227624408573876726757074435)
        ·
          refine ⟨341436612860815090135611653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227624408573876726757074435 341436612860815090135611653)
          ·
            refine ⟨64019364911402829400427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341436612860815090135611653 64019364911402829400427185)
            ·
              refine ⟨48014523683552122050320389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64019364911402829400427185 48014523683552122050320389)
              ·
                refine ⟨9002723190666022884435073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48014523683552122050320389 9002723190666022884435073)
                ·
                  refine ⟨6752042392999517163326305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002723190666022884435073 6752042392999517163326305)
                  ·
                    refine ⟨5064031794749637872494729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6752042392999517163326305 5064031794749637872494729)
                    ·
                      refine ⟨3798023846062228404371047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064031794749637872494729 3798023846062228404371047)
                      ·
                        rfl

theorem cell23_7396625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_7396625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396625 prefixEnd_7396625 := by exact prefixLift 7396625
  have htrace : WordTrace (prefixWord ++ tailWord_7396625) baseStart_7396625 baseEnd_7396625 := by
    simpa [prefixWord, tailWord_7396625, baseEnd_7396625] using wordTrace_append hprefix tailTrace_7396625
  have hstable : (prefixWord ++ tailWord_7396625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396625).length < 2 ^ (prefixWord ++ tailWord_7396625).sum := by decide
  have hdescent : baseEnd_7396625 < baseStart_7396625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396641 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7396641 : Nat := 118140960795 + 7396641 * 2 ^ 59
def prefixEnd_7396641 : Nat := 4983230072969 + 3 ^ 40 * 7396641 * 2
def baseEnd_7396641 : Nat := 3798032061752700341770973

theorem tailTrace_7396641 : CollatzResearch.WordTrace tailWord_7396641 prefixEnd_7396641 3798032061752700341770973 := by
  unfold tailWord_7396641
  simp only [CollatzResearch.WordTrace]
  refine ⟨269777660396240377555781777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179851773597493585037187851 269777660396240377555781777)
  ·
    refine ⟨202333245297180283166836333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269777660396240377555781777 202333245297180283166836333)
    ·
      refine ⟨75874966986442606187563625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202333245297180283166836333 75874966986442606187563625)
      ·
        refine ⟨56906225239831954640672719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75874966986442606187563625 56906225239831954640672719)
        ·
          refine ⟨85359337859747931961009079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56906225239831954640672719 85359337859747931961009079)
          ·
            refine ⟨128039006789621897941513619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85359337859747931961009079 128039006789621897941513619)
            ·
              refine ⟨192058510184432846912270429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128039006789621897941513619 192058510184432846912270429)
              ·
                refine ⟨72021941319162317592101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192058510184432846912270429 72021941319162317592101411)
                ·
                  refine ⟨108032911978743476388152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72021941319162317592101411 108032911978743476388152117)
                  ·
                    refine ⟨10128085498007200911389261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108032911978743476388152117 10128085498007200911389261)
                    ·
                      refine ⟨3798032061752700341770973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10128085498007200911389261 3798032061752700341770973)
                      ·
                        rfl

theorem cell23_7396641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7396641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396641 prefixEnd_7396641 := by exact prefixLift 7396641
  have htrace : WordTrace (prefixWord ++ tailWord_7396641) baseStart_7396641 baseEnd_7396641 := by
    simpa [prefixWord, tailWord_7396641, baseEnd_7396641] using wordTrace_append hprefix tailTrace_7396641
  have hstable : (prefixWord ++ tailWord_7396641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396641).length < 2 ^ (prefixWord ++ tailWord_7396641).sum := by decide
  have hdescent : baseEnd_7396641 < baseStart_7396641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396671 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_7396671 : Nat := 118140960795 + 7396671 * 2 ^ 59
def prefixEnd_7396671 : Nat := 4983230072969 + 3 ^ 40 * 7396671 * 2
def baseEnd_7396671 : Nat := 3798047466172335224395835

theorem tailTrace_7396671 : CollatzResearch.WordTrace tailWord_7396671 prefixEnd_7396671 3798047466172335224395835 := by
  unfold tailWord_7396671
  simp only [CollatzResearch.WordTrace]
  refine ⟨269778754586131692679373867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179852503057421128452915911 269778754586131692679373867)
  ·
    refine ⟨404668131879197539019060801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269778754586131692679373867 404668131879197539019060801)
    ·
      refine ⟨303501098909398154264295601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404668131879197539019060801 303501098909398154264295601)
      ·
        refine ⟨227625824182048615698221701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303501098909398154264295601 227625824182048615698221701)
        ·
          refine ⟨42679842034134115443416569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227625824182048615698221701 42679842034134115443416569)
          ·
            refine ⟨32009881525600586582562427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42679842034134115443416569 32009881525600586582562427)
            ·
              refine ⟨48014822288400879873843641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32009881525600586582562427 48014822288400879873843641)
              ·
                refine ⟨36011116716300659905382731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48014822288400879873843641 36011116716300659905382731)
                ·
                  refine ⟨54016675074450989858074097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36011116716300659905382731 54016675074450989858074097)
                  ·
                    refine ⟨40512506305838242393555573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54016675074450989858074097 40512506305838242393555573)
                    ·
                      refine ⟨3798047466172335224395835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40512506305838242393555573 3798047466172335224395835)
                      ·
                        rfl

theorem cell23_7396671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_7396671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396671 prefixEnd_7396671 := by exact prefixLift 7396671
  have htrace : WordTrace (prefixWord ++ tailWord_7396671) baseStart_7396671 baseEnd_7396671 := by
    simpa [prefixWord, tailWord_7396671, baseEnd_7396671] using wordTrace_append hprefix tailTrace_7396671
  have hstable : (prefixWord ++ tailWord_7396671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396671).length < 2 ^ (prefixWord ++ tailWord_7396671).sum := by decide
  have hdescent : baseEnd_7396671 < baseStart_7396671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396698 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_7396698 : Nat := 118140960795 + 7396698 * 2 ^ 59
def prefixEnd_7396698 : Nat := 4983230072969 + 3 ^ 40 * 7396698 * 2
def baseEnd_7396698 : Nat := 3798061330150006618758211

theorem tailTrace_7396698 : CollatzResearch.WordTrace tailWord_7396698 prefixEnd_7396698 3798061330150006618758211 := by
  unfold tailWord_7396698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67444934839258469072651687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179853159571355917527071165 67444934839258469072651687)
  ·
    refine ⟨101167402258887703608977531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67444934839258469072651687 101167402258887703608977531)
    ·
      refine ⟨151751103388331555413466297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101167402258887703608977531 151751103388331555413466297)
      ·
        refine ⟨113813327541248666560099723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151751103388331555413466297 113813327541248666560099723)
        ·
          refine ⟨170719991311872999840149585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113813327541248666560099723 170719991311872999840149585)
          ·
            refine ⟨128039993483904749880112189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170719991311872999840149585 128039993483904749880112189)
            ·
              refine ⟨48014997556464281205042071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128039993483904749880112189 48014997556464281205042071)
              ·
                refine ⟨72022496334696421807563107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48014997556464281205042071 72022496334696421807563107)
                ·
                  refine ⟨108033744502044632711344661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72022496334696421807563107 108033744502044632711344661)
                  ·
                    refine ⟨5064081773533342158344281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108033744502044632711344661 5064081773533342158344281)
                    ·
                      refine ⟨3798061330150006618758211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064081773533342158344281 3798061330150006618758211)
                      ·
                        rfl

theorem cell23_7396698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_7396698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396698 prefixEnd_7396698 := by exact prefixLift 7396698
  have htrace : WordTrace (prefixWord ++ tailWord_7396698) baseStart_7396698 baseEnd_7396698 := by
    simpa [prefixWord, tailWord_7396698, baseEnd_7396698] using wordTrace_append hprefix tailTrace_7396698
  have hstable : (prefixWord ++ tailWord_7396698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396698).length < 2 ^ (prefixWord ++ tailWord_7396698).sum := by decide
  have hdescent : baseEnd_7396698 < baseStart_7396698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396708 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_7396708 : Nat := 118140960795 + 7396708 * 2 ^ 59
def prefixEnd_7396708 : Nat := 4983230072969 + 3 ^ 40 * 7396708 * 2
def baseEnd_7396708 : Nat := 1266022154985517193211055

theorem tailTrace_7396708 : CollatzResearch.WordTrace tailWord_7396708 prefixEnd_7396708 1266022154985517193211055 := by
  unfold tailWord_7396708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134890052043498823999235389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179853402724665098665647185 134890052043498823999235389)
  ·
    refine ⟨50583769516312058999713271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134890052043498823999235389 50583769516312058999713271)
    ·
      refine ⟨75875654274468088499569907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50583769516312058999713271 75875654274468088499569907)
      ·
        refine ⟨113813481411702132749354861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75875654274468088499569907 113813481411702132749354861)
        ·
          refine ⟨42680055529388299781008073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113813481411702132749354861 42680055529388299781008073)
          ·
            refine ⟨32010041647041224835756055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42680055529388299781008073 32010041647041224835756055)
            ·
              refine ⟨48015062470561837253634083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32010041647041224835756055 48015062470561837253634083)
              ·
                refine ⟨72022593705842755880451125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48015062470561837253634083 72022593705842755880451125)
                ·
                  refine ⟨6752118159922758363792293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72022593705842755880451125 6752118159922758363792293)
                  ·
                    refine ⟨1266022154985517193211055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752118159922758363792293 1266022154985517193211055)
                    ·
                      rfl

theorem cell23_7396708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_7396708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396708 prefixEnd_7396708 := by exact prefixLift 7396708
  have htrace : WordTrace (prefixWord ++ tailWord_7396708) baseStart_7396708 baseEnd_7396708 := by
    simpa [prefixWord, tailWord_7396708, baseEnd_7396708] using wordTrace_append hprefix tailTrace_7396708
  have hstable : (prefixWord ++ tailWord_7396708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396708).length < 2 ^ (prefixWord ++ tailWord_7396708).sum := by decide
  have hdescent : baseEnd_7396708 < baseStart_7396708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396712 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7396712 : Nat := 118140960795 + 7396712 * 2 ^ 59
def prefixEnd_7396712 : Nat := 4983230072969 + 3 ^ 40 * 7396712 * 2
def baseEnd_7396712 : Nat := 1266022839626389854661049

theorem tailTrace_7396712 : CollatzResearch.WordTrace tailWord_7396712 prefixEnd_7396712 1266022839626389854661049 := by
  unfold tailWord_7396712
  simp only [CollatzResearch.WordTrace]
  refine ⟨134890124989491578340808195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179853499985988771121077593 134890124989491578340808195)
  ·
    refine ⟨202335187484237367511212293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134890124989491578340808195 202335187484237367511212293)
    ·
      refine ⟨37937847653294506408352305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202335187484237367511212293 37937847653294506408352305)
      ·
        refine ⟨28453385739970879806264229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37937847653294506408352305 28453385739970879806264229)
        ·
          refine ⟨5335009826244539963674543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28453385739970879806264229 5335009826244539963674543)
          ·
            refine ⟨8002514739366809945511815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335009826244539963674543 8002514739366809945511815)
            ·
              refine ⟨12003772109050214918267723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002514739366809945511815 12003772109050214918267723)
              ·
                refine ⟨18005658163575322377401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12003772109050214918267723 18005658163575322377401585)
                ·
                  refine ⟨13504243622681491783051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18005658163575322377401585 13504243622681491783051189)
                  ·
                    refine ⟨1266022839626389854661049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13504243622681491783051189 1266022839626389854661049)
                    ·
                      rfl

theorem cell23_7396712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7396712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396712 prefixEnd_7396712 := by exact prefixLift 7396712
  have htrace : WordTrace (prefixWord ++ tailWord_7396712) baseStart_7396712 baseEnd_7396712 := by
    simpa [prefixWord, tailWord_7396712, baseEnd_7396712] using wordTrace_append hprefix tailTrace_7396712
  have hstable : (prefixWord ++ tailWord_7396712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396712).length < 2 ^ (prefixWord ++ tailWord_7396712).sum := by decide
  have hdescent : baseEnd_7396712 < baseStart_7396712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396741 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_7396741 : Nat := 118140960795 + 7396741 * 2 ^ 59
def prefixEnd_7396741 : Nat := 4983230072969 + 3 ^ 40 * 7396741 * 2
def baseEnd_7396741 : Nat := 3798083409818149950520513

theorem tailTrace_7396741 : CollatzResearch.WordTrace tailWord_7396741 prefixEnd_7396741 3798083409818149950520513 := by
  unfold tailWord_7396741
  simp only [CollatzResearch.WordTrace]
  refine ⟨269781307695878094634422077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179854205130585396422948051 269781307695878094634422077)
  ·
    refine ⟨101167990385954285487908279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269781307695878094634422077 101167990385954285487908279)
    ·
      refine ⟨151751985578931428231862419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101167990385954285487908279 151751985578931428231862419)
      ·
        refine ⟨227627978368397142347793629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151751985578931428231862419 227627978368397142347793629)
        ·
          refine ⟨85360491888148928380422611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227627978368397142347793629 85360491888148928380422611)
          ·
            refine ⟨128040737832223392570633917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85360491888148928380422611 128040737832223392570633917)
            ·
              refine ⟨48015276687083772213987719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128040737832223392570633917 48015276687083772213987719)
              ·
                refine ⟨72022915030625658320981579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48015276687083772213987719 72022915030625658320981579)
                ·
                  refine ⟨108034372545938487481472369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72022915030625658320981579 108034372545938487481472369)
                  ·
                    refine ⟨81025779409453865611104277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108034372545938487481472369 81025779409453865611104277)
                    ·
                      refine ⟨3798083409818149950520513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81025779409453865611104277 3798083409818149950520513)
                      ·
                        rfl

theorem cell23_7396741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_7396741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396741 prefixEnd_7396741 := by exact prefixLift 7396741
  have htrace : WordTrace (prefixWord ++ tailWord_7396741) baseStart_7396741 baseEnd_7396741 := by
    simpa [prefixWord, tailWord_7396741, baseEnd_7396741] using wordTrace_append hprefix tailTrace_7396741
  have hstable : (prefixWord ++ tailWord_7396741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396741).length < 2 ^ (prefixWord ++ tailWord_7396741).sum := by decide
  have hdescent : baseEnd_7396741 < baseStart_7396741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396775 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7396775 : Nat := 118140960795 + 7396775 * 2 ^ 59
def prefixEnd_7396775 : Nat := 4983230072969 + 3 ^ 40 * 7396775 * 2
def baseEnd_7396775 : Nat := 3798100868160402817495357

theorem tailTrace_7396775 : CollatzResearch.WordTrace tailWord_7396775 prefixEnd_7396775 3798100868160402817495357 := by
  unfold tailWord_7396775
  simp only [CollatzResearch.WordTrace]
  refine ⟨269782547777754918441159779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179855031851836612294106519 269782547777754918441159779)
  ·
    refine ⟨404673821666632377661739669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269782547777754918441159779 404673821666632377661739669)
    ·
      refine ⟨18969085390623392702894047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 404673821666632377661739669 18969085390623392702894047)
      ·
        refine ⟨28453628085935089054341071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969085390623392702894047 28453628085935089054341071)
        ·
          refine ⟨42680442128902633581511607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28453628085935089054341071 42680442128902633581511607)
          ·
            refine ⟨64020663193353950372267411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42680442128902633581511607 64020663193353950372267411)
            ·
              refine ⟨96030994790030925558401117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64020663193353950372267411 96030994790030925558401117)
              ·
                refine ⟨36011623046261597084400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96030994790030925558401117 36011623046261597084400419)
                ·
                  refine ⟨54017434569392395626600629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36011623046261597084400419 54017434569392395626600629)
                  ·
                    refine ⟨5064134490880537089993809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54017434569392395626600629 5064134490880537089993809)
                    ·
                      refine ⟨3798100868160402817495357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064134490880537089993809 3798100868160402817495357)
                      ·
                        rfl

theorem cell23_7396775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7396775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396775 prefixEnd_7396775 := by exact prefixLift 7396775
  have htrace : WordTrace (prefixWord ++ tailWord_7396775) baseStart_7396775 baseEnd_7396775 := by
    simpa [prefixWord, tailWord_7396775, baseEnd_7396775] using wordTrace_append hprefix tailTrace_7396775
  have hstable : (prefixWord ++ tailWord_7396775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396775).length < 2 ^ (prefixWord ++ tailWord_7396775).sum := by decide
  have hdescent : baseEnd_7396775 < baseStart_7396775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396776 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7396776 : Nat := 118140960795 + 7396776 * 2 ^ 59
def prefixEnd_7396776 : Nat := 4983230072969 + 3 ^ 40 * 7396776 * 2
def baseEnd_7396776 : Nat := 1266033793880352437860951

theorem tailTrace_7396776 : CollatzResearch.WordTrace tailWord_7396776 prefixEnd_7396776 1266033793880352437860951 := by
  unfold tailWord_7396776
  simp only [CollatzResearch.WordTrace]
  refine ⟨134891292125375647805973091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179855056167167530407964121 134891292125375647805973091)
  ·
    refine ⟨202336938188063471708959637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134891292125375647805973091 202336938188063471708959637)
    ·
      refine ⟨9484543977565475236357483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202336938188063471708959637 9484543977565475236357483)
      ·
        refine ⟨14226815966348212854536225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484543977565475236357483 14226815966348212854536225)
        ·
          refine ⟨10670111974761159640902169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14226815966348212854536225 10670111974761159640902169)
          ·
            refine ⟨8002583981070869730676627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10670111974761159640902169 8002583981070869730676627)
            ·
              refine ⟨12003875971606304596014941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002583981070869730676627 12003875971606304596014941)
              ·
                refine ⟨4501453489352364223505603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12003875971606304596014941 4501453489352364223505603)
                ·
                  refine ⟨6752180234028546335258405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501453489352364223505603 6752180234028546335258405)
                  ·
                    refine ⟨1266033793880352437860951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752180234028546335258405 1266033793880352437860951)
                    ·
                      rfl

theorem cell23_7396776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7396776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396776 prefixEnd_7396776 := by exact prefixLift 7396776
  have htrace : WordTrace (prefixWord ++ tailWord_7396776) baseStart_7396776 baseEnd_7396776 := by
    simpa [prefixWord, tailWord_7396776, baseEnd_7396776] using wordTrace_append hprefix tailTrace_7396776
  have hstable : (prefixWord ++ tailWord_7396776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396776).length < 2 ^ (prefixWord ++ tailWord_7396776).sum := by decide
  have hdescent : baseEnd_7396776 < baseStart_7396776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396808 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7396808 : Nat := 118140960795 + 7396808 * 2 ^ 59
def prefixEnd_7396808 : Nat := 4983230072969 + 3 ^ 40 * 7396808 * 2
def baseEnd_7396808 : Nat := 3798117813022001188382705

theorem tailTrace_7396808 : CollatzResearch.WordTrace tailWord_7396808 prefixEnd_7396808 3798117813022001188382705 := by
  unfold tailWord_7396808
  simp only [CollatzResearch.WordTrace]
  refine ⟨134891875693317682538555539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179855834257756910051407385 134891875693317682538555539)
  ·
    refine ⟨202337813539976523807833309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134891875693317682538555539 202337813539976523807833309)
    ·
      refine ⟨75876680077491196427937491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202337813539976523807833309 75876680077491196427937491)
      ·
        refine ⟨113815020116236794641906237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75876680077491196427937491 113815020116236794641906237)
        ·
          refine ⟨42680632543588797990714839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113815020116236794641906237 42680632543588797990714839)
          ·
            refine ⟨64020948815383196986072259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42680632543588797990714839 64020948815383196986072259)
            ·
              refine ⟨96031423223074795479108389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64020948815383196986072259 96031423223074795479108389)
              ·
                refine ⟨18005891854326524152332823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96031423223074795479108389 18005891854326524152332823)
                ·
                  refine ⟨27008837781489786228499235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18005891854326524152332823 27008837781489786228499235)
                  ·
                    refine ⟨40513256672234679342748853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27008837781489786228499235 40513256672234679342748853)
                    ·
                      refine ⟨3798117813022001188382705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40513256672234679342748853 3798117813022001188382705)
                      ·
                        rfl

theorem cell23_7396808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7396808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396808 prefixEnd_7396808 := by exact prefixLift 7396808
  have htrace : WordTrace (prefixWord ++ tailWord_7396808) baseStart_7396808 baseEnd_7396808 := by
    simpa [prefixWord, tailWord_7396808, baseEnd_7396808] using wordTrace_append hprefix tailTrace_7396808
  have hstable : (prefixWord ++ tailWord_7396808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396808).length < 2 ^ (prefixWord ++ tailWord_7396808).sum := by decide
  have hdescent : baseEnd_7396808 < baseStart_7396808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396811 : List Nat := [1, 1, 1, 1, 3, 3, 3, 10]
def baseStart_7396811 : Nat := 118140960795 + 7396811 * 2 ^ 59
def prefixEnd_7396811 : Nat := 4983230072969 + 3 ^ 40 * 7396811 * 2
def baseEnd_7396811 : Nat := 140671087165332025060933

theorem tailTrace_7396811 : CollatzResearch.WordTrace tailWord_7396811 prefixEnd_7396811 140671087165332025060933 := by
  unfold tailWord_7396811
  simp only [CollatzResearch.WordTrace]
  refine ⟨269783860805624496589470287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179855907203749664392980191 269783860805624496589470287)
  ·
    refine ⟨404675791208436744884205431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269783860805624496589470287 404675791208436744884205431)
    ·
      refine ⟨607013686812655117326308147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404675791208436744884205431 607013686812655117326308147)
      ·
        refine ⟨910520530218982675989462221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607013686812655117326308147 910520530218982675989462221)
        ·
          refine ⟨341445198832118503496048333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910520530218982675989462221 341445198832118503496048333)
          ·
            refine ⟨128041949562044438811018125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341445198832118503496048333 128041949562044438811018125)
            ·
              refine ⟨48015731085766664554131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128041949562044438811018125 48015731085766664554131797)
              ·
                refine ⟨140671087165332025060933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48015731085766664554131797 140671087165332025060933)
                ·
                  rfl

theorem cell23_7396811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 10].length) (baseStart_7396811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396811 prefixEnd_7396811 := by exact prefixLift 7396811
  have htrace : WordTrace (prefixWord ++ tailWord_7396811) baseStart_7396811 baseEnd_7396811 := by
    simpa [prefixWord, tailWord_7396811, baseEnd_7396811] using wordTrace_append hprefix tailTrace_7396811
  have hstable : (prefixWord ++ tailWord_7396811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396811).length < 2 ^ (prefixWord ++ tailWord_7396811).sum := by decide
  have hdescent : baseEnd_7396811 < baseStart_7396811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396822 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7396822 : Nat := 118140960795 + 7396822 * 2 ^ 59
def prefixEnd_7396822 : Nat := 4983230072969 + 3 ^ 40 * 7396822 * 2
def baseEnd_7396822 : Nat := 3798125001751164133607641

theorem tailTrace_7396822 : CollatzResearch.WordTrace tailWord_7396822 prefixEnd_7396822 3798125001751164133607641 := by
  unfold tailWord_7396822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861516375536540341757545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179856174672389763645413813 16861516375536540341757545)
  ·
    refine ⟨12646137281652405256318159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16861516375536540341757545 12646137281652405256318159)
    ·
      refine ⟨18969205922478607884477239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12646137281652405256318159 18969205922478607884477239)
      ·
        refine ⟨28453808883717911826715859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969205922478607884477239 28453808883717911826715859)
        ·
          refine ⟨42680713325576867740073789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28453808883717911826715859 42680713325576867740073789)
          ·
            refine ⟨16005267497091325402527671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42680713325576867740073789 16005267497091325402527671)
            ·
              refine ⟨24007901245636988103791507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005267497091325402527671 24007901245636988103791507)
              ·
                refine ⟨36011851868455482155687261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24007901245636988103791507 36011851868455482155687261)
                ·
                  refine ⟨13504444450670805808382723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36011851868455482155687261 13504444450670805808382723)
                  ·
                    refine ⟨20256666676006208712574085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13504444450670805808382723 20256666676006208712574085)
                    ·
                      refine ⟨3798125001751164133607641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20256666676006208712574085 3798125001751164133607641)
                      ·
                        rfl

theorem cell23_7396822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7396822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396822 prefixEnd_7396822 := by exact prefixLift 7396822
  have htrace : WordTrace (prefixWord ++ tailWord_7396822) baseStart_7396822 baseEnd_7396822 := by
    simpa [prefixWord, tailWord_7396822, baseEnd_7396822] using wordTrace_append hprefix tailTrace_7396822
  have hstable : (prefixWord ++ tailWord_7396822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396822).length < 2 ^ (prefixWord ++ tailWord_7396822).sum := by decide
  have hdescent : baseEnd_7396822 < baseStart_7396822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396825 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_7396825 : Nat := 118140960795 + 7396825 * 2 ^ 59
def prefixEnd_7396825 : Nat := 4983230072969 + 3 ^ 40 * 7396825 * 2
def baseEnd_7396825 : Nat := 3798126542193127621870127

theorem tailTrace_7396825 : CollatzResearch.WordTrace tailWord_7396825 prefixEnd_7396825 3798126542193127621870127 := by
  unfold tailWord_7396825
  simp only [CollatzResearch.WordTrace]
  refine ⟨269784371427573776980479929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179856247618382517986986619 269784371427573776980479929)
  ·
    refine ⟨202338278570680332735359947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269784371427573776980479929 202338278570680332735359947)
    ·
      refine ⟨303507417856020499103039921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202338278570680332735359947 303507417856020499103039921)
      ·
        refine ⟨227630563392015374327279941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303507417856020499103039921 227630563392015374327279941)
        ·
          refine ⟨42680730636002882686364989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227630563392015374327279941 42680730636002882686364989)
          ·
            refine ⟨16005273988501081007386871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42680730636002882686364989 16005273988501081007386871)
            ·
              refine ⟨24007910982751621511080307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005273988501081007386871 24007910982751621511080307)
              ·
                refine ⟨36011866474127432266620461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24007910982751621511080307 36011866474127432266620461)
                ·
                  refine ⟨13504449927797787099982673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36011866474127432266620461 13504449927797787099982673)
                  ·
                    refine ⟨10128337445848340324987005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13504449927797787099982673 10128337445848340324987005)
                    ·
                      refine ⟨3798126542193127621870127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10128337445848340324987005 3798126542193127621870127)
                      ·
                        rfl

theorem cell23_7396825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_7396825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396825 prefixEnd_7396825 := by exact prefixLift 7396825
  have htrace : WordTrace (prefixWord ++ tailWord_7396825) baseStart_7396825 baseEnd_7396825 := by
    simpa [prefixWord, tailWord_7396825, baseEnd_7396825] using wordTrace_append hprefix tailTrace_7396825
  have hstable : (prefixWord ++ tailWord_7396825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396825).length < 2 ^ (prefixWord ++ tailWord_7396825).sum := by decide
  have hdescent : baseEnd_7396825 < baseStart_7396825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396835 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7396835 : Nat := 118140960795 + 7396835 * 2 ^ 59
def prefixEnd_7396835 : Nat := 4983230072969 + 3 ^ 40 * 7396835 * 2
def baseEnd_7396835 : Nat := 3798131676999672582745081

theorem tailTrace_7396835 : CollatzResearch.WordTrace tailWord_7396835 prefixEnd_7396835 3798131676999672582745081 := by
  unfold tailWord_7396835
  simp only [CollatzResearch.WordTrace]
  refine ⟨269784736157537548688343959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179856490771691699125562639 269784736157537548688343959)
  ·
    refine ⟨404677104236306323032515939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269784736157537548688343959 404677104236306323032515939)
    ·
      refine ⟨607015656354459484548773909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404677104236306323032515939 607015656354459484548773909)
      ·
        refine ⟨28453858891615288338223777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 607015656354459484548773909 28453858891615288338223777)
        ·
          refine ⟨21340394168711466253667833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28453858891615288338223777 21340394168711466253667833)
          ·
            refine ⟨16005295626533599690250875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21340394168711466253667833 16005295626533599690250875)
            ·
              refine ⟨24007943439800399535376313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005295626533599690250875 24007943439800399535376313)
              ·
                refine ⟨18005957579850299651532235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24007943439800399535376313 18005957579850299651532235)
                ·
                  refine ⟨27008936369775449477298353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18005957579850299651532235 27008936369775449477298353)
                  ·
                    refine ⟨20256702277331587107973765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27008936369775449477298353 20256702277331587107973765)
                    ·
                      refine ⟨3798131676999672582745081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20256702277331587107973765 3798131676999672582745081)
                      ·
                        rfl

theorem cell23_7396835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7396835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396835 prefixEnd_7396835 := by exact prefixLift 7396835
  have htrace : WordTrace (prefixWord ++ tailWord_7396835) baseStart_7396835 baseEnd_7396835 := by
    simpa [prefixWord, tailWord_7396835, baseEnd_7396835] using wordTrace_append hprefix tailTrace_7396835
  have hstable : (prefixWord ++ tailWord_7396835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396835).length < 2 ^ (prefixWord ++ tailWord_7396835).sum := by decide
  have hdescent : baseEnd_7396835 < baseStart_7396835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396842 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_7396842 : Nat := 118140960795 + 7396842 * 2 ^ 59
def prefixEnd_7396842 : Nat := 4983230072969 + 3 ^ 40 * 7396842 * 2
def baseEnd_7396842 : Nat := 3798135271364254055357549

theorem tailTrace_7396842 : CollatzResearch.WordTrace tailWord_7396842 prefixEnd_7396842 3798135271364254055357549 := by
  unfold tailWord_7396842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67446247867128047220962195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179856660979008125922565853 67446247867128047220962195)
  ·
    refine ⟨101169371800692070831443293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67446247867128047220962195 101169371800692070831443293)
    ·
      refine ⟨37938514425259526561791235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101169371800692070831443293 37938514425259526561791235)
      ·
        refine ⟨56907771637889289842686853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37938514425259526561791235 56907771637889289842686853)
        ·
          refine ⟨10670207182104241845503785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56907771637889289842686853 10670207182104241845503785)
          ·
            refine ⟨8002655386578181384127839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10670207182104241845503785 8002655386578181384127839)
            ·
              refine ⟨12003983079867272076191759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002655386578181384127839 12003983079867272076191759)
              ·
                refine ⟨18005974619800908114287639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12003983079867272076191759 18005974619800908114287639)
                ·
                  refine ⟨27008961929701362171431459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18005974619800908114287639 27008961929701362171431459)
                  ·
                    refine ⟨40513442894552043257147189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27008961929701362171431459 40513442894552043257147189)
                    ·
                      refine ⟨3798135271364254055357549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40513442894552043257147189 3798135271364254055357549)
                      ·
                        rfl

theorem cell23_7396842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_7396842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396842 prefixEnd_7396842 := by exact prefixLift 7396842
  have htrace : WordTrace (prefixWord ++ tailWord_7396842) baseStart_7396842 baseEnd_7396842 := by
    simpa [prefixWord, tailWord_7396842, baseEnd_7396842] using wordTrace_append hprefix tailTrace_7396842
  have hstable : (prefixWord ++ tailWord_7396842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396842).length < 2 ^ (prefixWord ++ tailWord_7396842).sum := by decide
  have hdescent : baseEnd_7396842 < baseStart_7396842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396845 : List Nat := [1, 5, 1, 3, 3, 10]
def baseStart_7396845 : Nat := 118140960795 + 7396845 * 2 ^ 59
def prefixEnd_7396845 : Nat := 4983230072969 + 3 ^ 40 * 7396845 * 2
def baseEnd_7396845 : Nat := 15630192641177849973745

theorem tailTrace_7396845 : CollatzResearch.WordTrace tailWord_7396845 prefixEnd_7396845 15630192641177849973745 := by
  unfold tailWord_7396845
  simp only [CollatzResearch.WordTrace]
  refine ⟨269785100887501320396207989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179856733925000880264138659 269785100887501320396207989)
  ·
    refine ⟨25292353208203248787144499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269785100887501320396207989 25292353208203248787144499)
    ·
      refine ⟨37938529812304873180716749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25292353208203248787144499 37938529812304873180716749)
      ·
        refine ⟨14226948679614327442768781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37938529812304873180716749 14226948679614327442768781)
        ·
          refine ⟨5335105754855372791038293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14226948679614327442768781 5335105754855372791038293)
          ·
            refine ⟨15630192641177849973745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5335105754855372791038293 15630192641177849973745)
            ·
              rfl

theorem cell23_7396845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 10].length) (baseStart_7396845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396845 prefixEnd_7396845 := by exact prefixLift 7396845
  have htrace : WordTrace (prefixWord ++ tailWord_7396845) baseStart_7396845 baseEnd_7396845 := by
    simpa [prefixWord, tailWord_7396845, baseEnd_7396845] using wordTrace_append hprefix tailTrace_7396845
  have hstable : (prefixWord ++ tailWord_7396845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396845).length < 2 ^ (prefixWord ++ tailWord_7396845).sum := by decide
  have hdescent : baseEnd_7396845 < baseStart_7396845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396856 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_7396856 : Nat := 118140960795 + 7396856 * 2 ^ 59
def prefixEnd_7396856 : Nat := 4983230072969 + 3 ^ 40 * 7396856 * 2
def baseEnd_7396856 : Nat := 3798142460093417000582485

theorem tailTrace_7396856 : CollatzResearch.WordTrace tailWord_7396856 prefixEnd_7396856 3798142460093417000582485 := by
  unfold tailWord_7396856
  simp only [CollatzResearch.WordTrace]
  refine ⟨134892751045230734637429211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179857001393640979516572281 134892751045230734637429211)
  ·
    refine ⟨202339126567846101956143817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134892751045230734637429211 202339126567846101956143817)
    ·
      refine ⟨151754344925884576467107863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202339126567846101956143817 151754344925884576467107863)
      ·
        refine ⟨227631517388826864700661795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151754344925884576467107863 227631517388826864700661795)
        ·
          refine ⟨341447276083240297050992693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227631517388826864700661795 341447276083240297050992693)
          ·
            refine ⟨32010682132803777848530565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341447276083240297050992693 32010682132803777848530565)
            ·
              refine ⟨6002002899900708346599481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32010682132803777848530565 6002002899900708346599481)
              ·
                refine ⟨4501502174925531259949611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002002899900708346599481 4501502174925531259949611)
                ·
                  refine ⟨6752253262388296889924417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501502174925531259949611 6752253262388296889924417)
                  ·
                    refine ⟨5064189946791222667443313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6752253262388296889924417 5064189946791222667443313)
                    ·
                      refine ⟨3798142460093417000582485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064189946791222667443313 3798142460093417000582485)
                      ·
                        rfl

theorem cell23_7396856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_7396856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396856 prefixEnd_7396856 := by exact prefixLift 7396856
  have htrace : WordTrace (prefixWord ++ tailWord_7396856) baseStart_7396856 baseEnd_7396856 := by
    simpa [prefixWord, tailWord_7396856, baseEnd_7396856] using wordTrace_append hprefix tailTrace_7396856
  have hstable : (prefixWord ++ tailWord_7396856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396856).length < 2 ^ (prefixWord ++ tailWord_7396856).sum := by decide
  have hdescent : baseEnd_7396856 < baseStart_7396856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396872 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_7396872 : Nat := 118140960795 + 7396872 * 2 ^ 59
def prefixEnd_7396872 : Nat := 4983230072969 + 3 ^ 40 * 7396872 * 2
def baseEnd_7396872 : Nat := 3798150675783888937982411

theorem tailTrace_7396872 : CollatzResearch.WordTrace tailWord_7396872 prefixEnd_7396872 3798150675783888937982411 := by
  unfold tailWord_7396872
  simp only [CollatzResearch.WordTrace]
  refine ⟨134893042829201752003720435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179857390438935669338293913 134893042829201752003720435)
  ·
    refine ⟨202339564243802628005580653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134893042829201752003720435 202339564243802628005580653)
    ·
      refine ⟨75877336591425985502092745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202339564243802628005580653 75877336591425985502092745)
      ·
        refine ⟨56908002443569489126569559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75877336591425985502092745 56908002443569489126569559)
        ·
          refine ⟨85362003665354233689854339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56908002443569489126569559 85362003665354233689854339)
          ·
            refine ⟨128043005498031350534781509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85362003665354233689854339 128043005498031350534781509)
            ·
              refine ⟨24008063530880878225271533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128043005498031350534781509 24008063530880878225271533)
              ·
                refine ⟨9003023824080329334476825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24008063530880878225271533 9003023824080329334476825)
                ·
                  refine ⟨6752267868060247000857619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9003023824080329334476825 6752267868060247000857619)
                  ·
                    refine ⟨10128401802090370501286429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6752267868060247000857619 10128401802090370501286429)
                    ·
                      refine ⟨3798150675783888937982411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10128401802090370501286429 3798150675783888937982411)
                      ·
                        rfl

theorem cell23_7396872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_7396872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396872 prefixEnd_7396872 := by exact prefixLift 7396872
  have htrace : WordTrace (prefixWord ++ tailWord_7396872) baseStart_7396872 baseEnd_7396872 := by
    simpa [prefixWord, tailWord_7396872, baseEnd_7396872] using wordTrace_append hprefix tailTrace_7396872
  have hstable : (prefixWord ++ tailWord_7396872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396872).length < 2 ^ (prefixWord ++ tailWord_7396872).sum := by decide
  have hdescent : baseEnd_7396872 < baseStart_7396872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396899 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 1, 3, 2]
def baseStart_7396899 : Nat := 118140960795 + 7396899 * 2 ^ 59
def prefixEnd_7396899 : Nat := 4983230072969 + 3 ^ 40 * 7396899 * 2
def baseEnd_7396899 : Nat := 3798164539761560332344787

theorem tailTrace_7396899 : CollatzResearch.WordTrace tailWord_7396899 prefixEnd_7396899 3798164539761560332344787 := by
  unfold tailWord_7396899
  simp only [CollatzResearch.WordTrace]
  refine ⟨269787070429305687618673751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179858046952870458412449167 269787070429305687618673751)
  ·
    refine ⟨404680605643958531428010627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269787070429305687618673751 404680605643958531428010627)
    ·
      refine ⟨607020908465937797142015941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404680605643958531428010627 607020908465937797142015941)
      ·
        refine ⟨113816420337363336964127989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607020908465937797142015941 113816420337363336964127989)
        ·
          refine ⟨10670289406627812840386999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113816420337363336964127989 10670289406627812840386999)
          ·
            refine ⟨16005434109941719260580499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10670289406627812840386999 16005434109941719260580499)
            ·
              refine ⟨24008151164912578890870749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005434109941719260580499 24008151164912578890870749)
              ·
                refine ⟨9003056686842217084076531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24008151164912578890870749 9003056686842217084076531)
                ·
                  refine ⟨13504585030263325626114797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9003056686842217084076531 13504585030263325626114797)
                  ·
                    refine ⟨5064219386348747109793049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13504585030263325626114797 5064219386348747109793049)
                    ·
                      refine ⟨3798164539761560332344787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064219386348747109793049 3798164539761560332344787)
                      ·
                        rfl

theorem cell23_7396899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_7396899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396899 prefixEnd_7396899 := by exact prefixLift 7396899
  have htrace : WordTrace (prefixWord ++ tailWord_7396899) baseStart_7396899 baseEnd_7396899 := by
    simpa [prefixWord, tailWord_7396899, baseEnd_7396899] using wordTrace_append hprefix tailTrace_7396899
  have hstable : (prefixWord ++ tailWord_7396899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396899).length < 2 ^ (prefixWord ++ tailWord_7396899).sum := by decide
  have hdescent : baseEnd_7396899 < baseStart_7396899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396965 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_7396965 : Nat := 118140960795 + 7396965 * 2 ^ 59
def prefixEnd_7396965 : Nat := 4983230072969 + 3 ^ 40 * 7396965 * 2
def baseEnd_7396965 : Nat := 1266066143161585691373161

theorem tailTrace_7396965 : CollatzResearch.WordTrace tailWord_7396965 prefixEnd_7396965 1266066143161585691373161 := by
  unfold tailWord_7396965
  simp only [CollatzResearch.WordTrace]
  refine ⟨269789477647066580890576349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179859651764711053927050899 269789477647066580890576349)
  ·
    refine ⟨101171054117649967833966131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269789477647066580890576349 101171054117649967833966131)
    ·
      refine ⟨151756581176474951750949197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101171054117649967833966131 151756581176474951750949197)
      ·
        refine ⟨56908717941178106906605949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151756581176474951750949197 56908717941178106906605949)
        ·
          refine ⟨21340769227941790089977231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56908717941178106906605949 21340769227941790089977231)
          ·
            refine ⟨32011153841912685134965847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340769227941790089977231 32011153841912685134965847)
            ·
              refine ⟨48016730762869027702448771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32011153841912685134965847 48016730762869027702448771)
              ·
                refine ⟨72025096144303541553673157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48016730762869027702448771 72025096144303541553673157)
                ·
                  refine ⟨13504705527056914041313717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72025096144303541553673157 13504705527056914041313717)
                  ·
                    refine ⟨1266066143161585691373161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13504705527056914041313717 1266066143161585691373161)
                    ·
                      rfl

theorem cell23_7396965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_7396965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396965 prefixEnd_7396965 := by exact prefixLift 7396965
  have htrace : WordTrace (prefixWord ++ tailWord_7396965) baseStart_7396965 baseEnd_7396965 := by
    simpa [prefixWord, tailWord_7396965, baseEnd_7396965] using wordTrace_append hprefix tailTrace_7396965
  have hstable : (prefixWord ++ tailWord_7396965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396965).length < 2 ^ (prefixWord ++ tailWord_7396965).sum := by decide
  have hdescent : baseEnd_7396965 < baseStart_7396965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396985 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7396985 : Nat := 118140960795 + 7396985 * 2 ^ 59
def prefixEnd_7396985 : Nat := 4983230072969 + 3 ^ 40 * 7396985 * 2
def baseEnd_7396985 : Nat := 3798208699097846995869391

theorem tailTrace_7396985 : CollatzResearch.WordTrace tailWord_7396985 prefixEnd_7396985 3798208699097846995869391 := by
  unfold tailWord_7396985
  simp only [CollatzResearch.WordTrace]
  refine ⟨269790207106994124306304409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179860138071329416204202939 269790207106994124306304409)
  ·
    refine ⟨202342655330245593229728307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269790207106994124306304409 202342655330245593229728307)
    ·
      refine ⟨303513982995368389844592461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202342655330245593229728307 303513982995368389844592461)
      ·
        refine ⟨113817743623263146191722173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303513982995368389844592461 113817743623263146191722173)
        ·
          refine ⟨42681653858723679821895815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113817743623263146191722173 42681653858723679821895815)
          ·
            refine ⟨64022480788085519732843723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42681653858723679821895815 64022480788085519732843723)
            ·
              refine ⟨96033721182128279599265585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64022480788085519732843723 96033721182128279599265585)
              ·
                refine ⟨72025290886596209699449189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96033721182128279599265585 72025290886596209699449189)
                ·
                  refine ⟨13504742041236789318646723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72025290886596209699449189 13504742041236789318646723)
                  ·
                    refine ⟨20257113061855183977970085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13504742041236789318646723 20257113061855183977970085)
                    ·
                      refine ⟨3798208699097846995869391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20257113061855183977970085 3798208699097846995869391)
                      ·
                        rfl

theorem cell23_7396985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7396985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396985 prefixEnd_7396985 := by exact prefixLift 7396985
  have htrace : WordTrace (prefixWord ++ tailWord_7396985) baseStart_7396985 baseEnd_7396985 := by
    simpa [prefixWord, tailWord_7396985, baseEnd_7396985] using wordTrace_append hprefix tailTrace_7396985
  have hstable : (prefixWord ++ tailWord_7396985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396985).length < 2 ^ (prefixWord ++ tailWord_7396985).sum := by decide
  have hdescent : baseEnd_7396985 < baseStart_7396985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7396995 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 5, 4]
def baseStart_7396995 : Nat := 118140960795 + 7396995 * 2 ^ 59
def prefixEnd_7396995 : Nat := 4983230072969 + 3 ^ 40 * 7396995 * 2
def baseEnd_7396995 : Nat := 1266071277968130652248115

theorem tailTrace_7396995 : CollatzResearch.WordTrace tailWord_7396995 prefixEnd_7396995 1266071277968130652248115 := by
  unfold tailWord_7396995
  simp only [CollatzResearch.WordTrace]
  refine ⟨269790571836957896014168439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179860381224638597342778959 269790571836957896014168439)
  ·
    refine ⟨404685857755436844021252659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269790571836957896014168439 404685857755436844021252659)
    ·
      refine ⟨607028786633155266031878989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404685857755436844021252659 607028786633155266031878989)
      ·
        refine ⟨227635794987433224761954621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607028786633155266031878989 227635794987433224761954621)
        ·
          refine ⟨85363423120287459285732983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227635794987433224761954621 85363423120287459285732983)
          ·
            refine ⟨128045134680431188928599475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85363423120287459285732983 128045134680431188928599475)
            ·
              refine ⟨192067702020646783392899213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128045134680431188928599475 192067702020646783392899213)
              ·
                refine ⟨72025388257742543772337205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192067702020646783392899213 72025388257742543772337205)
                ·
                  refine ⟨6752380149163363478656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72025388257742543772337205 6752380149163363478656613)
                  ·
                    refine ⟨1266071277968130652248115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752380149163363478656613 1266071277968130652248115)
                    ·
                      rfl

theorem cell23_7396995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 4].length) (baseStart_7396995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7396995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7396995 prefixEnd_7396995 := by exact prefixLift 7396995
  have htrace : WordTrace (prefixWord ++ tailWord_7396995) baseStart_7396995 baseEnd_7396995 := by
    simpa [prefixWord, tailWord_7396995, baseEnd_7396995] using wordTrace_append hprefix tailTrace_7396995
  have hstable : (prefixWord ++ tailWord_7396995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7396995).length < 2 ^ (prefixWord ++ tailWord_7396995).sum := by decide
  have hdescent : baseEnd_7396995 < baseStart_7396995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7396995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397002 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7397002 : Nat := 118140960795 + 7397002 * 2 ^ 59
def prefixEnd_7397002 : Nat := 4983230072969 + 3 ^ 40 * 7397002 * 2
def baseEnd_7397002 : Nat := 3798217428268973429356813

theorem tailTrace_7397002 : CollatzResearch.WordTrace tailWord_7397002 prefixEnd_7397002 3798217428268973429356813 := by
  unfold tailWord_7397002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447706786983134052418315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179860551431955024139782173 67447706786983134052418315)
  ·
    refine ⟨101171560180474701078627473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67447706786983134052418315 101171560180474701078627473)
    ·
      refine ⟨75878670135356025808970605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101171560180474701078627473 75878670135356025808970605)
      ·
        refine ⟨28454501300758509678363977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75878670135356025808970605 28454501300758509678363977)
        ·
          refine ⟨21340875975568882258772983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28454501300758509678363977 21340875975568882258772983)
          ·
            refine ⟨32011313963353323388159475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340875975568882258772983 32011313963353323388159475)
            ·
              refine ⟨48016970945029985082239213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32011313963353323388159475 48016970945029985082239213)
              ·
                refine ⟨18006364104386244405839705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48016970945029985082239213 18006364104386244405839705)
                ·
                  refine ⟨13504773078289683304379779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18006364104386244405839705 13504773078289683304379779)
                  ·
                    refine ⟨20257159617434524956569669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13504773078289683304379779 20257159617434524956569669)
                    ·
                      refine ⟨3798217428268973429356813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20257159617434524956569669 3798217428268973429356813)
                      ·
                        rfl

theorem cell23_7397002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7397002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397002 prefixEnd_7397002 := by exact prefixLift 7397002
  have htrace : WordTrace (prefixWord ++ tailWord_7397002) baseStart_7397002 baseEnd_7397002 := by
    simpa [prefixWord, tailWord_7397002, baseEnd_7397002] using wordTrace_append hprefix tailTrace_7397002
  have hstable : (prefixWord ++ tailWord_7397002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397002).length < 2 ^ (prefixWord ++ tailWord_7397002).sum := by decide
  have hdescent : baseEnd_7397002 < baseStart_7397002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397008 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 10]
def baseStart_7397008 : Nat := 118140960795 + 7397008 * 2 ^ 59
def prefixEnd_7397008 : Nat := 4983230072969 + 3 ^ 40 * 7397008 * 2
def baseEnd_7397008 : Nat := 422024501016988933986865

theorem tailTrace_7397008 : CollatzResearch.WordTrace tailWord_7397008 prefixEnd_7397008 422024501016988933986865 := by
  unfold tailWord_7397008
  simp only [CollatzResearch.WordTrace]
  refine ⟨134895522992955399617195839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179860697323940532822927785 134895522992955399617195839)
  ·
    refine ⟨202343284489433099425793759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134895522992955399617195839 202343284489433099425793759)
    ·
      refine ⟨303514926734149649138690639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202343284489433099425793759 303514926734149649138690639)
      ·
        refine ⟨455272390101224473708035959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303514926734149649138690639 455272390101224473708035959)
        ·
          refine ⟨682908585151836710562053939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455272390101224473708035959 682908585151836710562053939)
          ·
            refine ⟨1024362877727755065843080909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682908585151836710562053939 1024362877727755065843080909)
            ·
              refine ⟨384136079147908149691155341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1024362877727755065843080909 384136079147908149691155341)
              ·
                refine ⟨144051029680465556134183253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384136079147908149691155341 144051029680465556134183253)
                ·
                  refine ⟨422024501016988933986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144051029680465556134183253 422024501016988933986865)
                  ·
                    rfl

theorem cell23_7397008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_7397008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397008 prefixEnd_7397008 := by exact prefixLift 7397008
  have htrace : WordTrace (prefixWord ++ tailWord_7397008) baseStart_7397008 baseEnd_7397008 := by
    simpa [prefixWord, tailWord_7397008, baseEnd_7397008] using wordTrace_append hprefix tailTrace_7397008
  have hstable : (prefixWord ++ tailWord_7397008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397008).length < 2 ^ (prefixWord ++ tailWord_7397008).sum := by decide
  have hdescent : baseEnd_7397008 < baseStart_7397008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397046 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7397046 : Nat := 118140960795 + 7397046 * 2 ^ 59
def prefixEnd_7397046 : Nat := 4983230072969 + 3 ^ 40 * 7397046 * 2
def baseEnd_7397046 : Nat := 1266080007139257085735537

theorem tailTrace_7397046 : CollatzResearch.WordTrace tailWord_7397046 prefixEnd_7397046 1266080007139257085735537 := by
  unfold tailWord_7397046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862026997485820732767187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179861621306515421149516661 16862026997485820732767187)
  ·
    refine ⟨25293040496228731099150781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16862026997485820732767187 25293040496228731099150781)
    ·
      refine ⟨9484890186085774162181543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25293040496228731099150781 9484890186085774162181543)
      ·
        refine ⟨14227335279128661243272315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484890186085774162181543 14227335279128661243272315)
        ·
          refine ⟨21341002918692991864908473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14227335279128661243272315 21341002918692991864908473)
          ·
            refine ⟨16005752189019743898681355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21341002918692991864908473 16005752189019743898681355)
            ·
              refine ⟨24008628283529615848022033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005752189019743898681355 24008628283529615848022033)
              ·
                refine ⟨18006471212647211886016525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24008628283529615848022033 18006471212647211886016525)
                ·
                  refine ⟨6752426704742704457256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18006471212647211886016525 6752426704742704457256197)
                  ·
                    refine ⟨1266080007139257085735537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752426704742704457256197 1266080007139257085735537)
                    ·
                      rfl

theorem cell23_7397046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7397046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397046 prefixEnd_7397046 := by exact prefixLift 7397046
  have htrace : WordTrace (prefixWord ++ tailWord_7397046) baseStart_7397046 baseEnd_7397046 := by
    simpa [prefixWord, tailWord_7397046, baseEnd_7397046] using wordTrace_append hprefix tailTrace_7397046
  have hstable : (prefixWord ++ tailWord_7397046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397046).length < 2 ^ (prefixWord ++ tailWord_7397046).sum := by decide
  have hdescent : baseEnd_7397046 < baseStart_7397046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397055 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 3, 5]
def baseStart_7397055 : Nat := 118140960795 + 7397055 * 2 ^ 59
def prefixEnd_7397055 : Nat := 4983230072969 + 3 ^ 40 * 7397055 * 2
def baseEnd_7397055 : Nat := 1266081547581220573998023

theorem tailTrace_7397055 : CollatzResearch.WordTrace tailWord_7397055 prefixEnd_7397055 1266081547581220573998023 := by
  unfold tailWord_7397055
  simp only [CollatzResearch.WordTrace]
  refine ⟨269792760216740526261352619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179861840144493684174235079 269792760216740526261352619)
  ·
    refine ⟨404689140325110789392028929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269792760216740526261352619 404689140325110789392028929)
    ·
      refine ⟨303516855243833092044021697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404689140325110789392028929 303516855243833092044021697)
      ·
        refine ⟨227637641432874819033016273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303516855243833092044021697 227637641432874819033016273)
        ·
          refine ⟨170728231074656114274762205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227637641432874819033016273 170728231074656114274762205)
          ·
            refine ⟨64023086652996042853035827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170728231074656114274762205 64023086652996042853035827)
            ·
              refine ⟨96034629979494064279553741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64023086652996042853035827 96034629979494064279553741)
              ·
                refine ⟨36012986242310274104832653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96034629979494064279553741 36012986242310274104832653)
                ·
                  refine ⟨13504869840866352789312245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36012986242310274104832653 13504869840866352789312245)
                  ·
                    refine ⟨1266081547581220573998023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13504869840866352789312245 1266081547581220573998023)
                    ·
                      rfl

theorem cell23_7397055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_7397055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397055 prefixEnd_7397055 := by exact prefixLift 7397055
  have htrace : WordTrace (prefixWord ++ tailWord_7397055) baseStart_7397055 baseEnd_7397055 := by
    simpa [prefixWord, tailWord_7397055, baseEnd_7397055] using wordTrace_append hprefix tailTrace_7397055
  have hstable : (prefixWord ++ tailWord_7397055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397055).length < 2 ^ (prefixWord ++ tailWord_7397055).sum := by decide
  have hdescent : baseEnd_7397055 < baseStart_7397055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397143 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7397143 : Nat := 118140960795 + 7397143 * 2 ^ 59
def prefixEnd_7397143 : Nat := 4983230072969 + 3 ^ 40 * 7397143 * 2
def baseEnd_7397143 : Nat := 3798289829041257377693665

theorem tailTrace_7397143 : CollatzResearch.WordTrace tailWord_7397143 prefixEnd_7397143 3798289829041257377693665 := by
  unfold tailWord_7397143
  simp only [CollatzResearch.WordTrace]
  refine ⟨269795969840421717290556083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179863979893614478193704055 269795969840421717290556083)
  ·
    refine ⟨404693954760632575935834125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269795969840421717290556083 404693954760632575935834125)
    ·
      refine ⟨151760233035237215975937797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404693954760632575935834125 151760233035237215975937797)
      ·
        refine ⟨28455043694106977995488337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151760233035237215975937797 28455043694106977995488337)
        ·
          refine ⟨21341282770580233496616253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28455043694106977995488337 21341282770580233496616253)
          ·
            refine ⟨8002981038967587561231095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21341282770580233496616253 8002981038967587561231095)
            ·
              refine ⟨12004471558451381341846643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002981038967587561231095 12004471558451381341846643)
              ·
                refine ⟨18006707337677072012769965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12004471558451381341846643 18006707337677072012769965)
                ·
                  refine ⟨6752515251628902004788737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18006707337677072012769965 6752515251628902004788737)
                  ·
                    refine ⟨5064386438721676503591553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6752515251628902004788737 5064386438721676503591553)
                    ·
                      refine ⟨3798289829041257377693665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064386438721676503591553 3798289829041257377693665)
                      ·
                        rfl

theorem cell23_7397143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7397143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397143 prefixEnd_7397143 := by exact prefixLift 7397143
  have htrace : WordTrace (prefixWord ++ tailWord_7397143) baseStart_7397143 baseEnd_7397143 := by
    simpa [prefixWord, tailWord_7397143, baseEnd_7397143] using wordTrace_append hprefix tailTrace_7397143
  have hstable : (prefixWord ++ tailWord_7397143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397143).length < 2 ^ (prefixWord ++ tailWord_7397143).sum := by decide
  have hdescent : baseEnd_7397143 < baseStart_7397143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397175 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 8]
def baseStart_7397175 : Nat := 118140960795 + 7397175 * 2 ^ 59
def prefixEnd_7397175 : Nat := 4983230072969 + 3 ^ 40 * 7397175 * 2
def baseEnd_7397175 : Nat := 1266102086807400417497839

theorem tailTrace_7397175 : CollatzResearch.WordTrace tailWord_7397175 prefixEnd_7397175 1266102086807400417497839 := by
  unfold tailWord_7397175
  simp only [CollatzResearch.WordTrace]
  refine ⟨269797136976305786755720979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179864757984203857837147319 269797136976305786755720979)
  ·
    refine ⟨404695705464458680133581469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269797136976305786755720979 404695705464458680133581469)
    ·
      refine ⟨151760889549172005050093051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404695705464458680133581469 151760889549172005050093051)
      ·
        refine ⟨227641334323758007575139577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151760889549172005050093051 227641334323758007575139577)
        ·
          refine ⟨170731000742818505681354683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227641334323758007575139577 170731000742818505681354683)
          ·
            refine ⟨256096501114227758522032025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170731000742818505681354683 256096501114227758522032025)
            ·
              refine ⟨192072375835670818891524019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256096501114227758522032025 192072375835670818891524019)
              ·
                refine ⟨288108563753506228337286029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192072375835670818891524019 288108563753506228337286029)
                ·
                  refine ⟨108040711407564835626482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288108563753506228337286029 108040711407564835626482261)
                  ·
                    refine ⟨1266102086807400417497839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108040711407564835626482261 1266102086807400417497839)
                    ·
                      rfl

theorem cell23_7397175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_7397175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397175 prefixEnd_7397175 := by exact prefixLift 7397175
  have htrace : WordTrace (prefixWord ++ tailWord_7397175) baseStart_7397175 baseEnd_7397175 := by
    simpa [prefixWord, tailWord_7397175, baseEnd_7397175] using wordTrace_append hprefix tailTrace_7397175
  have hstable : (prefixWord ++ tailWord_7397175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397175).length < 2 ^ (prefixWord ++ tailWord_7397175).sum := by decide
  have hdescent : baseEnd_7397175 < baseStart_7397175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397216 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2]
def baseStart_7397216 : Nat := 118140960795 + 7397216 * 2 ^ 59
def prefixEnd_7397216 : Nat := 4983230072969 + 3 ^ 40 * 7397216 * 2
def baseEnd_7397216 : Nat := 3798327313129035592080829

theorem tailTrace_7397216 : CollatzResearch.WordTrace tailWord_7397216 prefixEnd_7397216 3798327313129035592080829 := by
  unfold tailWord_7397216
  simp only [CollatzResearch.WordTrace]
  refine ⟨134899316184578625378981751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179865754912771500505309001 134899316184578625378981751)
  ·
    refine ⟨202348974276867938068472627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134899316184578625378981751 202348974276867938068472627)
    ·
      refine ⟨303523461415301907102708941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202348974276867938068472627 303523461415301907102708941)
      ·
        refine ⟨113821298030738215163515853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303523461415301907102708941 113821298030738215163515853)
        ·
          refine ⟨42682986761526830686318445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113821298030738215163515853 42682986761526830686318445)
          ·
            refine ⟨16006120035572561507369417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42682986761526830686318445 16006120035572561507369417)
            ·
              refine ⟨12004590026679421130527063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16006120035572561507369417 12004590026679421130527063)
              ·
                refine ⟨18006885040019131695790595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12004590026679421130527063 18006885040019131695790595)
                ·
                  refine ⟨27010327560028697543685893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18006885040019131695790595 27010327560028697543685893)
                  ·
                    refine ⟨5064436417505380789441105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27010327560028697543685893 5064436417505380789441105)
                    ·
                      refine ⟨3798327313129035592080829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064436417505380789441105 3798327313129035592080829)
                      ·
                        rfl

theorem cell23_7397216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_7397216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397216 prefixEnd_7397216 := by exact prefixLift 7397216
  have htrace : WordTrace (prefixWord ++ tailWord_7397216) baseStart_7397216 baseEnd_7397216 := by
    simpa [prefixWord, tailWord_7397216, baseEnd_7397216] using wordTrace_append hprefix tailTrace_7397216
  have hstable : (prefixWord ++ tailWord_7397216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397216).length < 2 ^ (prefixWord ++ tailWord_7397216).sum := by decide
  have hdescent : baseEnd_7397216 < baseStart_7397216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397232 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_7397232 : Nat := 118140960795 + 7397232 * 2 ^ 59
def prefixEnd_7397232 : Nat := 4983230072969 + 3 ^ 40 * 7397232 * 2
def baseEnd_7397232 : Nat := 3798335528819507529480755

theorem tailTrace_7397232 : CollatzResearch.WordTrace tailWord_7397232 prefixEnd_7397232 3798335528819507529480755 := by
  unfold tailWord_7397232
  simp only [CollatzResearch.WordTrace]
  refine ⟨134899607968549642745272975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179866143958066190327030633 134899607968549642745272975)
  ·
    refine ⟨202349411952824464117909463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134899607968549642745272975 202349411952824464117909463)
    ·
      refine ⟨303524117929236696176864195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202349411952824464117909463 303524117929236696176864195)
      ·
        refine ⟨455286176893855044265296293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303524117929236696176864195 455286176893855044265296293)
        ·
          refine ⟨85366158167597820799743055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455286176893855044265296293 85366158167597820799743055)
          ·
            refine ⟨128049237251396731199614583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85366158167597820799743055 128049237251396731199614583)
            ·
              refine ⟨192073855877095096799421875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128049237251396731199614583 192073855877095096799421875)
              ·
                refine ⟨288110783815642645199132813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192073855877095096799421875 288110783815642645199132813)
                ·
                  refine ⟨108041543930865991949674805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288110783815642645199132813 108041543930865991949674805)
                  ·
                    refine ⟨10128894743518686745282013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108041543930865991949674805 10128894743518686745282013)
                    ·
                      refine ⟨3798335528819507529480755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10128894743518686745282013 3798335528819507529480755)
                      ·
                        rfl

theorem cell23_7397232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_7397232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397232 prefixEnd_7397232 := by exact prefixLift 7397232
  have htrace : WordTrace (prefixWord ++ tailWord_7397232) baseStart_7397232 baseEnd_7397232 := by
    simpa [prefixWord, tailWord_7397232, baseEnd_7397232] using wordTrace_append hprefix tailTrace_7397232
  have hstable : (prefixWord ++ tailWord_7397232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397232).length < 2 ^ (prefixWord ++ tailWord_7397232).sum := by decide
  have hdescent : baseEnd_7397232 < baseStart_7397232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397246 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7397246 : Nat := 118140960795 + 7397246 * 2 ^ 59
def prefixEnd_7397246 : Nat := 4983230072969 + 3 ^ 40 * 7397246 * 2
def baseEnd_7397246 : Nat := 3798342717548670474705691

theorem tailTrace_7397246 : CollatzResearch.WordTrace tailWord_7397246 prefixEnd_7397246 3798342717548670474705691 := by
  unfold tailWord_7397246
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724965819881070735194449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179866484372699043921037061 33724965819881070735194449)
  ·
    refine ⟨25293724364910803051395837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33724965819881070735194449 25293724364910803051395837)
    ·
      refine ⟨9485146636841551144273439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25293724364910803051395837 9485146636841551144273439)
      ·
        refine ⟨14227719955262326716410159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485146636841551144273439 14227719955262326716410159)
        ·
          refine ⟨21341579932893490074615239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14227719955262326716410159 21341579932893490074615239)
          ·
            refine ⟨32012369899340235111922859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21341579932893490074615239 32012369899340235111922859)
            ·
              refine ⟨48018554849010352667884289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32012369899340235111922859 48018554849010352667884289)
              ·
                refine ⟨36013916136757764500913217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48018554849010352667884289 36013916136757764500913217)
                ·
                  refine ⟨27010437102568323375684913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36013916136757764500913217 27010437102568323375684913)
                  ·
                    refine ⟨20257827826926242531763685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27010437102568323375684913 20257827826926242531763685)
                    ·
                      refine ⟨3798342717548670474705691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20257827826926242531763685 3798342717548670474705691)
                      ·
                        rfl

theorem cell23_7397246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7397246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397246 prefixEnd_7397246 := by exact prefixLift 7397246
  have htrace : WordTrace (prefixWord ++ tailWord_7397246) baseStart_7397246 baseEnd_7397246 := by
    simpa [prefixWord, tailWord_7397246, baseEnd_7397246] using wordTrace_append hprefix tailTrace_7397246
  have hstable : (prefixWord ++ tailWord_7397246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397246).length < 2 ^ (prefixWord ++ tailWord_7397246).sum := by decide
  have hdescent : baseEnd_7397246 < baseStart_7397246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397266 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7397266 : Nat := 118140960795 + 7397266 * 2 ^ 59
def prefixEnd_7397266 : Nat := 4983230072969 + 3 ^ 40 * 7397266 * 2
def baseEnd_7397266 : Nat := 3798352987161760396455599

theorem tailTrace_7397266 : CollatzResearch.WordTrace tailWord_7397266 prefixEnd_7397266 3798352987161760396455599 := by
  unfold tailWord_7397266
  simp only [CollatzResearch.WordTrace]
  refine ⟨67450114004744027324320913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179866970679317406198189101 67450114004744027324320913)
  ·
    refine ⟨50587585503558020493240685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67450114004744027324320913 50587585503558020493240685)
    ·
      refine ⟨18970344563834257684965257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50587585503558020493240685 18970344563834257684965257)
      ·
        refine ⟨14227758422875693263723943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18970344563834257684965257 14227758422875693263723943)
        ·
          refine ⟨21341637634313539895585915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14227758422875693263723943 21341637634313539895585915)
          ·
            refine ⟨32012456451470309843378873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21341637634313539895585915 32012456451470309843378873)
            ·
              refine ⟨24009342338602732382534155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32012456451470309843378873 24009342338602732382534155)
              ·
                refine ⟨36014013507904098573801233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24009342338602732382534155 36014013507904098573801233)
                ·
                  refine ⟨27010510130928073930350925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36014013507904098573801233 27010510130928073930350925)
                  ·
                    refine ⟨10128941299098027723881597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27010510130928073930350925 10128941299098027723881597)
                    ·
                      refine ⟨3798352987161760396455599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10128941299098027723881597 3798352987161760396455599)
                      ·
                        rfl

theorem cell23_7397266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7397266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397266 prefixEnd_7397266 := by exact prefixLift 7397266
  have htrace : WordTrace (prefixWord ++ tailWord_7397266) baseStart_7397266 baseEnd_7397266 := by
    simpa [prefixWord, tailWord_7397266, baseEnd_7397266] using wordTrace_append hprefix tailTrace_7397266
  have hstable : (prefixWord ++ tailWord_7397266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397266).length < 2 ^ (prefixWord ++ tailWord_7397266).sum := by decide
  have hdescent : baseEnd_7397266 < baseStart_7397266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397289 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 4, 2]
def baseStart_7397289 : Nat := 118140960795 + 7397289 * 2 ^ 59
def prefixEnd_7397289 : Nat := 4983230072969 + 3 ^ 40 * 7397289 * 2
def baseEnd_7397289 : Nat := 3798364797216813806467993

theorem tailTrace_7397289 : CollatzResearch.WordTrace tailWord_7397289 prefixEnd_7397289 3798364797216813806467993 := by
  unfold tailWord_7397289
  simp only [CollatzResearch.WordTrace]
  refine ⟨269801294897892784225370921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179867529931928522816913947 269801294897892784225370921)
  ·
    refine ⟨202350971173419588169028191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269801294897892784225370921 202350971173419588169028191)
    ·
      refine ⟨303526456760129382253542287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202350971173419588169028191 303526456760129382253542287)
      ·
        refine ⟨455289685140194073380313431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303526456760129382253542287 455289685140194073380313431)
        ·
          refine ⟨682934527710291110070470147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455289685140194073380313431 682934527710291110070470147)
          ·
            refine ⟨1024401791565436665105705221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682934527710291110070470147 1024401791565436665105705221)
            ·
              refine ⟨192075335918519374707319729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1024401791565436665105705221 192075335918519374707319729)
              ·
                refine ⟨144056501938889531030489797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192075335918519374707319729 144056501938889531030489797)
                ·
                  refine ⟨27010594113541787068216837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144056501938889531030489797 27010594113541787068216837)
                  ·
                    refine ⟨5064486396289085075290657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27010594113541787068216837 5064486396289085075290657)
                    ·
                      refine ⟨3798364797216813806467993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064486396289085075290657 3798364797216813806467993)
                      ·
                        rfl

theorem cell23_7397289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4, 2].length) (baseStart_7397289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397289 prefixEnd_7397289 := by exact prefixLift 7397289
  have htrace : WordTrace (prefixWord ++ tailWord_7397289) baseStart_7397289 baseEnd_7397289 := by
    simpa [prefixWord, tailWord_7397289, baseEnd_7397289] using wordTrace_append hprefix tailTrace_7397289
  have hstable : (prefixWord ++ tailWord_7397289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397289).length < 2 ^ (prefixWord ++ tailWord_7397289).sum := by decide
  have hdescent : baseEnd_7397289 < baseStart_7397289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397312 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 8]
def baseStart_7397312 : Nat := 118140960795 + 7397312 * 2 ^ 59
def prefixEnd_7397312 : Nat := 4983230072969 + 3 ^ 40 * 7397312 * 2
def baseEnd_7397312 : Nat := 422041845252429690720043

theorem tailTrace_7397312 : CollatzResearch.WordTrace tailWord_7397312 prefixEnd_7397312 422041845252429690720043 := by
  unfold tailWord_7397312
  simp only [CollatzResearch.WordTrace]
  refine ⟨134901066888404729576729095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179868089184539639435638793 134901066888404729576729095)
  ·
    refine ⟨202351600332607094365093643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134901066888404729576729095 202351600332607094365093643)
    ·
      refine ⟨303527400498910641547640465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202351600332607094365093643 303527400498910641547640465)
      ·
        refine ⟨227645550374182981160730349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303527400498910641547640465 227645550374182981160730349)
        ·
          refine ⟨85367081390318617935273881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227645550374182981160730349 85367081390318617935273881)
          ·
            refine ⟨64025311042738963451455411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85367081390318617935273881 64025311042738963451455411)
            ·
              refine ⟨96037966564108445177183117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64025311042738963451455411 96037966564108445177183117)
              ·
                refine ⟨36014237461540666941443669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96037966564108445177183117 36014237461540666941443669)
                ·
                  refine ⟨422041845252429690720043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36014237461540666941443669 422041845252429690720043)
                  ·
                    rfl

theorem cell23_7397312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_7397312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397312 prefixEnd_7397312 := by exact prefixLift 7397312
  have htrace : WordTrace (prefixWord ++ tailWord_7397312) baseStart_7397312 baseEnd_7397312 := by
    simpa [prefixWord, tailWord_7397312, baseEnd_7397312] using wordTrace_append hprefix tailTrace_7397312
  have hstable : (prefixWord ++ tailWord_7397312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397312).length < 2 ^ (prefixWord ++ tailWord_7397312).sum := by decide
  have hdescent : baseEnd_7397312 < baseStart_7397312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397413 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_7397413 : Nat := 118140960795 + 7397413 * 2 ^ 59
def prefixEnd_7397413 : Nat := 4983230072969 + 3 ^ 40 * 7397413 * 2
def baseEnd_7397413 : Nat := 3798428468817971321317423

theorem tailTrace_7397413 : CollatzResearch.WordTrace tailWord_7397413 prefixEnd_7397413 3798428468817971321317423 := by
  unfold tailWord_7397413
  simp only [CollatzResearch.WordTrace]
  refine ⟨269805817549443553402884893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179870545032962368935256595 269805817549443553402884893)
  ·
    refine ⟨101177181581041332526081835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269805817549443553402884893 101177181581041332526081835)
    ·
      refine ⟨151765772371561998789122753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101177181581041332526081835 151765772371561998789122753)
      ·
        refine ⟨113824329278671499091842065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151765772371561998789122753 113824329278671499091842065)
        ·
          refine ⟨85368246959003624318881549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113824329278671499091842065 85368246959003624318881549)
          ·
            refine ⟨32013092609626359119580581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85368246959003624318881549 32013092609626359119580581)
            ·
              refine ⟨6002454864304942334921359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32013092609626359119580581 6002454864304942334921359)
              ·
                refine ⟨9003682296457413502382039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6002454864304942334921359 9003682296457413502382039)
                ·
                  refine ⟨13505523444686120253573059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9003682296457413502382039 13505523444686120253573059)
                  ·
                    refine ⟨20258285167029180380359589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13505523444686120253573059 20258285167029180380359589)
                    ·
                      refine ⟨3798428468817971321317423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20258285167029180380359589 3798428468817971321317423)
                      ·
                        rfl

theorem cell23_7397413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_7397413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397413 prefixEnd_7397413 := by exact prefixLift 7397413
  have htrace : WordTrace (prefixWord ++ tailWord_7397413) baseStart_7397413 baseEnd_7397413 := by
    simpa [prefixWord, tailWord_7397413, baseEnd_7397413] using wordTrace_append hprefix tailTrace_7397413
  have hstable : (prefixWord ++ tailWord_7397413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397413).length < 2 ^ (prefixWord ++ tailWord_7397413).sum := by decide
  have hdescent : baseEnd_7397413 < baseStart_7397413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397470 : List Nat := [4, 4, 1, 1, 2, 2, 9]
def baseStart_7397470 : Nat := 118140960795 + 7397470 * 2 ^ 59
def prefixEnd_7397470 : Nat := 4983230072969 + 3 ^ 40 * 7397470 * 2
def baseEnd_7397470 : Nat := 46894539965620711090181

theorem tailTrace_7397470 : CollatzResearch.WordTrace tailWord_7397470 prefixEnd_7397470 46894539965620711090181 := by
  unfold tailWord_7397470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33725987063779631517213733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179871931006824701425139909 33725987063779631517213733)
  ·
    refine ⟨6323622574458680909477575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33725987063779631517213733 6323622574458680909477575)
    ·
      refine ⟨9485433861688021364216363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323622574458680909477575 9485433861688021364216363)
      ·
        refine ⟨14228150792532032046324545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485433861688021364216363 14228150792532032046324545)
        ·
          refine ⟨10671113094399024034743409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14228150792532032046324545 10671113094399024034743409)
          ·
            refine ⟨8003334820799268026057557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10671113094399024034743409 8003334820799268026057557)
            ·
              refine ⟨46894539965620711090181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8003334820799268026057557 46894539965620711090181)
              ·
                rfl

theorem cell23_7397470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 9].length) (baseStart_7397470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397470 prefixEnd_7397470 := by exact prefixLift 7397470
  have htrace : WordTrace (prefixWord ++ tailWord_7397470) baseStart_7397470 baseEnd_7397470 := by
    simpa [prefixWord, tailWord_7397470, baseEnd_7397470] using wordTrace_append hprefix tailTrace_7397470
  have hstable : (prefixWord ++ tailWord_7397470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397470).length < 2 ^ (prefixWord ++ tailWord_7397470).sum := by decide
  have hdescent : baseEnd_7397470 < baseStart_7397470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397486 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7397486 : Nat := 118140960795 + 7397486 * 2 ^ 59
def prefixEnd_7397486 : Nat := 4983230072969 + 3 ^ 40 * 7397486 * 2
def baseEnd_7397486 : Nat := 3798465952905749535704587

theorem tailTrace_7397486 : CollatzResearch.WordTrace tailWord_7397486 prefixEnd_7397486 3798465952905749535704587 := by
  unfold tailWord_7397486
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726060009772385858786539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179872320052119391246861541 33726060009772385858786539)
  ·
    refine ⟨50589090014658578788179809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33726060009772385858786539 50589090014658578788179809)
    ·
      refine ⟨37941817510993934091134857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50589090014658578788179809 37941817510993934091134857)
      ·
        refine ⟨28456363133245450568351143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37941817510993934091134857 28456363133245450568351143)
        ·
          refine ⟨42684544699868175852526715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456363133245450568351143 42684544699868175852526715)
          ·
            refine ⟨64026817049802263778790073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42684544699868175852526715 64026817049802263778790073)
            ·
              refine ⟨48020112787351697834092555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64026817049802263778790073 48020112787351697834092555)
              ·
                refine ⟨72030169181027546751138833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48020112787351697834092555 72030169181027546751138833)
                ·
                  refine ⟨54022626885770660063354125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72030169181027546751138833 54022626885770660063354125)
                  ·
                    refine ⟨20258485082163997523757797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54022626885770660063354125 20258485082163997523757797)
                    ·
                      refine ⟨3798465952905749535704587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20258485082163997523757797 3798465952905749535704587)
                      ·
                        rfl

theorem cell23_7397486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7397486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397486 prefixEnd_7397486 := by exact prefixLift 7397486
  have htrace : WordTrace (prefixWord ++ tailWord_7397486) baseStart_7397486 baseEnd_7397486 := by
    simpa [prefixWord, tailWord_7397486, baseEnd_7397486] using wordTrace_append hprefix tailTrace_7397486
  have hstable : (prefixWord ++ tailWord_7397486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397486).length < 2 ^ (prefixWord ++ tailWord_7397486).sum := by decide
  have hdescent : baseEnd_7397486 < baseStart_7397486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397489 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7397489 : Nat := 118140960795 + 7397489 * 2 ^ 59
def prefixEnd_7397489 : Nat := 4983230072969 + 3 ^ 40 * 7397489 * 2
def baseEnd_7397489 : Nat := 3798467493347713023967073

theorem tailTrace_7397489 : CollatzResearch.WordTrace tailWord_7397489 prefixEnd_7397489 3798467493347713023967073 := by
  unfold tailWord_7397489
  simp only [CollatzResearch.WordTrace]
  refine ⟨269808589497168218382651521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179872392998112145588434347 269808589497168218382651521)
  ·
    refine ⟨202356442122876163786988641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269808589497168218382651521 202356442122876163786988641)
    ·
      refine ⟨151767331592157122840241481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202356442122876163786988641 151767331592157122840241481)
      ·
        refine ⟨113825498694117842130181111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151767331592157122840241481 113825498694117842130181111)
        ·
          refine ⟨170738248041176763195271667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113825498694117842130181111 170738248041176763195271667)
          ·
            refine ⟨256107372061765144792907501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170738248041176763195271667 256107372061765144792907501)
            ·
              refine ⟨96040264523161929297340313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256107372061765144792907501 96040264523161929297340313)
              ·
                refine ⟨72030198392371446973005235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96040264523161929297340313 72030198392371446973005235)
                ·
                  refine ⟨108045297588557170459507853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72030198392371446973005235 108045297588557170459507853)
                  ·
                    refine ⟨40516986595708938922315445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108045297588557170459507853 40516986595708938922315445)
                    ·
                      refine ⟨3798467493347713023967073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40516986595708938922315445 3798467493347713023967073)
                      ·
                        rfl

theorem cell23_7397489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7397489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397489 prefixEnd_7397489 := by exact prefixLift 7397489
  have htrace : WordTrace (prefixWord ++ tailWord_7397489) baseStart_7397489 baseEnd_7397489 := by
    simpa [prefixWord, tailWord_7397489, baseEnd_7397489] using wordTrace_append hprefix tailTrace_7397489
  have hstable : (prefixWord ++ tailWord_7397489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397489).length < 2 ^ (prefixWord ++ tailWord_7397489).sum := by decide
  have hdescent : baseEnd_7397489 < baseStart_7397489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397497 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 2, 1, 3]
def baseStart_7397497 : Nat := 118140960795 + 7397497 * 2 ^ 59
def prefixEnd_7397497 : Nat := 4983230072969 + 3 ^ 40 * 7397497 * 2
def baseEnd_7397497 : Nat := 3798471601192948992667037

theorem tailTrace_7397497 : CollatzResearch.WordTrace tailWord_7397497 prefixEnd_7397497 3798471601192948992667037 := by
  unfold tailWord_7397497
  simp only [CollatzResearch.WordTrace]
  refine ⟨269808881281139235748942745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179872587520759490499295163 269808881281139235748942745)
  ·
    refine ⟨202356660960854426811707059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269808881281139235748942745 202356660960854426811707059)
    ·
      refine ⟨303534991441281640217560589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202356660960854426811707059 303534991441281640217560589)
      ·
        refine ⟨113825621790480615081585221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303534991441281640217560589 113825621790480615081585221)
        ·
          refine ⟨21342304085715115327797229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113825621790480615081585221 21342304085715115327797229)
          ·
            refine ⟨8003364032143168247923961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21342304085715115327797229 8003364032143168247923961)
            ·
              refine ⟨6002523024107376185942971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8003364032143168247923961 6002523024107376185942971)
              ·
                refine ⟨9003784536161064278914457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6002523024107376185942971 9003784536161064278914457)
                ·
                  refine ⟨6752838402120798209185843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9003784536161064278914457 6752838402120798209185843)
                  ·
                    refine ⟨10129257603181197313778765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6752838402120798209185843 10129257603181197313778765)
                    ·
                      refine ⟨3798471601192948992667037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10129257603181197313778765 3798471601192948992667037)
                      ·
                        rfl

theorem cell23_7397497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_7397497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397497 prefixEnd_7397497 := by exact prefixLift 7397497
  have htrace : WordTrace (prefixWord ++ tailWord_7397497) baseStart_7397497 baseEnd_7397497 := by
    simpa [prefixWord, tailWord_7397497, baseEnd_7397497] using wordTrace_append hprefix tailTrace_7397497
  have hstable : (prefixWord ++ tailWord_7397497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397497).length < 2 ^ (prefixWord ++ tailWord_7397497).sum := by decide
  have hdescent : baseEnd_7397497 < baseStart_7397497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397537 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7397537 : Nat := 118140960795 + 7397537 * 2 ^ 59
def prefixEnd_7397537 : Nat := 4983230072969 + 3 ^ 40 * 7397537 * 2
def baseEnd_7397537 : Nat := 3798492140419128836166853

theorem tailTrace_7397537 : CollatzResearch.WordTrace tailWord_7397537 prefixEnd_7397537 3798492140419128836166853 := by
  unfold tailWord_7397537
  simp only [CollatzResearch.WordTrace]
  refine ⟨269810340200994322580398865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179873560133996215053599243 269810340200994322580398865)
  ·
    refine ⟨202357755150745741935299149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269810340200994322580398865 202357755150745741935299149)
    ·
      refine ⟨75884158181529653225737181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202357755150745741935299149 75884158181529653225737181)
      ·
        refine ⟨28456559318073619959651443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75884158181529653225737181 28456559318073619959651443)
        ·
          refine ⟨42684838977110429939477165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456559318073619959651443 42684838977110429939477165)
          ·
            refine ⟨16006814616416411227303937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42684838977110429939477165 16006814616416411227303937)
            ·
              refine ⟨12005110962312308420477953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16006814616416411227303937 12005110962312308420477953)
              ·
                refine ⟨9003833221734231315358465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12005110962312308420477953 9003833221734231315358465)
                ·
                  refine ⟨6752874916300673486518849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9003833221734231315358465 6752874916300673486518849)
                  ·
                    refine ⟨5064656187225505114889137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6752874916300673486518849 5064656187225505114889137)
                    ·
                      refine ⟨3798492140419128836166853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064656187225505114889137 3798492140419128836166853)
                      ·
                        rfl

theorem cell23_7397537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7397537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397537 prefixEnd_7397537 := by exact prefixLift 7397537
  have htrace : WordTrace (prefixWord ++ tailWord_7397537) baseStart_7397537 baseEnd_7397537 := by
    simpa [prefixWord, tailWord_7397537, baseEnd_7397537] using wordTrace_append hprefix tailTrace_7397537
  have hstable : (prefixWord ++ tailWord_7397537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397537).length < 2 ^ (prefixWord ++ tailWord_7397537).sum := by decide
  have hdescent : baseEnd_7397537 < baseStart_7397537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397539 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 7]
def baseStart_7397539 : Nat := 118140960795 + 7397539 * 2 ^ 59
def prefixEnd_7397539 : Nat := 4983230072969 + 3 ^ 40 * 7397539 * 2
def baseEnd_7397539 : Nat := 1266164389126812609447281

theorem tailTrace_7397539 : CollatzResearch.WordTrace tailWord_7397539 prefixEnd_7397539 1266164389126812609447281 := by
  unfold tailWord_7397539
  simp only [CollatzResearch.WordTrace]
  refine ⟨269810413146987076921971671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179873608764658051281314447 269810413146987076921971671)
  ·
    refine ⟨404715619720480615382957507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269810413146987076921971671 404715619720480615382957507)
    ·
      refine ⟨607073429580720923074436261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404715619720480615382957507 607073429580720923074436261)
      ·
        refine ⟨113826268046385173076456799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607073429580720923074436261 113826268046385173076456799)
        ·
          refine ⟨170739402069577759614685199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113826268046385173076456799 170739402069577759614685199)
          ·
            refine ⟨256109103104366639422027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170739402069577759614685199 256109103104366639422027799)
            ·
              refine ⟨384163654656549959133041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256109103104366639422027799 384163654656549959133041699)
              ·
                refine ⟨576245481984824938699562549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384163654656549959133041699 576245481984824938699562549)
                ·
                  refine ⟨54023013936077338003083989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576245481984824938699562549 54023013936077338003083989)
                  ·
                    refine ⟨1266164389126812609447281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54023013936077338003083989 1266164389126812609447281)
                    ·
                      rfl

theorem cell23_7397539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_7397539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397539 prefixEnd_7397539 := by exact prefixLift 7397539
  have htrace : WordTrace (prefixWord ++ tailWord_7397539) baseStart_7397539 baseEnd_7397539 := by
    simpa [prefixWord, tailWord_7397539, baseEnd_7397539] using wordTrace_append hprefix tailTrace_7397539
  have hstable : (prefixWord ++ tailWord_7397539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397539).length < 2 ^ (prefixWord ++ tailWord_7397539).sum := by decide
  have hdescent : baseEnd_7397539 < baseStart_7397539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397593 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 4, 2]
def baseStart_7397593 : Nat := 118140960795 + 7397593 * 2 ^ 59
def prefixEnd_7397593 : Nat := 4983230072969 + 3 ^ 40 * 7397593 * 2
def baseEnd_7397593 : Nat := 3798520895335780617066595

theorem tailTrace_7397593 : CollatzResearch.WordTrace tailWord_7397593 prefixEnd_7397593 3798520895335780617066595 := by
  unfold tailWord_7397593
  simp only [CollatzResearch.WordTrace]
  refine ⟨269812382688791444144437433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179874921792527629429624955 269812382688791444144437433)
  ·
    refine ⟨202359287016593583108328075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269812382688791444144437433 202359287016593583108328075)
    ·
      refine ⟨303538930524890374662492113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202359287016593583108328075 303538930524890374662492113)
      ·
        refine ⟨227654197893667780996869085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303538930524890374662492113 227654197893667780996869085)
        ·
          refine ⟨85370324210125417873825907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227654197893667780996869085 85370324210125417873825907)
          ·
            refine ⟨128055486315188126810738861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85370324210125417873825907 128055486315188126810738861)
            ·
              refine ⟨48020807368195547554027073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128055486315188126810738861 48020807368195547554027073)
              ·
                refine ⟨36015605526146660665520305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48020807368195547554027073 36015605526146660665520305)
                ·
                  refine ⟨27011704144609995499140229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36015605526146660665520305 27011704144609995499140229)
                  ·
                    refine ⟨5064694527114374156088793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27011704144609995499140229 5064694527114374156088793)
                    ·
                      refine ⟨3798520895335780617066595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064694527114374156088793 3798520895335780617066595)
                      ·
                        rfl

theorem cell23_7397593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_7397593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397593 prefixEnd_7397593 := by exact prefixLift 7397593
  have htrace : WordTrace (prefixWord ++ tailWord_7397593) baseStart_7397593 baseEnd_7397593 := by
    simpa [prefixWord, tailWord_7397593, baseEnd_7397593] using wordTrace_append hprefix tailTrace_7397593
  have hstable : (prefixWord ++ tailWord_7397593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397593).length < 2 ^ (prefixWord ++ tailWord_7397593).sum := by decide
  have hdescent : baseEnd_7397593 < baseStart_7397593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397616 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 6]
def baseStart_7397616 : Nat := 118140960795 + 7397616 * 2 ^ 59
def prefixEnd_7397616 : Nat := 4983230072969 + 3 ^ 40 * 7397616 * 2
def baseEnd_7397616 : Nat := 422059189487870447453221

theorem tailTrace_7397616 : CollatzResearch.WordTrace tailWord_7397616 prefixEnd_7397616 422059189487870447453221 := by
  unfold tailWord_7397616
  simp only [CollatzResearch.WordTrace]
  refine ⟨134906610783854059536262351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179875481045138746048349801 134906610783854059536262351)
  ·
    refine ⟨202359916175781089304393527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134906610783854059536262351 202359916175781089304393527)
    ·
      refine ⟨303539874263671633956590291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202359916175781089304393527 303539874263671633956590291)
      ·
        refine ⟨455309811395507450934885437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303539874263671633956590291 455309811395507450934885437)
        ·
          refine ⟨170741179273315294100582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455309811395507450934885437 170741179273315294100582039)
          ·
            refine ⟨256111768909972941150873059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170741179273315294100582039 256111768909972941150873059)
            ·
              refine ⟨384167653364959411726309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256111768909972941150873059 384167653364959411726309589)
              ·
                refine ⟨9003929375741236212335381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 384167653364959411726309589 9003929375741236212335381)
                ·
                  refine ⟨422059189487870447453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9003929375741236212335381 422059189487870447453221)
                  ·
                    rfl

theorem cell23_7397616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_7397616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397616 prefixEnd_7397616 := by exact prefixLift 7397616
  have htrace : WordTrace (prefixWord ++ tailWord_7397616) baseStart_7397616 baseEnd_7397616 := by
    simpa [prefixWord, tailWord_7397616, baseEnd_7397616] using wordTrace_append hprefix tailTrace_7397616
  have hstable : (prefixWord ++ tailWord_7397616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397616).length < 2 ^ (prefixWord ++ tailWord_7397616).sum := by decide
  have hdescent : baseEnd_7397616 < baseStart_7397616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397630 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_7397630 : Nat := 118140960795 + 7397630 * 2 ^ 59
def prefixEnd_7397630 : Nat := 4983230072969 + 3 ^ 40 * 7397630 * 2
def baseEnd_7397630 : Nat := 3798539894119996972303925

theorem tailTrace_7397630 : CollatzResearch.WordTrace tailWord_7397630 prefixEnd_7397630 3798539894119996972303925 := by
  unfold tailWord_7397630
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726716523707174932941793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179875821459771599642356229 33726716523707174932941793)
  ·
    refine ⟨25295037392780381199706345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33726716523707174932941793 25295037392780381199706345)
    ·
      refine ⟨18971278044585285899779759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25295037392780381199706345 18971278044585285899779759)
      ·
        refine ⟨28456917066877928849669639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18971278044585285899779759 28456917066877928849669639)
        ·
          refine ⟨42685375600316893274504459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456917066877928849669639 42685375600316893274504459)
          ·
            refine ⟨64028063400475339911756689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42685375600316893274504459 64028063400475339911756689)
            ·
              refine ⟨48021047550356504933817517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64028063400475339911756689 48021047550356504933817517)
              ·
                refine ⟨18007892831383689350181569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48021047550356504933817517 18007892831383689350181569)
                ·
                  refine ⟨13505919623537767012636177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18007892831383689350181569 13505919623537767012636177)
                  ·
                    refine ⟨10129439717653325259477133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13505919623537767012636177 10129439717653325259477133)
                    ·
                      refine ⟨3798539894119996972303925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10129439717653325259477133 3798539894119996972303925)
                      ·
                        rfl

theorem cell23_7397630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_7397630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397630 prefixEnd_7397630 := by exact prefixLift 7397630
  have htrace : WordTrace (prefixWord ++ tailWord_7397630) baseStart_7397630 baseEnd_7397630 := by
    simpa [prefixWord, tailWord_7397630, baseEnd_7397630] using wordTrace_append hprefix tailTrace_7397630
  have hstable : (prefixWord ++ tailWord_7397630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397630).length < 2 ^ (prefixWord ++ tailWord_7397630).sum := by decide
  have hdescent : baseEnd_7397630 < baseStart_7397630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397683 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4]
def baseStart_7397683 : Nat := 118140960795 + 7397683 * 2 ^ 59
def prefixEnd_7397683 : Nat := 4983230072969 + 3 ^ 40 * 7397683 * 2
def baseEnd_7397683 : Nat := 3798567108594685264941181

theorem tailTrace_7397683 : CollatzResearch.WordTrace tailWord_7397683 prefixEnd_7397683 3798567108594685264941181 := by
  unfold tailWord_7397683
  simp only [CollatzResearch.WordTrace]
  refine ⟨269815665258465389515213703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179877110172310259676809135 269815665258465389515213703)
  ·
    refine ⟨404723497887698084272820555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269815665258465389515213703 404723497887698084272820555)
    ·
      refine ⟨607085246831547126409230833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404723497887698084272820555 607085246831547126409230833)
      ·
        refine ⟨455313935123660344806923125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607085246831547126409230833 455313935123660344806923125)
        ·
          refine ⟨42685681417843157325649043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455313935123660344806923125 42685681417843157325649043)
          ·
            refine ⟨64028522126764735988473565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42685681417843157325649043 64028522126764735988473565)
            ·
              refine ⟨24010695797536775995677587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64028522126764735988473565 24010695797536775995677587)
              ·
                refine ⟨36016043696305163993516381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24010695797536775995677587 36016043696305163993516381)
                ·
                  refine ⟨13506016386114436497568643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36016043696305163993516381 13506016386114436497568643)
                  ·
                    refine ⟨20259024579171654746352965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13506016386114436497568643 20259024579171654746352965)
                    ·
                      refine ⟨3798567108594685264941181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259024579171654746352965 3798567108594685264941181)
                      ·
                        rfl

theorem cell23_7397683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_7397683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397683 prefixEnd_7397683 := by exact prefixLift 7397683
  have htrace : WordTrace (prefixWord ++ tailWord_7397683) baseStart_7397683 baseEnd_7397683 := by
    simpa [prefixWord, tailWord_7397683, baseEnd_7397683] using wordTrace_append hprefix tailTrace_7397683
  have hstable : (prefixWord ++ tailWord_7397683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397683).length < 2 ^ (prefixWord ++ tailWord_7397683).sum := by decide
  have hdescent : baseEnd_7397683 < baseStart_7397683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397696 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_7397696 : Nat := 118140960795 + 7397696 * 2 ^ 59
def prefixEnd_7397696 : Nat := 4983230072969 + 3 ^ 40 * 7397696 * 2
def baseEnd_7397696 : Nat := 3798573783843193714078621

theorem tailTrace_7397696 : CollatzResearch.WordTrace tailWord_7397696 prefixEnd_7397696 3798573783843193714078621 := by
  unfold tailWord_7397696
  simp only [CollatzResearch.WordTrace]
  refine ⟨134908069703709146367718471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179877426271612195156957961 134908069703709146367718471)
  ·
    refine ⟨202362104555563719551577707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134908069703709146367718471 202362104555563719551577707)
    ·
      refine ⟨303543156833345579327366561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202362104555563719551577707 303543156833345579327366561)
      ·
        refine ⟨227657367625009184495524921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303543156833345579327366561 227657367625009184495524921)
        ·
          refine ⟨170743025718756888371643691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227657367625009184495524921 170743025718756888371643691)
          ·
            refine ⟨256114538578135332557465537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170743025718756888371643691 256114538578135332557465537)
            ·
              refine ⟨192085903933601499418099153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256114538578135332557465537 192085903933601499418099153)
              ·
                refine ⟨144064427950201124563574365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192085903933601499418099153 144064427950201124563574365)
                ·
                  refine ⟨54024160481325421711340387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144064427950201124563574365 54024160481325421711340387)
                  ·
                    refine ⟨81036240721988132567010581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54024160481325421711340387 81036240721988132567010581)
                    ·
                      refine ⟨3798573783843193714078621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81036240721988132567010581 3798573783843193714078621)
                      ·
                        rfl

theorem cell23_7397696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_7397696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397696 prefixEnd_7397696 := by exact prefixLift 7397696
  have htrace : WordTrace (prefixWord ++ tailWord_7397696) baseStart_7397696 baseEnd_7397696 := by
    simpa [prefixWord, tailWord_7397696, baseEnd_7397696] using wordTrace_append hprefix tailTrace_7397696
  have hstable : (prefixWord ++ tailWord_7397696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397696).length < 2 ^ (prefixWord ++ tailWord_7397696).sum := by decide
  have hdescent : baseEnd_7397696 < baseStart_7397696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397730 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7397730 : Nat := 118140960795 + 7397730 * 2 ^ 59
def prefixEnd_7397730 : Nat := 4983230072969 + 3 ^ 40 * 7397730 * 2
def baseEnd_7397730 : Nat := 3798591242185446581053465

theorem tailTrace_7397730 : CollatzResearch.WordTrace tailWord_7397730 prefixEnd_7397730 3798591242185446581053465 := by
  unfold tailWord_7397730
  simp only [CollatzResearch.WordTrace]
  refine ⟨67454344872323779135543661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179878252992863411028116429 67454344872323779135543661)
  ·
    refine ⟨25295379327121417175828873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67454344872323779135543661 25295379327121417175828873)
    ·
      refine ⟨18971534495341062881871655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25295379327121417175828873 18971534495341062881871655)
      ·
        refine ⟨28457301743011594322807483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18971534495341062881871655 28457301743011594322807483)
        ·
          refine ⟨42685952614517391484211225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28457301743011594322807483 42685952614517391484211225)
          ·
            refine ⟨32014464460888043613158419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42685952614517391484211225 32014464460888043613158419)
            ·
              refine ⟨48021696691332065419737629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32014464460888043613158419 48021696691332065419737629)
              ·
                refine ⟨18008136259249524532401611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48021696691332065419737629 18008136259249524532401611)
                ·
                  refine ⟨27012204388874286798602417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18008136259249524532401611 27012204388874286798602417)
                  ·
                    refine ⟨20259153291655715098951813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27012204388874286798602417 20259153291655715098951813)
                    ·
                      refine ⟨3798591242185446581053465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259153291655715098951813 3798591242185446581053465)
                      ·
                        rfl

theorem cell23_7397730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7397730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397730 prefixEnd_7397730 := by exact prefixLift 7397730
  have htrace : WordTrace (prefixWord ++ tailWord_7397730) baseStart_7397730 baseEnd_7397730 := by
    simpa [prefixWord, tailWord_7397730, baseEnd_7397730] using wordTrace_append hprefix tailTrace_7397730
  have hstable : (prefixWord ++ tailWord_7397730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397730).length < 2 ^ (prefixWord ++ tailWord_7397730).sum := by decide
  have hdescent : baseEnd_7397730 < baseStart_7397730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397740 : List Nat := [2, 2, 1, 1, 6, 1, 3, 7]
def baseStart_7397740 : Nat := 118140960795 + 7397740 * 2 ^ 59
def prefixEnd_7397740 : Nat := 4983230072969 + 3 ^ 40 * 7397740 * 2
def baseEnd_7397740 : Nat := 140688754703407094145497

theorem tailTrace_7397740 : CollatzResearch.WordTrace tailWord_7397740 prefixEnd_7397740 140688754703407094145497 := by
  unfold tailWord_7397740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134908872109629444125019337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179878496146172592166692449 134908872109629444125019337)
  ·
    refine ⟨101181654082222083093764503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134908872109629444125019337 101181654082222083093764503)
    ·
      refine ⟨151772481123333124640646755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101181654082222083093764503 151772481123333124640646755)
      ·
        refine ⟨227658721684999686960970133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151772481123333124640646755 227658721684999686960970133)
        ·
          refine ⟨10671502578984360326295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227658721684999686960970133 10671502578984360326295475)
          ·
            refine ⟨16007253868476540489443213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671502578984360326295475 16007253868476540489443213)
            ·
              refine ⟨6002720200678702683541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16007253868476540489443213 6002720200678702683541205)
              ·
                refine ⟨140688754703407094145497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6002720200678702683541205 140688754703407094145497)
                ·
                  rfl

theorem cell23_7397740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 7].length) (baseStart_7397740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397740 prefixEnd_7397740 := by exact prefixLift 7397740
  have htrace : WordTrace (prefixWord ++ tailWord_7397740) baseStart_7397740 baseEnd_7397740 := by
    simpa [prefixWord, tailWord_7397740, baseEnd_7397740] using wordTrace_append hprefix tailTrace_7397740
  have hstable : (prefixWord ++ tailWord_7397740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397740).length < 2 ^ (prefixWord ++ tailWord_7397740).sum := by decide
  have hdescent : baseEnd_7397740 < baseStart_7397740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397783 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 6]
def baseStart_7397783 : Nat := 118140960795 + 7397783 * 2 ^ 59
def prefixEnd_7397783 : Nat := 4983230072969 + 3 ^ 40 * 7397783 * 2
def baseEnd_7397783 : Nat := 1266206152220044957896907

theorem tailTrace_7397783 : CollatzResearch.WordTrace tailWord_7397783 prefixEnd_7397783 1266206152220044957896907 := by
  unfold tailWord_7397783
  simp only [CollatzResearch.WordTrace]
  refine ⟨269819312558103106593854003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179879541705402071062569335 269819312558103106593854003)
  ·
    refine ⟨404728968837154659890781005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269819312558103106593854003 404728968837154659890781005)
    ·
      refine ⟨151773363313932997459042877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404728968837154659890781005 151773363313932997459042877)
      ·
        refine ⟨56915011242724874047141079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151773363313932997459042877 56915011242724874047141079)
        ·
          refine ⟨85372516864087311070711619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56915011242724874047141079 85372516864087311070711619)
          ·
            refine ⟨128058775296130966606067429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85372516864087311070711619 128058775296130966606067429)
            ·
              refine ⟨24011020368024556238637643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128058775296130966606067429 24011020368024556238637643)
              ·
                refine ⟨36016530552036834357956465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24011020368024556238637643 36016530552036834357956465)
                ·
                  refine ⟨27012397914027625768467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36016530552036834357956465 27012397914027625768467349)
                  ·
                    refine ⟨1266206152220044957896907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27012397914027625768467349 1266206152220044957896907)
                    ·
                      rfl

theorem cell23_7397783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_7397783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397783 prefixEnd_7397783 := by exact prefixLift 7397783
  have htrace : WordTrace (prefixWord ++ tailWord_7397783) baseStart_7397783 baseEnd_7397783 := by
    simpa [prefixWord, tailWord_7397783, baseEnd_7397783] using wordTrace_append hprefix tailTrace_7397783
  have hstable : (prefixWord ++ tailWord_7397783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397783).length < 2 ^ (prefixWord ++ tailWord_7397783).sum := by decide
  have hdescent : baseEnd_7397783 < baseStart_7397783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397794 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_7397794 : Nat := 118140960795 + 7397794 * 2 ^ 59
def prefixEnd_7397794 : Nat := 4983230072969 + 3 ^ 40 * 7397794 * 2
def baseEnd_7397794 : Nat := 3798624104947334330653171

theorem tailTrace_7397794 : CollatzResearch.WordTrace tailWord_7397794 prefixEnd_7397794 3798624104947334330653171 := by
  unfold tailWord_7397794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67454928440265813868126109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179879809174042170315002957 67454928440265813868126109)
  ·
    refine ⟨25295598165099680200547291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67454928440265813868126109 25295598165099680200547291)
    ·
      refine ⟨37943397247649520300820937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25295598165099680200547291 37943397247649520300820937)
      ·
        refine ⟨28457547935737140225615703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37943397247649520300820937 28457547935737140225615703)
        ·
          refine ⟨42686321903605710338423555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28457547935737140225615703 42686321903605710338423555)
          ·
            refine ⟨64029482855408565507635333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42686321903605710338423555 64029482855408565507635333)
            ·
              refine ⟨12005528035389106032681625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64029482855408565507635333 12005528035389106032681625)
              ·
                refine ⟨9004146026541829524511219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12005528035389106032681625 9004146026541829524511219)
                ·
                  refine ⟨13506219039812744286766829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004146026541829524511219 13506219039812744286766829)
                  ·
                    refine ⟨5064832139929779107537561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13506219039812744286766829 5064832139929779107537561)
                    ·
                      refine ⟨3798624104947334330653171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064832139929779107537561 3798624104947334330653171)
                      ·
                        rfl

theorem cell23_7397794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_7397794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397794 prefixEnd_7397794 := by exact prefixLift 7397794
  have htrace : WordTrace (prefixWord ++ tailWord_7397794) baseStart_7397794 baseEnd_7397794 := by
    simpa [prefixWord, tailWord_7397794, baseEnd_7397794] using wordTrace_append hprefix tailTrace_7397794
  have hstable : (prefixWord ++ tailWord_7397794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397794).length < 2 ^ (prefixWord ++ tailWord_7397794).sum := by decide
  have hdescent : baseEnd_7397794 < baseStart_7397794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397802 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7397802 : Nat := 118140960795 + 7397802 * 2 ^ 59
def prefixEnd_7397802 : Nat := 4983230072969 + 3 ^ 40 * 7397802 * 2
def baseEnd_7397802 : Nat := 3798628212792570299353135

theorem tailTrace_7397802 : CollatzResearch.WordTrace tailWord_7397802 prefixEnd_7397802 3798628212792570299353135 := by
  unfold tailWord_7397802
  simp only [CollatzResearch.WordTrace]
  refine ⟨67455001386258568209698915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179880003696689515225863773 67455001386258568209698915)
  ·
    refine ⟨101182502079387852314548373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67455001386258568209698915 101182502079387852314548373)
    ·
      refine ⟨4742929784971305577244455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101182502079387852314548373 4742929784971305577244455)
      ·
        refine ⟨7114394677456958365866683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742929784971305577244455 7114394677456958365866683)
        ·
          refine ⟨10671592016185437548800025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114394677456958365866683 10671592016185437548800025)
          ·
            refine ⟨8003694012139078161600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10671592016185437548800025 8003694012139078161600019)
            ·
              refine ⟨12005541018208617242400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003694012139078161600019 12005541018208617242400029)
              ·
                refine ⟨4502077881828231465900011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12005541018208617242400029 4502077881828231465900011)
                ·
                  refine ⟨6753116822742347198850017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502077881828231465900011 6753116822742347198850017)
                  ·
                    refine ⟨5064837617056760399137513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753116822742347198850017 5064837617056760399137513)
                    ·
                      refine ⟨3798628212792570299353135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064837617056760399137513 3798628212792570299353135)
                      ·
                        rfl

theorem cell23_7397802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7397802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397802 prefixEnd_7397802 := by exact prefixLift 7397802
  have htrace : WordTrace (prefixWord ++ tailWord_7397802) baseStart_7397802 baseEnd_7397802 := by
    simpa [prefixWord, tailWord_7397802, baseEnd_7397802] using wordTrace_append hprefix tailTrace_7397802
  have hstable : (prefixWord ++ tailWord_7397802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397802).length < 2 ^ (prefixWord ++ tailWord_7397802).sum := by decide
  have hdescent : baseEnd_7397802 < baseStart_7397802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397870 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7397870 : Nat := 118140960795 + 7397870 * 2 ^ 59
def prefixEnd_7397870 : Nat := 4983230072969 + 3 ^ 40 * 7397870 * 2
def baseEnd_7397870 : Nat := 3798663129477076033302821

theorem tailTrace_7397870 : CollatzResearch.WordTrace tailWord_7397870 prefixEnd_7397870 3798663129477076033302821 := by
  unfold tailWord_7397870
  simp only [CollatzResearch.WordTrace]
  refine ⟨33727810713598490056533883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179881657139191946968180709 33727810713598490056533883)
  ·
    refine ⟨50591716070397735084800825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33727810713598490056533883 50591716070397735084800825)
    ·
      refine ⟨37943787052798301313600619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50591716070397735084800825 37943787052798301313600619)
      ·
        refine ⟨56915680579197451970400929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37943787052798301313600619 56915680579197451970400929)
        ·
          refine ⟨42686760434398088977800697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56915680579197451970400929 42686760434398088977800697)
          ·
            refine ⟨32015070325798566733350523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42686760434398088977800697 32015070325798566733350523)
            ·
              refine ⟨48022605488697850100025785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32015070325798566733350523 48022605488697850100025785)
              ·
                refine ⟨36016954116523387575019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48022605488697850100025785 36016954116523387575019339)
                ·
                  refine ⟨54025431174785081362529009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36016954116523387575019339 54025431174785081362529009)
                  ·
                    refine ⟨40519073381088811021896757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54025431174785081362529009 40519073381088811021896757)
                    ·
                      refine ⟨3798663129477076033302821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40519073381088811021896757 3798663129477076033302821)
                      ·
                        rfl

theorem cell23_7397870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7397870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397870 prefixEnd_7397870 := by exact prefixLift 7397870
  have htrace : WordTrace (prefixWord ++ tailWord_7397870) baseStart_7397870 baseEnd_7397870 := by
    simpa [prefixWord, tailWord_7397870, baseEnd_7397870] using wordTrace_append hprefix tailTrace_7397870
  have hstable : (prefixWord ++ tailWord_7397870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397870).length < 2 ^ (prefixWord ++ tailWord_7397870).sum := by decide
  have hdescent : baseEnd_7397870 < baseStart_7397870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397880 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_7397880 : Nat := 118140960795 + 7397880 * 2 ^ 59
def prefixEnd_7397880 : Nat := 4983230072969 + 3 ^ 40 * 7397880 * 2
def baseEnd_7397880 : Nat := 3798668264283620994177775

theorem tailTrace_7397880 : CollatzResearch.WordTrace tailWord_7397880 prefixEnd_7397880 3798668264283620994177775 := by
  unfold tailWord_7397880
  simp only [CollatzResearch.WordTrace]
  refine ⟨134911425219375846080067547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179881900292501128106756729 134911425219375846080067547)
  ·
    refine ⟨202367137829063769120101321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134911425219375846080067547 202367137829063769120101321)
    ·
      refine ⟨151775353371797826840075991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202367137829063769120101321 151775353371797826840075991)
      ·
        refine ⟨227663030057696740260113987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151775353371797826840075991 227663030057696740260113987)
        ·
          refine ⟨341494545086545110390170981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227663030057696740260113987 341494545086545110390170981)
          ·
            refine ⟨64030227203727208198157059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341494545086545110390170981 64030227203727208198157059)
            ·
              refine ⟨96045340805590812297235589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64030227203727208198157059 96045340805590812297235589)
              ·
                refine ⟨18008501401048277305731673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96045340805590812297235589 18008501401048277305731673)
                ·
                  refine ⟨13506376050786207979298755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18008501401048277305731673 13506376050786207979298755)
                  ·
                    refine ⟨20259564076179311968948133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13506376050786207979298755 20259564076179311968948133)
                    ·
                      refine ⟨3798668264283620994177775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259564076179311968948133 3798668264283620994177775)
                      ·
                        rfl

theorem cell23_7397880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_7397880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397880 prefixEnd_7397880 := by exact prefixLift 7397880
  have htrace : WordTrace (prefixWord ++ tailWord_7397880) baseStart_7397880 baseEnd_7397880 := by
    simpa [prefixWord, tailWord_7397880, baseEnd_7397880] using wordTrace_append hprefix tailTrace_7397880
  have hstable : (prefixWord ++ tailWord_7397880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397880).length < 2 ^ (prefixWord ++ tailWord_7397880).sum := by decide
  have hdescent : baseEnd_7397880 < baseStart_7397880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397911 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 2, 5]
def baseStart_7397911 : Nat := 118140960795 + 7397911 * 2 ^ 59
def prefixEnd_7397911 : Nat := 4983230072969 + 3 ^ 40 * 7397911 * 2
def baseEnd_7397911 : Nat := 1266228060727970124296711

theorem tailTrace_7397911 : CollatzResearch.WordTrace tailWord_7397911 prefixEnd_7397911 1266228060727970124296711 := by
  unfold tailWord_7397911
  simp only [CollatzResearch.WordTrace]
  refine ⟨269823981101639384454513587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179882654067759589636342391 269823981101639384454513587)
  ·
    refine ⟨404735971652459076681770381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269823981101639384454513587 404735971652459076681770381)
    ·
      refine ⟨151775989369672153755663893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404735971652459076681770381 151775989369672153755663893)
      ·
        refine ⟨7114499501703382207296745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151775989369672153755663893 7114499501703382207296745)
        ·
          refine ⟨5335874626277536655472559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7114499501703382207296745 5335874626277536655472559)
          ·
            refine ⟨8003811939416304983208839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335874626277536655472559 8003811939416304983208839)
            ·
              refine ⟨12005717909124457474813259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003811939416304983208839 12005717909124457474813259)
              ·
                refine ⟨18008576863686686212219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12005717909124457474813259 18008576863686686212219889)
                ·
                  refine ⟨13506432647765014659164917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18008576863686686212219889 13506432647765014659164917)
                  ·
                    refine ⟨1266228060727970124296711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506432647765014659164917 1266228060727970124296711)
                    ·
                      rfl

theorem cell23_7397911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_7397911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397911 prefixEnd_7397911 := by exact prefixLift 7397911
  have htrace : WordTrace (prefixWord ++ tailWord_7397911) baseStart_7397911 baseEnd_7397911 := by
    simpa [prefixWord, tailWord_7397911, baseEnd_7397911] using wordTrace_append hprefix tailTrace_7397911
  have hstable : (prefixWord ++ tailWord_7397911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397911).length < 2 ^ (prefixWord ++ tailWord_7397911).sum := by decide
  have hdescent : baseEnd_7397911 < baseStart_7397911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397917 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_7397917 : Nat := 118140960795 + 7397917 * 2 ^ 59
def prefixEnd_7397917 : Nat := 4983230072969 + 3 ^ 40 * 7397917 * 2
def baseEnd_7397917 : Nat := 3798687263067837349415105

theorem tailTrace_7397917 : CollatzResearch.WordTrace tailWord_7397917 prefixEnd_7397917 3798687263067837349415105 := by
  unfold tailWord_7397917
  simp only [CollatzResearch.WordTrace]
  refine ⟨269824199939617647479232005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179882799959745098319488003 269824199939617647479232005)
  ·
    refine ⟨50592037488678308902356001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269824199939617647479232005 50592037488678308902356001)
    ·
      refine ⟨37944028116508731676767001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50592037488678308902356001 37944028116508731676767001)
      ·
        refine ⟨28458021087381548757575251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37944028116508731676767001 28458021087381548757575251)
        ·
          refine ⟨42687031631072323136362877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28458021087381548757575251 42687031631072323136362877)
          ·
            refine ⟨16007636861652121176136079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42687031631072323136362877 16007636861652121176136079)
            ·
              refine ⟨24011455292478181764204119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16007636861652121176136079 24011455292478181764204119)
              ·
                refine ⟨36017182938717272646306179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24011455292478181764204119 36017182938717272646306179)
                ·
                  refine ⟨54025774408075908969459269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36017182938717272646306179 54025774408075908969459269)
                  ·
                    refine ⟨10129832701514232931773613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54025774408075908969459269 10129832701514232931773613)
                    ·
                      refine ⟨3798687263067837349415105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10129832701514232931773613 3798687263067837349415105)
                      ·
                        rfl

theorem cell23_7397917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_7397917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397917 prefixEnd_7397917 := by exact prefixLift 7397917
  have htrace : WordTrace (prefixWord ++ tailWord_7397917) baseStart_7397917 baseEnd_7397917 := by
    simpa [prefixWord, tailWord_7397917, baseEnd_7397917] using wordTrace_append hprefix tailTrace_7397917
  have hstable : (prefixWord ++ tailWord_7397917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397917).length < 2 ^ (prefixWord ++ tailWord_7397917).sum := by decide
  have hdescent : baseEnd_7397917 < baseStart_7397917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397957 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_7397957 : Nat := 118140960795 + 7397957 * 2 ^ 59
def prefixEnd_7397957 : Nat := 4983230072969 + 3 ^ 40 * 7397957 * 2
def baseEnd_7397957 : Nat := 3798707802294017192914921

theorem tailTrace_7397957 : CollatzResearch.WordTrace tailWord_7397957 prefixEnd_7397957 3798707802294017192914921 := by
  unfold tailWord_7397957
  simp only [CollatzResearch.WordTrace]
  refine ⟨269825658859472734310688125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179883772572981822873792083 269825658859472734310688125)
  ·
    refine ⟨101184622072302275366508047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269825658859472734310688125 101184622072302275366508047)
    ·
      refine ⟨151776933108453413049762071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101184622072302275366508047 151776933108453413049762071)
      ·
        refine ⟨227665399662680119574643107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151776933108453413049762071 227665399662680119574643107)
        ·
          refine ⟨341498099494020179361964661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227665399662680119574643107 341498099494020179361964661)
          ·
            refine ⟨32015446827564391815184187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341498099494020179361964661 32015446827564391815184187)
            ·
              refine ⟨48023170241346587722776281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32015446827564391815184187 48023170241346587722776281)
              ·
                refine ⟨36017377681009940792082211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48023170241346587722776281 36017377681009940792082211)
                ·
                  refine ⟨54026066521514911188123317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36017377681009940792082211 54026066521514911188123317)
                  ·
                    refine ⟨5064943736392022923886561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54026066521514911188123317 5064943736392022923886561)
                    ·
                      refine ⟨3798707802294017192914921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5064943736392022923886561 3798707802294017192914921)
                      ·
                        rfl

theorem cell23_7397957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_7397957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397957 prefixEnd_7397957 := by exact prefixLift 7397957
  have htrace : WordTrace (prefixWord ++ tailWord_7397957) baseStart_7397957 baseEnd_7397957 := by
    simpa [prefixWord, tailWord_7397957, baseEnd_7397957] using wordTrace_append hprefix tailTrace_7397957
  have hstable : (prefixWord ++ tailWord_7397957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397957).length < 2 ^ (prefixWord ++ tailWord_7397957).sum := by decide
  have hdescent : baseEnd_7397957 < baseStart_7397957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7397987 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 4]
def baseStart_7397987 : Nat := 118140960795 + 7397987 * 2 ^ 59
def prefixEnd_7397987 : Nat := 4983230072969 + 3 ^ 40 * 7397987 * 2
def baseEnd_7397987 : Nat := 3798723206713652075539783

theorem tailTrace_7397987 : CollatzResearch.WordTrace tailWord_7397987 prefixEnd_7397987 3798723206713652075539783 := by
  unfold tailWord_7397987
  simp only [CollatzResearch.WordTrace]
  refine ⟨269826753049364049434280215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179884502032909366289520143 269826753049364049434280215)
  ·
    refine ⟨404740129574046074151420323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269826753049364049434280215 404740129574046074151420323)
    ·
      refine ⟨607110194361069111227130485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404740129574046074151420323 607110194361069111227130485)
      ·
        refine ⟨56916580721350229177543483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 607110194361069111227130485 56916580721350229177543483)
        ·
          refine ⟨85374871082025343766315225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56916580721350229177543483 85374871082025343766315225)
          ·
            refine ⟨64031153311519007824736419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85374871082025343766315225 64031153311519007824736419)
            ·
              refine ⟨96046729967278511737104629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64031153311519007824736419 96046729967278511737104629)
              ·
                refine ⟨9004380934432360475353559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96046729967278511737104629 9004380934432360475353559)
                ·
                  refine ⟨13506571401648540713030339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004380934432360475353559 13506571401648540713030339)
                  ·
                    refine ⟨20259857102472811069545509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13506571401648540713030339 20259857102472811069545509)
                    ·
                      refine ⟨3798723206713652075539783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259857102472811069545509 3798723206713652075539783)
                      ·
                        rfl

theorem cell23_7397987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_7397987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7397987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7397987 prefixEnd_7397987 := by exact prefixLift 7397987
  have htrace : WordTrace (prefixWord ++ tailWord_7397987) baseStart_7397987 baseEnd_7397987 := by
    simpa [prefixWord, tailWord_7397987, baseEnd_7397987] using wordTrace_append hprefix tailTrace_7397987
  have hstable : (prefixWord ++ tailWord_7397987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7397987).length < 2 ^ (prefixWord ++ tailWord_7397987).sum := by decide
  have hdescent : baseEnd_7397987 < baseStart_7397987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7397987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398017 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7398017 : Nat := 118140960795 + 7398017 * 2 ^ 59
def prefixEnd_7398017 : Nat := 4983230072969 + 3 ^ 40 * 7398017 * 2
def baseEnd_7398017 : Nat := 3798738611133286958164645

theorem tailTrace_7398017 : CollatzResearch.WordTrace tailWord_7398017 prefixEnd_7398017 3798738611133286958164645 := by
  unfold tailWord_7398017
  simp only [CollatzResearch.WordTrace]
  refine ⟨269827847239255364557872305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179885231492836909705248203 269827847239255364557872305)
  ·
    refine ⟨202370885429441523418404229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269827847239255364557872305 202370885429441523418404229)
    ·
      refine ⟨37944541018020285640950793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202370885429441523418404229 37944541018020285640950793)
      ·
        refine ⟨28458405763515214230713095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37944541018020285640950793 28458405763515214230713095)
        ·
          refine ⟨42687608645272821346069643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28458405763515214230713095 42687608645272821346069643)
          ·
            refine ⟨64031412967909232019104465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42687608645272821346069643 64031412967909232019104465)
            ·
              refine ⟨48023559725931924014328349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64031412967909232019104465 48023559725931924014328349)
              ·
                refine ⟨18008834897224471505373131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48023559725931924014328349 18008834897224471505373131)
                ·
                  refine ⟨27013252345836707258059697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18008834897224471505373131 27013252345836707258059697)
                  ·
                    refine ⟨20259939259377530443544773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27013252345836707258059697 20259939259377530443544773)
                    ·
                      refine ⟨3798738611133286958164645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259939259377530443544773 3798738611133286958164645)
                      ·
                        rfl

theorem cell23_7398017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7398017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398017 prefixEnd_7398017 := by exact prefixLift 7398017
  have htrace : WordTrace (prefixWord ++ tailWord_7398017) baseStart_7398017 baseEnd_7398017 := by
    simpa [prefixWord, tailWord_7398017, baseEnd_7398017] using wordTrace_append hprefix tailTrace_7398017
  have hstable : (prefixWord ++ tailWord_7398017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398017).length < 2 ^ (prefixWord ++ tailWord_7398017).sum := by decide
  have hdescent : baseEnd_7398017 < baseStart_7398017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398018 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7398018 : Nat := 118140960795 + 7398018 * 2 ^ 59
def prefixEnd_7398018 : Nat := 4983230072969 + 3 ^ 40 * 7398018 * 2
def baseEnd_7398018 : Nat := 1266246374871313818084047

theorem tailTrace_7398018 : CollatzResearch.WordTrace tailWord_7398018 prefixEnd_7398018 1266246374871313818084047 := by
  unfold tailWord_7398018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67456970928062935432164677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179885255808167827819105805 67456970928062935432164677)
  ·
    refine ⟨12648182049011800393530877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67456970928062935432164677 12648182049011800393530877)
    ·
      refine ⟨4743068268379425147574079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12648182049011800393530877 4743068268379425147574079)
      ·
        refine ⟨7114602402569137721361119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743068268379425147574079 7114602402569137721361119)
        ·
          refine ⟨10671903603853706582041679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114602402569137721361119 10671903603853706582041679)
          ·
            refine ⟨16007855405780559873062519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671903603853706582041679 16007855405780559873062519)
            ·
              refine ⟨24011783108670839809593779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16007855405780559873062519 24011783108670839809593779)
              ·
                refine ⟨36017674663006259714390669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24011783108670839809593779 36017674663006259714390669)
                ·
                  refine ⟨13506627998627347392896501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36017674663006259714390669 13506627998627347392896501)
                  ·
                    refine ⟨1266246374871313818084047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506627998627347392896501 1266246374871313818084047)
                    ·
                      rfl

theorem cell23_7398018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7398018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398018 prefixEnd_7398018 := by exact prefixLift 7398018
  have htrace : WordTrace (prefixWord ++ tailWord_7398018) baseStart_7398018 baseEnd_7398018 := by
    simpa [prefixWord, tailWord_7398018, baseEnd_7398018] using wordTrace_append hprefix tailTrace_7398018
  have hstable : (prefixWord ++ tailWord_7398018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398018).length < 2 ^ (prefixWord ++ tailWord_7398018).sum := by decide
  have hdescent : baseEnd_7398018 < baseStart_7398018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398034 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7398034 : Nat := 118140960795 + 7398034 * 2 ^ 59
def prefixEnd_7398034 : Nat := 4983230072969 + 3 ^ 40 * 7398034 * 2
def baseEnd_7398034 : Nat := 3798747340304413391652067

theorem tailTrace_7398034 : CollatzResearch.WordTrace tailWord_7398034 prefixEnd_7398034 3798747340304413391652067 := by
  unfold tailWord_7398034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67457116820048444115310289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179885644853462517640827437 67457116820048444115310289)
  ·
    refine ⟨50592837615036333086482717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67457116820048444115310289 50592837615036333086482717)
    ·
      refine ⟨18972314105638624907431019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50592837615036333086482717 18972314105638624907431019)
      ·
        refine ⟨28458471158457937361146529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18972314105638624907431019 28458471158457937361146529)
        ·
          refine ⟨21343853368843453020859897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28458471158457937361146529 21343853368843453020859897)
          ·
            refine ⟨16007890026632589765644923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21343853368843453020859897 16007890026632589765644923)
            ·
              refine ⟨24011835039948884648467385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16007890026632589765644923 24011835039948884648467385)
              ·
                refine ⟨18008876279961663486350539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24011835039948884648467385 18008876279961663486350539)
                ·
                  refine ⟨27013314419942495229525809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18008876279961663486350539 27013314419942495229525809)
                  ·
                    refine ⟨20259985814956871422144357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27013314419942495229525809 20259985814956871422144357)
                    ·
                      refine ⟨3798747340304413391652067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20259985814956871422144357 3798747340304413391652067)
                      ·
                        rfl

theorem cell23_7398034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7398034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398034 prefixEnd_7398034 := by exact prefixLift 7398034
  have htrace : WordTrace (prefixWord ++ tailWord_7398034) baseStart_7398034 baseEnd_7398034 := by
    simpa [prefixWord, tailWord_7398034, baseEnd_7398034] using wordTrace_append hprefix tailTrace_7398034
  have hstable : (prefixWord ++ tailWord_7398034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398034).length < 2 ^ (prefixWord ++ tailWord_7398034).sum := by decide
  have hdescent : baseEnd_7398034 < baseStart_7398034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398098 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7398098 : Nat := 118140960795 + 7398098 * 2 ^ 59
def prefixEnd_7398098 : Nat := 4983230072969 + 3 ^ 40 * 7398098 * 2
def baseEnd_7398098 : Nat := 3798780203066301141251773

theorem tailTrace_7398098 : CollatzResearch.WordTrace tailWord_7398098 prefixEnd_7398098 3798780203066301141251773 := by
  unfold tailWord_7398098
  simp only [CollatzResearch.WordTrace]
  refine ⟨67457700387990478847892737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179887201034641276927713965 67457700387990478847892737)
  ·
    refine ⟨50593275290992859135919553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67457700387990478847892737 50593275290992859135919553)
    ·
      refine ⟨37944956468244644351939665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50593275290992859135919553 37944956468244644351939665)
      ·
        refine ⟨28458717351183483263954749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37944956468244644351939665 28458717351183483263954749)
        ·
          refine ⟨10672019006693806223983031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28458717351183483263954749 10672019006693806223983031)
          ·
            refine ⟨16008028510040709335974547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672019006693806223983031 16008028510040709335974547)
            ·
              refine ⟨24012042765061064003961821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008028510040709335974547 24012042765061064003961821)
              ·
                refine ⟨9004516036897899001485683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24012042765061064003961821 9004516036897899001485683)
                ·
                  refine ⟨13506774055346848502228525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004516036897899001485683 13506774055346848502228525)
                  ·
                    refine ⟨5065040270755068188335697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13506774055346848502228525 5065040270755068188335697)
                    ·
                      refine ⟨3798780203066301141251773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065040270755068188335697 3798780203066301141251773)
                      ·
                        rfl

theorem cell23_7398098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7398098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398098 prefixEnd_7398098 := by exact prefixLift 7398098
  have htrace : WordTrace (prefixWord ++ tailWord_7398098) baseStart_7398098 baseEnd_7398098 := by
    simpa [prefixWord, tailWord_7398098, baseEnd_7398098] using wordTrace_append hprefix tailTrace_7398098
  have hstable : (prefixWord ++ tailWord_7398098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398098).length < 2 ^ (prefixWord ++ tailWord_7398098).sum := by decide
  have hdescent : baseEnd_7398098 < baseStart_7398098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398111 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 4, 2, 2]
def baseStart_7398111 : Nat := 118140960795 + 7398111 * 2 ^ 59
def prefixEnd_7398111 : Nat := 4983230072969 + 3 ^ 40 * 7398111 * 2
def baseEnd_7398111 : Nat := 3798786878314809590389213

theorem tailTrace_7398111 : CollatzResearch.WordTrace tailWord_7398111 prefixEnd_7398111 3798786878314809590389213 := by
  unfold tailWord_7398111
  simp only [CollatzResearch.WordTrace]
  refine ⟨269831275700914818611794187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179887517133943212407862791 269831275700914818611794187)
  ·
    refine ⟨404746913551372227917691281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269831275700914818611794187 404746913551372227917691281)
    ·
      refine ⟨303560185163529170938268461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404746913551372227917691281 303560185163529170938268461)
      ·
        refine ⟨113835069436323439101850673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303560185163529170938268461 113835069436323439101850673)
        ·
          refine ⟨85376302077242579326388005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113835069436323439101850673 85376302077242579326388005)
          ·
            refine ⟨16008056639482983623697751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85376302077242579326388005 16008056639482983623697751)
            ·
              refine ⟨24012084959224475435546627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008056639482983623697751 24012084959224475435546627)
              ·
                refine ⟨36018127438836713153319941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24012084959224475435546627 36018127438836713153319941)
                ·
                  refine ⟨6753398894781883716247489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36018127438836713153319941 6753398894781883716247489)
                  ·
                    refine ⟨5065049171086412787185617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753398894781883716247489 5065049171086412787185617)
                    ·
                      refine ⟨3798786878314809590389213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065049171086412787185617 3798786878314809590389213)
                      ·
                        rfl

theorem cell23_7398111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_7398111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398111 prefixEnd_7398111 := by exact prefixLift 7398111
  have htrace : WordTrace (prefixWord ++ tailWord_7398111) baseStart_7398111 baseEnd_7398111 := by
    simpa [prefixWord, tailWord_7398111, baseEnd_7398111] using wordTrace_append hprefix tailTrace_7398111
  have hstable : (prefixWord ++ tailWord_7398111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398111).length < 2 ^ (prefixWord ++ tailWord_7398111).sum := by decide
  have hdescent : baseEnd_7398111 < baseStart_7398111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398117 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 7]
def baseStart_7398117 : Nat := 118140960795 + 7398117 * 2 ^ 59
def prefixEnd_7398117 : Nat := 4983230072969 + 3 ^ 40 * 7398117 * 2
def baseEnd_7398117 : Nat := 422087773244304062990465

theorem tailTrace_7398117 : CollatzResearch.WordTrace tailWord_7398117 prefixEnd_7398117 422087773244304062990465 := by
  unfold tailWord_7398117
  simp only [CollatzResearch.WordTrace]
  refine ⟨269831494538893081636512605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179887663025928721091008403 269831494538893081636512605)
  ·
    refine ⟨101186810452084905613692227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269831494538893081636512605 101186810452084905613692227)
    ·
      refine ⟨151780215678127358420538341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101186810452084905613692227 151780215678127358420538341)
      ·
        refine ⟨28458790439648879703850939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151780215678127358420538341 28458790439648879703850939)
        ·
          refine ⟨42688185659473319555776409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28458790439648879703850939 42688185659473319555776409)
          ·
            refine ⟨32016139244604989666832307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42688185659473319555776409 32016139244604989666832307)
            ·
              refine ⟨48024208866907484500248461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32016139244604989666832307 48024208866907484500248461)
              ·
                refine ⟨18009078325090306687593173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48024208866907484500248461 18009078325090306687593173)
                ·
                  refine ⟨422087773244304062990465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18009078325090306687593173 422087773244304062990465)
                  ·
                    rfl

theorem cell23_7398117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_7398117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398117 prefixEnd_7398117 := by exact prefixLift 7398117
  have htrace : WordTrace (prefixWord ++ tailWord_7398117) baseStart_7398117 baseEnd_7398117 := by
    simpa [prefixWord, tailWord_7398117, baseEnd_7398117] using wordTrace_append hprefix tailTrace_7398117
  have hstable : (prefixWord ++ tailWord_7398117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398117).length < 2 ^ (prefixWord ++ tailWord_7398117).sum := by decide
  have hdescent : baseEnd_7398117 < baseStart_7398117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398128 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2]
def baseStart_7398128 : Nat := 118140960795 + 7398128 * 2 ^ 59
def prefixEnd_7398128 : Nat := 4983230072969 + 3 ^ 40 * 7398128 * 2
def baseEnd_7398128 : Nat := 3798795607485936023876635

theorem tailTrace_7398128 : CollatzResearch.WordTrace tailWord_7398128 prefixEnd_7398128 3798795607485936023876635 := by
  unfold tailWord_7398128
  simp only [CollatzResearch.WordTrace]
  refine ⟨134915947870926615257581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179887930494568820343442025 134915947870926615257581519)
  ·
    refine ⟨202373921806389922886372279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134915947870926615257581519 202373921806389922886372279)
    ·
      refine ⟨303560882709584884329558419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202373921806389922886372279 303560882709584884329558419)
      ·
        refine ⟨455341324064377326494337629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303560882709584884329558419 455341324064377326494337629)
        ·
          refine ⟨170752996524141497435376611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455341324064377326494337629 170752996524141497435376611)
          ·
            refine ⟨256129494786212246153064917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170752996524141497435376611 256129494786212246153064917)
            ·
              refine ⟨6003035034051849519212459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 256129494786212246153064917 6003035034051849519212459)
              ·
                refine ⟨9004552551077774278818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003035034051849519212459 9004552551077774278818689)
                ·
                  refine ⟨6753414413308330709114017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9004552551077774278818689 6753414413308330709114017)
                  ·
                    refine ⟨5065060809981248031835513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753414413308330709114017 5065060809981248031835513)
                    ·
                      refine ⟨3798795607485936023876635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065060809981248031835513 3798795607485936023876635)
                      ·
                        rfl

theorem cell23_7398128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2].length) (baseStart_7398128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398128 prefixEnd_7398128 := by exact prefixLift 7398128
  have htrace : WordTrace (prefixWord ++ tailWord_7398128) baseStart_7398128 baseEnd_7398128 := by
    simpa [prefixWord, tailWord_7398128, baseEnd_7398128] using wordTrace_append hprefix tailTrace_7398128
  have hstable : (prefixWord ++ tailWord_7398128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398128).length < 2 ^ (prefixWord ++ tailWord_7398128).sum := by decide
  have hdescent : baseEnd_7398128 < baseStart_7398128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398132 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7398132 : Nat := 118140960795 + 7398132 * 2 ^ 59
def prefixEnd_7398132 : Nat := 4983230072969 + 3 ^ 40 * 7398132 * 2
def baseEnd_7398132 : Nat := 3798797661408554008226617

theorem tailTrace_7398132 : CollatzResearch.WordTrace tailWord_7398132 prefixEnd_7398132 3798797661408554008226617 := by
  unfold tailWord_7398132
  simp only [CollatzResearch.WordTrace]
  refine ⟨134916020816919369599154325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179888027755892492798872433 134916020816919369599154325)
  ·
    refine ⟨6324188475793095449960359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134916020816919369599154325 6324188475793095449960359)
    ·
      refine ⟨9486282713689643174940539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6324188475793095449960359 9486282713689643174940539)
      ·
        refine ⟨14229424070534464762410809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486282713689643174940539 14229424070534464762410809)
        ·
          refine ⟨10672068052900848571808107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14229424070534464762410809 10672068052900848571808107)
          ·
            refine ⟨16008102079351272857712161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672068052900848571808107 16008102079351272857712161)
            ·
              refine ⟨12006076559513454643284121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16008102079351272857712161 12006076559513454643284121)
              ·
                refine ⟨9004557419635090982463091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12006076559513454643284121 9004557419635090982463091)
                ·
                  refine ⟨13506836129452636473694637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004557419635090982463091 13506836129452636473694637)
                  ·
                    refine ⟨5065063548544738677635489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13506836129452636473694637 5065063548544738677635489)
                    ·
                      refine ⟨3798797661408554008226617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065063548544738677635489 3798797661408554008226617)
                      ·
                        rfl

theorem cell23_7398132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7398132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398132 prefixEnd_7398132 := by exact prefixLift 7398132
  have htrace : WordTrace (prefixWord ++ tailWord_7398132) baseStart_7398132 baseEnd_7398132 := by
    simpa [prefixWord, tailWord_7398132, baseEnd_7398132] using wordTrace_append hprefix tailTrace_7398132
  have hstable : (prefixWord ++ tailWord_7398132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398132).length < 2 ^ (prefixWord ++ tailWord_7398132).sum := by decide
  have hdescent : baseEnd_7398132 < baseStart_7398132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398147 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 2, 5]
def baseStart_7398147 : Nat := 118140960795 + 7398147 * 2 ^ 59
def prefixEnd_7398147 : Nat := 4983230072969 + 3 ^ 40 * 7398147 * 2
def baseEnd_7398147 : Nat := 1266268454539457149846349

theorem tailTrace_7398147 : CollatzResearch.WordTrace tailWord_7398147 prefixEnd_7398147 1266268454539457149846349 := by
  unfold tailWord_7398147
  simp only [CollatzResearch.WordTrace]
  refine ⟨269832588728784396760104695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179888392485856264506736463 269832588728784396760104695)
  ·
    refine ⟨404748883093176595140157043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269832588728784396760104695 404748883093176595140157043)
    ·
      refine ⟨607123324639764892710235565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404748883093176595140157043 607123324639764892710235565)
      ·
        refine ⟨227671246739911834766338337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607123324639764892710235565 227671246739911834766338337)
        ·
          refine ⟨170753435054933876074753753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227671246739911834766338337 170753435054933876074753753)
          ·
            refine ⟨128065076291200407056065315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170753435054933876074753753 128065076291200407056065315)
            ·
              refine ⟨192097614436800610584097973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128065076291200407056065315 192097614436800610584097973)
              ·
                refine ⟨18009151353450057242259185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192097614436800610584097973 18009151353450057242259185)
                ·
                  refine ⟨13506863515087542931694389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18009151353450057242259185 13506863515087542931694389)
                  ·
                    refine ⟨1266268454539457149846349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506863515087542931694389 1266268454539457149846349)
                    ·
                      rfl

theorem cell23_7398147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].length) (baseStart_7398147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398147 prefixEnd_7398147 := by exact prefixLift 7398147
  have htrace : WordTrace (prefixWord ++ tailWord_7398147) baseStart_7398147 baseEnd_7398147 := by
    simpa [prefixWord, tailWord_7398147, baseEnd_7398147] using wordTrace_append hprefix tailTrace_7398147
  have hstable : (prefixWord ++ tailWord_7398147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398147).length < 2 ^ (prefixWord ++ tailWord_7398147).sum := by decide
  have hdescent : baseEnd_7398147 < baseStart_7398147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398151 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 5]
def baseStart_7398151 : Nat := 118140960795 + 7398151 * 2 ^ 59
def prefixEnd_7398151 : Nat := 4983230072969 + 3 ^ 40 * 7398151 * 2
def baseEnd_7398151 : Nat := 422089713060109937098781

theorem tailTrace_7398151 : CollatzResearch.WordTrace tailWord_7398151 prefixEnd_7398151 422089713060109937098781 := by
  unfold tailWord_7398151
  simp only [CollatzResearch.WordTrace]
  refine ⟨269832734620769905443250307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179888489747179936962166871 269832734620769905443250307)
  ·
    refine ⟨404749101931154858164875461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269832734620769905443250307 404749101931154858164875461)
    ·
      refine ⟨75890456612091535905914149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404749101931154858164875461 75890456612091535905914149)
      ·
        refine ⟨14229460614767162982358903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75890456612091535905914149 14229460614767162982358903)
        ·
          refine ⟨21344190922150744473538355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229460614767162982358903 21344190922150744473538355)
          ·
            refine ⟨32016286383226116710307533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21344190922150744473538355 32016286383226116710307533)
            ·
              refine ⟨12006107393709793766365325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32016286383226116710307533 12006107393709793766365325)
              ·
                refine ⟨4502290272641172662386997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12006107393709793766365325 4502290272641172662386997)
                ·
                  refine ⟨422089713060109937098781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502290272641172662386997 422089713060109937098781)
                  ·
                    rfl

theorem cell23_7398151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 5].length) (baseStart_7398151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398151 prefixEnd_7398151 := by exact prefixLift 7398151
  have htrace : WordTrace (prefixWord ++ tailWord_7398151) baseStart_7398151 baseEnd_7398151 := by
    simpa [prefixWord, tailWord_7398151, baseEnd_7398151] using wordTrace_append hprefix tailTrace_7398151
  have hstable : (prefixWord ++ tailWord_7398151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398151).length < 2 ^ (prefixWord ++ tailWord_7398151).sum := by decide
  have hdescent : baseEnd_7398151 < baseStart_7398151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398184 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7398184 : Nat := 118140960795 + 7398184 * 2 ^ 59
def prefixEnd_7398184 : Nat := 4983230072969 + 3 ^ 40 * 7398184 * 2
def baseEnd_7398184 : Nat := 3798824362402587804776377

theorem tailTrace_7398184 : CollatzResearch.WordTrace tailWord_7398184 prefixEnd_7398184 3798824362402587804776377 := by
  unfold tailWord_7398184
  simp only [CollatzResearch.WordTrace]
  refine ⟨134916969114825176039600803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179889292153100234719467737 134916969114825176039600803)
  ·
    refine ⟨202375453672237764059401205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134916969114825176039600803 202375453672237764059401205)
    ·
      refine ⟨18972698781772290380568863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202375453672237764059401205 18972698781772290380568863)
      ·
        refine ⟨28459048172658435570853295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18972698781772290380568863 28459048172658435570853295)
        ·
          refine ⟨42688572258987653356279943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28459048172658435570853295 42688572258987653356279943)
          ·
            refine ⟨64032858388481480034419915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42688572258987653356279943 64032858388481480034419915)
            ·
              refine ⟨96049287582722220051629873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64032858388481480034419915 96049287582722220051629873)
              ·
                refine ⟨72036965687041665038722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96049287582722220051629873 72036965687041665038722405)
                ·
                  refine ⟨13506931066320312194760451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72036965687041665038722405 13506931066320312194760451)
                  ·
                    refine ⟨20260396599480468292140677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13506931066320312194760451 20260396599480468292140677)
                    ·
                      refine ⟨3798824362402587804776377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20260396599480468292140677 3798824362402587804776377)
                      ·
                        rfl

theorem cell23_7398184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7398184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398184 prefixEnd_7398184 := by exact prefixLift 7398184
  have htrace : WordTrace (prefixWord ++ tailWord_7398184) baseStart_7398184 baseEnd_7398184 := by
    simpa [prefixWord, tailWord_7398184, baseEnd_7398184] using wordTrace_append hprefix tailTrace_7398184
  have hstable : (prefixWord ++ tailWord_7398184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398184).length < 2 ^ (prefixWord ++ tailWord_7398184).sum := by decide
  have hdescent : baseEnd_7398184 < baseStart_7398184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398194 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_7398194 : Nat := 118140960795 + 7398194 * 2 ^ 59
def prefixEnd_7398194 : Nat := 4983230072969 + 3 ^ 40 * 7398194 * 2
def baseEnd_7398194 : Nat := 1266276499069710921883777

theorem tailTrace_7398194 : CollatzResearch.WordTrace tailWord_7398194 prefixEnd_7398194 1266276499069710921883777 := by
  unfold tailWord_7398194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458575739903530946766409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179889535306409415858043757 67458575739903530946766409)
  ·
    refine ⟨50593931804927648210074807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67458575739903530946766409 50593931804927648210074807)
    ·
      refine ⟨75890897707391472315112211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50593931804927648210074807 75890897707391472315112211)
      ·
        refine ⟨113836346561087208472668317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75890897707391472315112211 113836346561087208472668317)
        ·
          refine ⟨42688629960407703177250619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113836346561087208472668317 42688629960407703177250619)
          ·
            refine ⟨64032944940611554765875929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42688629960407703177250619 64032944940611554765875929)
            ·
              refine ⟨48024708705458666074406947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64032944940611554765875929 48024708705458666074406947)
              ·
                refine ⟨72037063058187999111610421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48024708705458666074406947 72037063058187999111610421)
                ·
                  refine ⟨6753474661705124916713477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72037063058187999111610421 6753474661705124916713477)
                  ·
                    refine ⟨1266276499069710921883777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6753474661705124916713477 1266276499069710921883777)
                    ·
                      rfl

theorem cell23_7398194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_7398194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398194 prefixEnd_7398194 := by exact prefixLift 7398194
  have htrace : WordTrace (prefixWord ++ tailWord_7398194) baseStart_7398194 baseEnd_7398194 := by
    simpa [prefixWord, tailWord_7398194, baseEnd_7398194] using wordTrace_append hprefix tailTrace_7398194
  have hstable : (prefixWord ++ tailWord_7398194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398194).length < 2 ^ (prefixWord ++ tailWord_7398194).sum := by decide
  have hdescent : baseEnd_7398194 < baseStart_7398194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398198 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7398198 : Nat := 118140960795 + 7398198 * 2 ^ 59
def prefixEnd_7398198 : Nat := 4983230072969 + 3 ^ 40 * 7398198 * 2
def baseEnd_7398198 : Nat := 1266277183710583583333771

theorem tailTrace_7398198 : CollatzResearch.WordTrace tailWord_7398198 prefixEnd_7398198 1266277183710583583333771 := by
  unfold tailWord_7398198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864653053224977029388203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179889632567733088313474165 16864653053224977029388203)
  ·
    refine ⟨25296979579837465544082305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16864653053224977029388203 25296979579837465544082305)
    ·
      refine ⟨18972734684878099158061729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25296979579837465544082305 18972734684878099158061729)
      ·
        refine ⟨14229551013658574368546297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18972734684878099158061729 14229551013658574368546297)
        ·
          refine ⟨10672163260243930776409723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14229551013658574368546297 10672163260243930776409723)
          ·
            refine ⟨16008244890365896164614585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672163260243930776409723 16008244890365896164614585)
            ·
              refine ⟨12006183667774422123460939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16008244890365896164614585 12006183667774422123460939)
              ·
                refine ⟨18009275501661633185191409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006183667774422123460939 18009275501661633185191409)
                ·
                  refine ⟨13506956626246224888893557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18009275501661633185191409 13506956626246224888893557)
                  ·
                    refine ⟨1266277183710583583333771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506956626246224888893557 1266277183710583583333771)
                    ·
                      rfl

theorem cell23_7398198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7398198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398198 prefixEnd_7398198 := by exact prefixLift 7398198
  have htrace : WordTrace (prefixWord ++ tailWord_7398198) baseStart_7398198 baseEnd_7398198 := by
    simpa [prefixWord, tailWord_7398198, baseEnd_7398198] using wordTrace_append hprefix tailTrace_7398198
  have hstable : (prefixWord ++ tailWord_7398198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398198).length < 2 ^ (prefixWord ++ tailWord_7398198).sum := by decide
  have hdescent : baseEnd_7398198 < baseStart_7398198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398211 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 1, 4]
def baseStart_7398211 : Nat := 118140960795 + 7398211 * 2 ^ 59
def prefixEnd_7398211 : Nat := 4983230072969 + 3 ^ 40 * 7398211 * 2
def baseEnd_7398211 : Nat := 1266279408793419733046251

theorem tailTrace_7398211 : CollatzResearch.WordTrace tailWord_7398211 prefixEnd_7398211 1266279408793419733046251 := by
  unfold tailWord_7398211
  simp only [CollatzResearch.WordTrace]
  refine ⟨269834923000552535690434487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179889948667035023793622991 269834923000552535690434487)
  ·
    refine ⟨404752384500828803535651731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269834923000552535690434487 404752384500828803535651731)
    ·
      refine ⟨607128576751243205303477597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404752384500828803535651731 607128576751243205303477597)
      ·
        refine ⟨227673216281716201988804099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607128576751243205303477597 227673216281716201988804099)
        ·
          refine ⟨341509824422574302983206149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227673216281716201988804099 341509824422574302983206149)
          ·
            refine ⟨64033092079232681809351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341509824422574302983206149 64033092079232681809351153)
            ·
              refine ⟨48024819059424511357013365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64033092079232681809351153 48024819059424511357013365)
              ·
                refine ⟨4502326786821047939720003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48024819059424511357013365 4502326786821047939720003)
                ·
                  refine ⟨6753490180231571909580005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502326786821047939720003 6753490180231571909580005)
                  ·
                    refine ⟨1266279408793419733046251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6753490180231571909580005 1266279408793419733046251)
                    ·
                      rfl

theorem cell23_7398211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 4].length) (baseStart_7398211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398211 prefixEnd_7398211 := by exact prefixLift 7398211
  have htrace : WordTrace (prefixWord ++ tailWord_7398211) baseStart_7398211 baseEnd_7398211 := by
    simpa [prefixWord, tailWord_7398211, baseEnd_7398211] using wordTrace_append hprefix tailTrace_7398211
  have hstable : (prefixWord ++ tailWord_7398211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398211).length < 2 ^ (prefixWord ++ tailWord_7398211).sum := by decide
  have hdescent : baseEnd_7398211 < baseStart_7398211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398271 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 1, 5]
def baseStart_7398271 : Nat := 118140960795 + 7398271 * 2 ^ 59
def prefixEnd_7398271 : Nat := 4983230072969 + 3 ^ 40 * 7398271 * 2
def baseEnd_7398271 : Nat := 1266289678406509654796159

theorem tailTrace_7398271 : CollatzResearch.WordTrace tailWord_7398271 prefixEnd_7398271 1266289678406509654796159 := by
  unfold tailWord_7398271
  simp only [CollatzResearch.WordTrace]
  refine ⟨269837111380335165937618667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179891407586890110625079111 269837111380335165937618667)
  ·
    refine ⟨404755667070502748906428001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269837111380335165937618667 404755667070502748906428001)
    ·
      refine ⟨303566750302877061679821001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404755667070502748906428001 303566750302877061679821001)
      ·
        refine ⟨227675062727157796259865751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303566750302877061679821001 227675062727157796259865751)
        ·
          refine ⟨341512594090736694389798627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227675062727157796259865751 341512594090736694389798627)
          ·
            refine ⟨512268891136105041584697941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341512594090736694389798627 512268891136105041584697941)
            ·
              refine ⟨6003151068001230956070679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 512268891136105041584697941 6003151068001230956070679)
              ·
                refine ⟨9004726602001846434106019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003151068001230956070679 9004726602001846434106019)
                ·
                  refine ⟨13507089903002769651159029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004726602001846434106019 13507089903002769651159029)
                  ·
                    refine ⟨1266289678406509654796159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13507089903002769651159029 1266289678406509654796159)
                    ·
                      rfl

theorem cell23_7398271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_7398271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398271 prefixEnd_7398271 := by exact prefixLift 7398271
  have htrace : WordTrace (prefixWord ++ tailWord_7398271) baseStart_7398271 baseEnd_7398271 := by
    simpa [prefixWord, tailWord_7398271, baseEnd_7398271] using wordTrace_append hprefix tailTrace_7398271
  have hstable : (prefixWord ++ tailWord_7398271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398271).length < 2 ^ (prefixWord ++ tailWord_7398271).sum := by decide
  have hdescent : baseEnd_7398271 < baseStart_7398271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398297 : List Nat := [1, 2, 1, 2, 1, 3, 1, 12]
def baseStart_7398297 : Nat := 118140960795 + 7398297 * 2 ^ 59
def prefixEnd_7398297 : Nat := 4983230072969 + 3 ^ 40 * 7398297 * 2
def baseEnd_7398297 : Nat := 140699347619131328246791

theorem tailTrace_7398297 : CollatzResearch.WordTrace tailWord_7398297 prefixEnd_7398297 140699347619131328246791 := by
  unfold tailWord_7398297
  simp only [CollatzResearch.WordTrace]
  refine ⟨269838059678240972378065145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179892039785493981585376763 269838059678240972378065145)
  ·
    refine ⟨202378544758680729283548859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269838059678240972378065145 202378544758680729283548859)
    ·
      refine ⟨303567817138021093925323289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202378544758680729283548859 303567817138021093925323289)
      ·
        refine ⟨227675862853515820443992467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303567817138021093925323289 227675862853515820443992467)
        ·
          refine ⟨341513794280273730665988701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227675862853515820443992467 341513794280273730665988701)
          ·
            refine ⟨128067672855102648999745763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341513794280273730665988701 128067672855102648999745763)
            ·
              refine ⟨192101509282653973499618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128067672855102648999745763 192101509282653973499618645)
              ·
                refine ⟨140699347619131328246791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 192101509282653973499618645 140699347619131328246791)
                ·
                  rfl

theorem cell23_7398297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 12].length) (baseStart_7398297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398297 prefixEnd_7398297 := by exact prefixLift 7398297
  have htrace : WordTrace (prefixWord ++ tailWord_7398297) baseStart_7398297 baseEnd_7398297 := by
    simpa [prefixWord, tailWord_7398297, baseEnd_7398297] using wordTrace_append hprefix tailTrace_7398297
  have hstable : (prefixWord ++ tailWord_7398297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398297).length < 2 ^ (prefixWord ++ tailWord_7398297).sum := by decide
  have hdescent : baseEnd_7398297 < baseStart_7398297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
